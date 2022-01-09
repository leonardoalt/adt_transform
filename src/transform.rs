use amzn_smt_ir::{logic::*, Command as IRCommand, ParseError, Script, Term as IRTerm};
use amzn_smt_ir::{ICoreOp, ISort, ISymbol, IVar, QualIdentifier, Identifier};
use amzn_smt_ir::visit::{ControlFlow, Visit, Visitor, SuperVisit};
use amzn_smt_ir::Term::Quantifier;
use amzn_smt_ir::Quantifier::Forall;

use num_traits::identities::Zero;
use std::collections::HashMap;

type Term = IRTerm<ALL>;
type Command = IRCommand<Term>;

///
/// Build an iterator from an input buffer. The input is parsed as a list of commands
/// in SMT-LIB syntax.
///
pub fn parse(
    smtlib: impl std::io::BufRead,
) -> Result<Script<Term>, ParseError<ALL>> {
    Ok(Script::<Term>::parse(smtlib)?)
}

#[derive(Default, Clone, Debug)]
pub struct ADTFlattener {
    // datatype_sort -> member_sort -> sort
    datatypes: HashMap<ISymbol, HashMap<ISymbol, ISort>>,
    // variable name -> sort
    var_sorts: HashMap<ISymbol, ISort>,
    local_var_sorts: HashMap<ISymbol, ISort>,
}

impl Visitor<ALL> for ADTFlattener {
    type BreakTy = ();

    fn visit_var(&mut self, var: &IVar<QualIdentifier>) -> ControlFlow<Self::BreakTy> {
        if let QualIdentifier::Simple { identifier } = var.as_ref() {
            let id_symbol = match identifier.as_ref() {
                Identifier::Simple { symbol } => symbol,
                Identifier::Indexed { symbol, .. } => symbol
            };
            match self.var_sorts.get(id_symbol) {
                Some(sort) => {
                    println!("Variable {} has sort {}", identifier, sort.sym())
                }
                None => {
                    println!("Variable {} has no sort", identifier)
                }
            }
        }
        ControlFlow::CONTINUE
    }

    fn visit_core_op(&mut self, op: &ICoreOp<ALL>) -> ControlFlow<Self::BreakTy> {
        op.super_visit_with(self)
    }
}

impl ADTFlattener {
    pub fn collect_datatypes(&mut self, commands: &Script<Term>) {
        commands.as_ref().iter().for_each(|c| {
            if let Command::DeclareDatatypes { datatypes } = c {
                datatypes
                    .iter()
                    .filter(|(_, numeral, datatype_dec)| {
                        numeral.is_zero() && datatype_dec.constructors.len() == 1
                    })
                    .for_each(|(symbol, _, datatype_dec)| {
                        let members = datatype_dec.constructors[0]
                            .selectors
                            .clone()
                            .into_iter()
                            .collect::<HashMap<ISymbol, ISort>>();
                        self.datatypes.insert(symbol.clone(), members);
                    })
            }
        });

        println!("{:?}", self.datatypes);
    }

    pub fn collect_var_sorts(&mut self, commands: &Script<Term>) {
        commands.as_ref().iter().for_each(|c| {
            if let Command::DeclareConst { symbol, sort } = c {
                self.var_sorts.insert(symbol.clone(), sort.clone());
            }
        });

        println!("{:?}", self.var_sorts);
    }

    pub fn collect_quant_var_sorts(&mut self, commands: &Script<Term>) {
        commands.as_ref().iter().for_each(|c| {
            if let Command::Assert { term } = c {
                println!("{:?}", term);
                if let Quantifier(quantifier) = term.clone() {
                    if let Forall(vars, ..) = quantifier.as_ref() {
                        vars.into_iter().for_each(|(symbol, sort)| {
                            self.local_var_sorts.insert(symbol.clone(), sort.clone());
                        })
                    }
                }
                let flow = term.visit_with(self);
                assert!(flow == ControlFlow::CONTINUE);
            }
        });
    }

    pub fn flatten(&mut self, commands: Script<Term>) -> Script<Term> {
        self.collect_datatypes(&commands);
        self.collect_var_sorts(&commands);
        self.collect_quant_var_sorts(&commands);
        commands
    }
}
