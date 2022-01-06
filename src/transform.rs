use amzn_smt_ir::{logic::*, Command as IRCommand, ParseError, Script, Term as IRTerm};
use amzn_smt_ir::{ICoreOp, ISort, ISymbol, IVar, QualIdentifier};
use amzn_smt_ir::visit::{ControlFlow, Visit, Visitor, SuperVisit};

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
) -> Result<impl Iterator<Item = Command>, ParseError<ALL>> {
    Ok(Script::<Term>::parse(smtlib)?.into_iter())
}

#[derive(Default, Clone, Debug)]
pub struct ADTFlattener {
    datatypes: HashMap<ISymbol, HashMap<ISymbol, ISort>>,
}

impl Visitor<ALL> for ADTFlattener {
    type BreakTy = ();

    fn visit_var(&mut self, var: &IVar<QualIdentifier>) -> ControlFlow<Self::BreakTy> {
        println!("{}", var.sym());
        ControlFlow::CONTINUE
    }

    fn visit_core_op(&mut self, op: &ICoreOp<ALL>) -> ControlFlow<Self::BreakTy> {
        op.super_visit_with(self)
    }
}

impl ADTFlattener {
    pub fn load<'a>(&mut self, commands: impl Iterator<Item = &'a Command>) {
        commands.for_each(|c| {
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

    pub fn flatten(&mut self, commands: impl Iterator<Item = Command>) {
        commands.for_each(|c| {
            if let Command::Assert { term } = c {
                term.visit_with(self);
            }
        });
    }
}

