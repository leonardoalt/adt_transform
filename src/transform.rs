use crate::helpers::*;

use amzn_smt_ir::fold::{Fold, Folder, SuperFold};
use amzn_smt_ir::Quantifier::Exists;
use amzn_smt_ir::Quantifier::Forall;
use amzn_smt_ir::Term::Quantifier;
use amzn_smt_ir::{logic::*, Command as IRCommand, Script, Term as IRTerm};
use amzn_smt_ir::{IConst, ICoreOp, ILet, IMatch, IQuantifier, IUF};
use amzn_smt_ir::{IOp, ISort, ISymbol, IVar, QualIdentifier};

use smt2parser::concrete::Command::DeclareConst;

use num_traits::identities::Zero;
use std::collections::HashMap;

type Term = IRTerm<ALL>;
type Command = IRCommand<Term>;

#[derive(Default, Clone, Debug)]
pub struct ADTFlattener {
    // datatype_sort -> member_sort -> (template name, sort)
    datatypes: HashMap<ISymbol, HashMap<ISymbol, (ISymbol, ISort)>>,
    // variable name -> sort
    var_sorts: HashMap<ISymbol, ISort>,
}

impl ADTFlattener {
    pub fn flatten(&mut self, commands: Script<Term>) -> Script<Term> {
        self.collect_datatypes(&commands);

        self.collect_var_sorts(&commands);

        let commands = self.remove_declare_datatypes(commands);
        let commands = self.flatten_all_declare_const(commands);

        // Flatten each assertion separately.
        commands.map(|cmd| match cmd {
            IRCommand::Assert { term } => self.flatten_assertion(term),
            _ => cmd,
        })
    }

    fn var_sort(&self, var: &IVar<QualIdentifier>) -> ISort {
        self.var_sorts.get(&var_symbol(var)).unwrap().clone()
    }

    fn flatten_assertion(&mut self, assertion: Term) -> IRCommand<Term> {
        //let quant_vars = self.collect_quant_var_sorts(&assertion);

        /*
        if let Quantifier(ref quantifier) = assertion {
            if let Forall(vars, term) = quantifier.as_ref() {
                let assertion = Forall(vars.to_vec(), term);
            } else if let Exists(vars, term) = quantifier.as_ref() {
                let assertion = Exists(vars.to_vec(), term);
            }
        }
        */

        /*
        let assertion = match assertion {
            Quantifier(quantifier) => Quantifier(IQuantifier(match quantifier.as_ref() {
                Forall(vars, term) => Forall(self.flatten_var_decls(vars.to_vec()), term),
                Exists(vars, term) => Exists(self.flatten_var_decls(vars.to_vec()), term)
            })),
            _ => assertion
        };
        */

        let t = assertion.fold_with(self);
        IRCommand::Assert { term: t.unwrap() }
    }

    fn collect_datatypes(&mut self, commands: &Script<Term>) {
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
                            .map(|(member, sort)| {
                                (
                                    member.clone(),
                                    (ISymbol::from(format!("{}_{}", symbol, member)), sort),
                                )
                            })
                            .collect::<HashMap<ISymbol, (ISymbol, ISort)>>();
                        self.datatypes.insert(symbol.clone(), members);
                    })
            }
        });
    }

    fn collect_var_sorts(&mut self, commands: &Script<Term>) {
        commands.as_ref().iter().for_each(|c| {
            if let Command::DeclareConst { symbol, sort } = c {
                self.var_sorts.insert(symbol.clone(), sort.clone());
            }
        });
    }

    fn flatten_var_decl(&mut self, (name, sort): (ISymbol, ISort)) -> Vec<(ISymbol, ISort)> {
        match self.datatypes.get(sort.sym()) {
            Some(members) => members
                .iter()
                .map(|(_, (template_name, sort))| {
                    (
                        ISymbol::from(format!("{}_{}", name, template_name)),
                        sort.clone(),
                    )
                })
                .collect::<Vec<(ISymbol, ISort)>>(),
            None => vec![(name, sort)],
        }
    }

    fn flatten_declare_const(&mut self, declare_const: IRCommand<Term>) -> Vec<IRCommand<Term>> {
        match declare_const {
            DeclareConst { symbol, sort } => self
                .flatten_var_decl((symbol, sort))
                .into_iter()
                .map(|(symbol, sort)| IRCommand::DeclareConst { symbol, sort })
                .collect(),
            _ => vec![declare_const],
        }
    }

    fn flatten_all_declare_const(&mut self, commands: Script<Term>) -> Script<Term> {
        Script::from_commands(
            commands
                .into_iter()
                .map(|cmd| self.flatten_declare_const(cmd))
                .collect::<Vec<Vec<IRCommand<Term>>>>()
                .into_iter()
                .flatten()
                .collect::<Vec<IRCommand<Term>>>(),
        )
    }

    fn remove_declare_datatypes(&mut self, commands: Script<Term>) -> Script<Term> {
        commands
            .into_iter()
            .filter(|cmd| !matches!(cmd, IRCommand::DeclareDatatypes { .. }))
            .collect()
    }
}

impl Folder<ALL> for ADTFlattener {
    type Output = Term;
    type Error = ();

    fn fold_uninterpreted_func(&mut self, uf: IUF<ALL>) -> Result<Self::Output, Self::Error> {
        let args = &uf.as_ref().args;
        if args.len() == 1 {
            if let Term::Variable(var) = &args[0] {
                let sort = self.var_sort(var);
                if let Some(dt) = self.datatypes.get(sort.sym()) {
                    let dt_info = dt.get(&uf.as_ref().func);
                    assert!(dt_info.is_some());
                    let new_name =
                        ISymbol::from(format!("{}_{}", dt_info.unwrap().0, var_symbol(var)));
                    return Ok(Term::from(IVar::from(QualIdentifier::from(new_name))));
                }
            }
        }

        uf.super_fold_with(self).map(Into::into)
    }

    fn fold_const(&mut self, constant: IConst) -> Result<Self::Output, Self::Error> {
        Ok(constant.into())
    }

    fn fold_var(&mut self, var: IVar<QualIdentifier>) -> Result<Self::Output, Self::Error> {
        Ok(var.into())
    }

    fn fold_core_op(&mut self, op: ICoreOp<ALL>) -> Result<Self::Output, Self::Error> {
        op.super_fold_with(self).map(Into::into)
    }

    fn fold_theory_op(&mut self, op: IOp<ALL>) -> Result<Self::Output, Self::Error> {
        op.super_fold_with(self).map(Into::into)
    }

    fn fold_let(&mut self, l: ILet<ALL>) -> Result<Self::Output, Self::Error> {
        l.super_fold_with(self).map(Into::into)
    }

    fn fold_match(&mut self, m: IMatch<ALL>) -> Result<Self::Output, Self::Error> {
        m.super_fold_with(self).map(Into::into)
    }

    fn fold_quantifier(
        &mut self,
        quantifier: IQuantifier<ALL>,
    ) -> Result<Self::Output, Self::Error> {
        quantifier.super_fold_with(self).map(Into::into)
    }
}
