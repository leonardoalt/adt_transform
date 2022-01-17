use crate::helpers::*;

use amzn_smt_ir::fold::{Fold, Folder, SuperFold};
use amzn_smt_ir::Quantifier::Exists;
use amzn_smt_ir::Quantifier::Forall;
use amzn_smt_ir::Term::Quantifier;
use amzn_smt_ir::{logic::*, Command as IRCommand, Script, Term as IRTerm};
use amzn_smt_ir::{IConst, ICoreOp, ILet, IMatch, IQuantifier, IUF};
use amzn_smt_ir::{IOp, ISort, ISymbol, IVar, QualIdentifier};

use smt2parser::concrete::Command::{DeclareConst, DeclareFun};

use num_traits::identities::Zero;
use std::collections::HashMap;
use std::collections::HashSet;

type Term = IRTerm<ALL>;
type Command = IRCommand<Term>;

#[derive(Default, Clone, Debug)]
pub struct ADTFlattener {
    // datatype_sort -> (member name, template name, member sort)
    datatypes: HashMap<ISymbol, Vec<(ISymbol, ISymbol, ISort)>>,
    accessors: HashSet<ISymbol>,

    // variable name -> sort
    var_sorts: HashMap<ISymbol, ISort>,

    // Caches:
    //
    // variable (name, sort) -> [(name, sort)]
    var_new_names_cache: HashMap<(ISymbol, ISort), Vec<(ISymbol, ISort)>>,
    // sort -> [sort]
    sort_cache: HashMap<ISort, Vec<ISort>>,
}

impl ADTFlattener {
    pub fn flatten(&mut self, commands: Script<Term>) -> Script<Term> {
        self.collect_datatypes(&commands);

        self.collect_var_sorts(&commands);

        let commands = self.remove_declare_datatypes(commands);
        let commands = self.flatten_all_declare_const(commands);
        let commands = self.flatten_all_declare_fun(commands);

        // Flatten each assertion separately.
        commands.map(|cmd| match cmd {
            IRCommand::Assert { term } => self.flatten_assertion(term),
            _ => cmd,
        })
    }

    fn var_sort(&self, var: &IVar<QualIdentifier>) -> ISort {
        self.var_sorts.get(&var_symbol(var)).unwrap().clone()
    }

    fn has_datatype_sort(&self, var: &IVar<QualIdentifier>) -> bool {
        self.datatypes.contains_key(self.var_sort(var).sym())
    }

    fn flatten_assertion(&mut self, assertion: Term) -> IRCommand<Term> {
        self.collect_quant_vars(&assertion);

        let assertion = self.flatten_quant_vars(assertion);

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
                                    ISymbol::from(format!("{}_{}", symbol, member)),
                                    sort,
                                )
                            })
                            .collect();
                        self.datatypes.insert(symbol.clone(), members);
                        self.datatypes
                            .get(symbol)
                            .unwrap()
                            .iter()
                            .for_each(|(member, _, _)| {
                                self.accessors.insert(member.clone());
                            });
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

    fn collect_quant_vars(&mut self, assertion: &Term) {
        if let Quantifier(ref quantifier) = assertion {
            match quantifier.as_ref() {
                Forall(vars, ..) | Exists(vars, ..) => vars.iter().for_each(|(symbol, sort)| {
                    self.var_sorts.insert(symbol.clone(), sort.clone());
                }),
            }
        };
    }

    fn flatten_sort(&mut self, sort: ISort) -> Vec<ISort> {
        if !self.sort_cache.contains_key(&sort) {
            self.sort_cache
                .insert(sort.clone(), self.flatten_sort_nocache(sort.clone()));
        }
        self.sort_cache.get(&sort).unwrap().to_vec()
    }

    fn flatten_sort_nocache(&self, sort: ISort) -> Vec<ISort> {
        match self.datatypes.get(sort.sym()) {
            Some(members) => members
                .clone()
                .into_iter()
                .map(|(_, _, sort)| sort)
                .collect(),
            None => vec![sort],
        }
    }

    fn flatten_var_decl(&mut self, var: (ISymbol, ISort)) -> Vec<(ISymbol, ISort)> {
        if !self.var_new_names_cache.contains_key(&var) {
            self.var_new_names_cache
                .insert(var.clone(), self.flatten_var_decl_nocache(var.clone()));
        }
        let new_vars = self.var_new_names_cache.get(&var).unwrap();
        new_vars.iter().for_each(|(symbol, sort)| {
            self.var_sorts.insert(symbol.clone(), sort.clone());
        });
        new_vars.to_vec()
    }

    fn flatten_var_decl_nocache(&self, (name, sort): (ISymbol, ISort)) -> Vec<(ISymbol, ISort)> {
        match self.datatypes.get(sort.sym()) {
            Some(members) => members
                .iter()
                .map(|(_, template_name, sort)| {
                    (
                        ISymbol::from(format!("{}_{}", name, template_name)),
                        sort.clone(),
                    )
                })
                .collect::<Vec<(ISymbol, ISort)>>(),
            None => vec![(name, sort)],
        }
    }

    fn flatten_quant_vars(&mut self, assertion: Term) -> Term {
        // TODO can we clone less stuff here?
        match assertion {
            Quantifier(ref quantifier) => match quantifier.as_ref() {
                Forall(vars, term) => Term::from(Forall(
                    vars.clone()
                        .into_iter()
                        .map(|var| self.flatten_var_decl(var))
                        .collect::<Vec<Vec<(ISymbol, ISort)>>>()
                        .into_iter()
                        .flatten()
                        .collect(),
                    term.clone(),
                )),
                Exists(vars, term) => Term::from(Exists(
                    vars.clone()
                        .into_iter()
                        .map(|var| self.flatten_var_decl(var))
                        .collect::<Vec<Vec<(ISymbol, ISort)>>>()
                        .into_iter()
                        .flatten()
                        .collect(),
                    term.clone(),
                )),
            },
            _ => assertion,
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

    fn remove_declare_datatypes(&self, commands: Script<Term>) -> Script<Term> {
        commands
            .into_iter()
            .filter(|cmd| !matches!(cmd, IRCommand::DeclareDatatypes { .. }))
            .collect()
    }

    fn flatten_declare_fun(&mut self, declare_fun: IRCommand<Term>) -> IRCommand<Term> {
        match declare_fun {
            DeclareFun {
                symbol,
                parameters,
                sort,
            } => DeclareFun {
                symbol,
                parameters: parameters
                    .into_iter()
                    .map(|sort| self.flatten_sort(sort))
                    .flatten()
                    .collect(),
                sort,
            },
            _ => declare_fun,
        }
    }

    fn flatten_all_declare_fun(&mut self, commands: Script<Term>) -> Script<Term> {
        Script::from_commands(
            commands
                .into_iter()
                .map(|cmd| self.flatten_declare_fun(cmd))
                .collect(),
        )
    }

    fn flatten_accessor(&self, accessor: &ISymbol, var: &IVar<QualIdentifier>) -> ISymbol {
        let sort = self.var_sort(var);
        let dt = self.datatypes.get(sort.sym()).unwrap();
        let dt_info = dt.iter().find(|(name, _, _)| name == accessor);
        assert!(dt_info.is_some());
        ISymbol::from(format!("{}_{}", var_symbol(var), dt_info.unwrap().1))
    }
}

impl Folder<ALL> for ADTFlattener {
    type Output = Term;
    type Error = ();

    fn fold_uninterpreted_func(&mut self, uf: IUF<ALL>) -> Result<Self::Output, Self::Error> {
        let args = &uf.as_ref().args;
        let func = &uf.as_ref().func;
        if self.accessors.contains(func) {
            assert!(args.len() == 1);
            if let Term::Variable(var) = &args[0] {
                return Ok(Term::from(IVar::from(QualIdentifier::from(
                    self.flatten_accessor(func, var),
                ))));
            }
        } else {
            let mut uf = uf.super_fold_with(self)?;
            uf.args = (Vec::from(uf.args).into_iter())
                .map(|arg| match arg {
                    Term::Variable(ref var) => match self.has_datatype_sort(var) {
                        true => self
                            .var_new_names_cache
                            .get(&(var_symbol(var), self.var_sort(var)))
                            .unwrap()
                            .clone()
                            .into_iter()
                            .map(|(symbol, _)| symbol.into())
                            .collect(),
                        false => vec![arg],
                    },
                    _ => vec![arg],
                })
                .flatten()
                .collect();
            return Ok(uf.into());
        }

        // Currently accessors over terms that are not variables end up here.
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
