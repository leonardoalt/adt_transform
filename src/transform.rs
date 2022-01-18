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
    // scope -> variable name -> [name]
    // this is separated by scopes because a variable can have the same
    // name but different sorts in different quantifiers.
    var_names_cache: Vec<HashMap<ISymbol, Vec<ISymbol>>>,
    // sort -> [sort]
    sort_cache: HashMap<ISort, Vec<ISort>>,
}

// Main functions.
impl ADTFlattener {
    pub fn flatten(&mut self, commands: Script<Term>) -> Script<Term> {
        let mut commands = commands;

        let mut current = commands.to_string();
        loop {
            self.reset();
            commands = self.iterate(commands);
            let new = commands.to_string();

            if current == new {
                break;
            }

            current = new;
        }

        self.remove_declare_datatypes(commands)
    }

    fn reset(&mut self) {
        self.datatypes.clear();
        self.accessors.clear();
        self.var_sorts.clear();

        self.var_names_cache.clear();
        self.var_names_cache.push(HashMap::default());
        self.sort_cache.clear();
    }

    fn iterate(&mut self, commands: Script<Term>) -> Script<Term> {
        self.collect_datatypes(&commands);

        self.collect_global_var_sorts(&commands);

        let commands = self.flatten_all_declare_const(commands);
        let commands = self.flatten_all_declare_fun(commands);

        // Flatten each assertion separately.
        commands.map(|cmd| match cmd {
            IRCommand::Assert { term } => self.flatten_assertion(term),
            _ => cmd,
        })
    }
}

// View helper functions.
impl ADTFlattener {
    fn var_sort_from_symbol(&self, symbol: &ISymbol) -> ISort {
        self.var_sorts.get(symbol).unwrap().clone()
    }

    fn var_sort(&self, var: &IVar<QualIdentifier>) -> ISort {
        self.var_sort_from_symbol(&var_symbol(var))
    }

    fn has_datatype_sort(&self, var: &IVar<QualIdentifier>) -> bool {
        self.datatypes.contains_key(self.var_sort(var).sym())
    }
}

// Mutating helper functions.
impl ADTFlattener {
    fn declare_var(&mut self, (symbol, sort): (ISymbol, ISort)) {
        self.var_sorts.insert(symbol, sort);
    }
}

// Cache scope wrapping stuff.
impl ADTFlattener {
    fn current_var_name_cache_contains(&self, symbol: &ISymbol) -> bool {
        self.var_names_cache.last().unwrap().contains_key(symbol)
    }

    fn current_var_name_cache_get(&self, symbol: &ISymbol) -> Option<&Vec<ISymbol>> {
        self.var_names_cache.last().unwrap().get(symbol)
    }

    fn current_var_name_cache_insert(&mut self, symbol: ISymbol, symbols: Vec<ISymbol>) {
        let mut current = self.var_names_cache.pop().unwrap();
        current.insert(symbol, symbols);
        self.var_names_cache.push(current);
    }
}

// Collected info.
impl ADTFlattener {
    // Collects
    // - all the declared datatypes
    // - each datatype's members
    // - creates template sort names for each pair (dt, member)
    // TODO maybe we should remove the template name from here
    // to keep it separated.
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

    fn collect_global_var_sorts(&mut self, commands: &Script<Term>) {
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
}

// Basic flattening helpers.
impl ADTFlattener {
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

    fn flatten_var_decl(&mut self, (symbol, sort): (ISymbol, ISort)) -> Vec<(ISymbol, ISort)> {
        let names = self.flatten_var_name(symbol);
        let sorts = self.flatten_sort(sort);
        assert_eq!(names.len(), sorts.len());
        let var_decls: Vec<_> = names.into_iter().zip(sorts.into_iter()).collect();
        var_decls
            .iter()
            .for_each(|decl| self.declare_var(decl.clone()));
        var_decls
    }

    fn flatten_var_name(&mut self, symbol: ISymbol) -> Vec<ISymbol> {
        if !self.current_var_name_cache_contains(&symbol) {
            self.current_var_name_cache_insert(
                symbol.clone(),
                self.flatten_var_name_nocache(symbol.clone()),
            );
        }
        self.current_var_name_cache_get(&symbol).unwrap().to_vec()
    }

    fn flatten_var_name_nocache(&self, symbol: ISymbol) -> Vec<ISymbol> {
        let sort = self.var_sort_from_symbol(&symbol);
        match self.datatypes.get(sort.sym()) {
            Some(members) => members
                .iter()
                .map(|(_, template_name, _)| ISymbol::from(format!("{}_{}", symbol, template_name)))
                .collect(),
            None => vec![symbol],
        }
    }

    fn flatten_accessor(&self, accessor: &ISymbol, var: &IVar<QualIdentifier>) -> ISymbol {
        let sort = self.var_sort(var);
        let dt = self.datatypes.get(sort.sym()).unwrap();
        let dt_info = dt.iter().find(|(name, _, _)| name == accessor);
        assert!(dt_info.is_some());
        ISymbol::from(format!("{}_{}", var_symbol(var), dt_info.unwrap().1))
    }
}

// Top level commands flatteners.
impl ADTFlattener {
    fn flatten_assertion(&mut self, assertion: Term) -> IRCommand<Term> {
        self.var_names_cache
            .push(self.var_names_cache.last().unwrap().clone());
        self.collect_quant_vars(&assertion);

        let assertion = self.flatten_quant_vars(assertion);

        let t = assertion.fold_with(self);
        self.var_names_cache.pop();

        IRCommand::Assert { term: t.unwrap() }
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
}

// Used to flatten and replace:
// - Accessor function applications over tuple variables.
// - Function applications over tuple variables.
// - Function applications over tuple constructors.
// - Equalities over tuple constructors.
impl Folder<ALL> for ADTFlattener {
    type Output = Term;
    type Error = ();

    fn fold_uninterpreted_func(&mut self, uf: IUF<ALL>) -> Result<Self::Output, Self::Error> {
        let args = &uf.as_ref().args;
        let func = &uf.as_ref().func;
        if self.accessors.contains(func) {
            // Replace accessor over tuple variable.
            assert!(args.len() == 1);
            if let Term::Variable(var) = &args[0] {
                return Ok(Term::from(IVar::from(QualIdentifier::from(
                    self.flatten_accessor(func, var),
                ))));
            }
        } else {
            // Replace function application over tuple variables.
            let mut uf = uf.super_fold_with(self)?;
            uf.args = (Vec::from(uf.args).into_iter())
                .map(|arg| match arg {
                    Term::Variable(ref var) => match self.has_datatype_sort(var) {
                        true => self
                            .current_var_name_cache_get(&var_symbol(var))
                            .unwrap()
                            .clone()
                            .into_iter()
                            .map(|arg| arg.into())
                            .collect(),
                        false => vec![arg],
                    },
                    Term::UF(ref arg_uf) => match self.datatypes.get(&arg_uf.func) {
                        Some(_) => Vec::from(arg_uf.args.clone()),
                        None => vec![arg],
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
