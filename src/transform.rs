// SPDX-License-Identifier: GPL-3.0-only

use crate::helpers::*;
use crate::parser;

use amzn_smt_ir::fold::{Fold, Folder, SuperFold};
use amzn_smt_ir::logic::all::Op::Array;
use amzn_smt_ir::logic::ArrayOp;
use amzn_smt_ir::CoreOp::*;
use amzn_smt_ir::Quantifier::Exists;
use amzn_smt_ir::Quantifier::Forall;
use amzn_smt_ir::Sort;
use amzn_smt_ir::Term::Quantifier;
use amzn_smt_ir::{logic::*, Command as IRCommand, Script, Term as IRTerm};
use amzn_smt_ir::{IConst, ICoreOp, ILet, IMatch, IQuantifier, IUF};
use amzn_smt_ir::{IOp, ISort, ISymbol, IVar, QualIdentifier};

use smt2parser::concrete::Command::{DeclareConst, DeclareFun};

use atomic_counter::{AtomicCounter, ConsistentCounter};
use num_traits::identities::Zero;

use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::HashSet;

type Term = IRTerm<ALL>;
type Command = IRCommand<Term>;

#[derive(Default, Debug)]
pub struct ADTFlattener {
    // datatype_sort -> (member name, template name, member sort)
    datatypes: HashMap<ISymbol, Vec<(ISymbol, ISymbol, ISort)>>,
    accessors: HashSet<ISymbol>,

    // variable name -> sort
    var_sorts: HashMap<ISymbol, ISort>,

    // array of tuple index type -> nested array of array index type
    array_tuples: HashMap<ISort, ISort>,

    // array of tuple element type -> [array for member i]
    array_elem_tuples: HashMap<ISort, Vec<ISort>>,

    // Caches:
    //
    // scope -> variable name -> [name]
    // this is separated by scopes because a variable can have the same
    // name but different sorts in different quantifiers.
    var_names_cache: Vec<HashMap<ISymbol, Vec<ISymbol>>>,
    // sort -> [sort]
    sort_cache: HashMap<ISort, Vec<ISort>>,

    // Unique id generator.
    counter: ConsistentCounter,
}

// Main functions.
impl ADTFlattener {
    pub fn flatten(&mut self, commands: Script<Term>) -> Script<Term> {
        self.full_pass(commands)
    }

    fn full_pass(&mut self, commands: Script<Term>) -> Script<Term> {
        self.collect_datatypes(&commands);

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

        commands = self.remove_declare_datatypes(commands);

        assert!(parser::parse_from_string(&commands.to_string()).is_ok());

        commands
    }

    fn reset(&mut self) {
        self.var_names_cache.clear();
        self.var_names_cache.push(HashMap::default());
    }

    fn iterate(&mut self, commands: Script<Term>) -> Script<Term> {
        self.collect_global_var_sorts(&commands);
        self.collect_arrays_tuple_index();
        self.collect_arrays_tuple_elem();

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

    fn is_tuple_sort(&self, sort: &ISort) -> bool {
        self.datatypes.contains_key(sort.sym())
    }

    fn contains_tuple_sort(&self, sort: &ISort) -> bool {
        if self.is_tuple_sort(sort) {
            return true;
        }

        match sort.as_ref() {
            Sort::Simple { .. } => false,
            Sort::Parameterized {
                identifier: _,
                parameters,
            } => parameters
                .iter()
                .map(|p| self.contains_tuple_sort(p))
                .any(|x| x),
        }
    }

    fn datatype_sort_var(&self, term: &Term) -> Option<(ISort, IVar)> {
        match term {
            Term::Variable(var) => {
                let sort = self.var_sort(var);
                match self.datatypes.contains_key(sort.sym()) {
                    true => Some((sort, var.clone())),
                    false => None,
                }
            }
            _ => None,
        }
    }

    fn datatype_constructor_args(&self, term: &Term) -> Option<Vec<Term>> {
        match term {
            Term::UF(ref uf) => match self.datatypes.contains_key(&uf.func) {
                true => Some(Vec::from(uf.args.clone())),
                false => None,
            },
            _ => None,
        }
    }

    // TODO rewrite this when we have proper typed sorts
    fn is_array_tuple_index(&self, sort: &ISort) -> bool {
        match sort.as_ref() {
            Sort::Simple { .. } => false,
            Sort::Parameterized {
                identifier,
                parameters,
            } if identifier_symbol(identifier).to_string().as_str() == "Array"
                && parameters.len() == 2
                && self.is_tuple_sort(&parameters[0]) =>
            {
                true
            }
            _ => false,
        }
    }

    fn is_array_tuple_elem(&self, sort: &ISort) -> bool {
        match sort.as_ref() {
            Sort::Simple { .. } => false,
            Sort::Parameterized {
                identifier,
                parameters,
            } if identifier_symbol(identifier).to_string().as_str() == "Array"
                && parameters.len() == 2
                && self.is_tuple_sort(&parameters[1]) =>
            {
                true
            }
            _ => false,
        }
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
                                    ISymbol::from(format!("{}_{}", member, self.counter.inc())),
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

    fn collect_arrays_tuple_index(&mut self) {
        self.array_tuples.extend(
            self.sort_cache
                .clone()
                .into_iter()
                .filter(|(sort, _)| self.is_array_tuple_index(sort))
                .map(|(sort, _)| (sort.clone(), self.flatten_array_tuple(sort)))
                .collect::<HashMap<ISort, ISort>>(),
        );
    }

    fn collect_arrays_tuple_elem(&mut self) {
        self.array_elem_tuples.extend(
            self.sort_cache
                .clone()
                .into_iter()
                .filter(|(sort, _)| self.is_array_tuple_elem(sort))
                .map(|(sort, _)| (sort.clone(), self.flatten_array_tuple_elem(sort)))
                .collect::<HashMap<ISort, Vec<ISort>>>(),
        );
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
            // Flatten a tuple into its members.
            Some(members) => members
                .clone()
                .into_iter()
                .map(|(_, _, sort)| sort)
                .collect(),
            None => match self.is_array_tuple_elem(&sort) {
                // Flatten an array that has a tuple as index.
                // The order here is important, we need to
                // flatten those before the tuple index case.
                true => self.flatten_array_tuple_elem(sort),
                false => match self.is_array_tuple_index(&sort) {
                    // Flatten an array that has a tuple as element.
                    true => vec![self.flatten_array_tuple(sort)],
                    false => vec![sort],
                },
            },
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
                .map(|(_, template_name, _)| {
                    ISymbol::from(format!("{}_{}", symbol, template_name).replace("|", ""))
                })
                .collect(),
            // TODO this is disgusting \/
            // Should somehow reuse the map creating the names,
            // it's the same as the arm above.
            None => match self.is_array_tuple_elem(&sort) {
                true => match sort.as_ref() {
                    Sort::Parameterized {
                        identifier: _,
                        parameters,
                    } => self
                        .datatypes
                        .get(parameters[1].sym())
                        .unwrap()
                        .iter()
                        .map(|(_, template_name, _)| {
                            ISymbol::from(format!("{}_{}", symbol, template_name).replace("|", ""))
                        })
                        .collect(),
                    _ => vec![symbol],
                },
                _ => vec![symbol],
            },
        }
    }

    fn flatten_accessor(&self, accessor: &ISymbol, var: &IVar<QualIdentifier>) -> ISymbol {
        let sort = self.var_sort(var);
        let dt = self.datatypes.get(sort.sym()).unwrap();
        let dt_info = dt.iter().find(|(name, _, _)| name == accessor);
        assert!(dt_info.is_some());
        ISymbol::from(format!("{}_{}", var_symbol(var), dt_info.unwrap().1).replace("|", ""))
    }

    fn flatten_array_tuple(&self, sort: ISort) -> ISort {
        match self.is_array_tuple_index(&sort) {
            true => match sort.as_ref() {
                Sort::Parameterized {
                    identifier,
                    parameters,
                } => self
                    .datatypes
                    .get(parameters[0].sym())
                    .unwrap()
                    .iter()
                    .map(|(_, _, sort)| sort)
                    .rev()
                    .fold(
                        self.flatten_array_tuple(parameters[1].clone()),
                        |acc, member_sort| {
                            Sort::Parameterized {
                                identifier: identifier.clone(),
                                parameters: [self.flatten_array_tuple(member_sort.clone()), acc]
                                    .to_vec(),
                            }
                            // TODO can we remove some clones here?
                            .into()
                        },
                    ),
                _ => unreachable!(),
            },
            false => sort,
        }
    }

    fn flatten_array_tuple_elem(&self, sort: ISort) -> Vec<ISort> {
        match self.is_array_tuple_elem(&sort) {
            true => match sort.as_ref() {
                Sort::Parameterized {
                    identifier,
                    parameters,
                } => self
                    .datatypes
                    .get(parameters[1].sym())
                    .unwrap()
                    .iter()
                    .map(|(_, _, sort)| {
                        Sort::Parameterized {
                            identifier: identifier.clone(),
                            parameters: [parameters[0].clone(), sort.clone()].to_vec(),
                        }
                        .into()
                    })
                    .collect(),
                _ => unreachable!(),
            },
            false => vec![sort],
        }
    }

    fn flatten_select_array_tuple_elem(
        &mut self,
        array: &IVar<QualIdentifier>,
        idx: &Term,
    ) -> Vec<Term> {
        // Replace `select` inside fun appl,
        // where its array has tuple element type,
        // but its new indexed arrays.
        self.flatten_var_decl((var_symbol(array), self.var_sort(array)))
            .into_iter()
            .map(|(name, _)| ArrayOp::Select(name.into(), idx.clone()).into())
            .collect()
    }
}

// Top level commands flatteners.
impl ADTFlattener {
    fn flatten_assertion(&mut self, assertion: Term) -> IRCommand<Term> {
        self.var_names_cache
            .push(self.var_names_cache.last().unwrap().clone());

        self.collect_quant_vars(&assertion);

        let assertion = self.flatten_quant_vars(assertion);
        //self.flatten_quant_vars(&assertion);

        //println!("Var sorts AFTER are {:?}", self.var_sorts);
        let mut t = assertion.fold_with(self).unwrap();

        if let Quantifier(ref quantifier) = t {
            if let Forall(ref vars, ref term) = quantifier.as_ref() {
                let x = BTreeMap::<ISymbol, ISort>::from_iter(vars.clone());
                //x.extend(self.var_sorts.clone());
                t = Term::from(Forall(Vec::from_iter(x), term.clone()));
            }
        }

        self.var_names_cache.pop();

        IRCommand::Assert { term: t }
    }

    fn flatten_quant_vars(&mut self, assertion: Term) -> Term {
        // TODO can we clone less stuff here?
        match assertion {
            Quantifier(ref quantifier) => match quantifier.as_ref() {
                Forall(vars, term) => {
                    Term::from(Forall(
                        vars.clone()
                            .into_iter()
                            .map(|var| {
                                // TODO does this make sense?
                                let mut v = self.flatten_var_decl(var.clone());
                                if !self.contains_tuple_sort(&var.1) {
                                    v.push(var);
                                }
                                v
                            })
                            .collect::<Vec<Vec<(ISymbol, ISort)>>>()
                            .into_iter()
                            .flatten()
                            .collect(),
                        term.clone(),
                    ))
                }
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
            match &args[0] {
                Term::Variable(var) => {
                    return Ok(Term::from(IVar::from(QualIdentifier::from(
                        self.flatten_accessor(func, var),
                    ))));
                }
                Term::OtherOp(ref op) => {
                    if let Array(ArrayOp::Select(Term::Variable(ref array), ref idx)) = op.as_ref()
                    {
                        /*
                         * if arg is a select:
                         * element of array must be a tuple
                         * first resolve the array itself. If the array has tuple element type,
                         * one select will become multiple selects.
                         * After that, fold each select so that the indices are resolved into
                         * nested selects.
                         * After that, the index of the accessor in the tuple is the index of the
                         * array that should be used.
                         */
                        let selects: Vec<Term> =
                            match self.is_array_tuple_elem(&self.var_sort(array)) {
                                true => self.flatten_select_array_tuple_elem(array, idx),
                                false => vec![op.clone().into()],
                            };
                        let nested_selects: Vec<Term> = selects
                            .into_iter()
                            .map(|select| select.fold_with(self).unwrap())
                            .collect();
                        // TODO improve this search
                        let pos = self
                            .datatypes
                            .iter()
                            .map(|(_, members)| {
                                members.iter().position(|(member, _, _)| member == func)
                            })
                            .fold(None, |acc, x| match (acc, x) {
                                (Some(_), Some(_)) => panic!(),
                                (_, Some(x)) => Some(x),
                                (Some(acc), _) => Some(acc),
                                _ => None,
                            });
                        // TODO assert that members has same length as
                        // nested_selects.
                        assert!(pos.is_some());
                        let pos = pos.unwrap();
                        assert!(pos < nested_selects.len());
                        return Ok(nested_selects[pos].clone());
                    }
                }
                _ => {}
            }
        } else {
            let mut uf = uf.super_fold_with(self)?;
            uf.args = (Vec::from(uf.args).into_iter())
                .map(|arg| match arg {
                    // Replace function application over tuple variables.
                    Term::Variable(ref var)
                        if self.has_datatype_sort(var) ||
                            self.is_array_tuple_elem(&self.var_sort(var))
                        =>
                        self
                            // TODO make sure these vars are declared/have a sort.
                            .flatten_var_name(var_symbol(var))
                            .into_iter()
                            .map(|arg| arg.into())
                            .collect()
                    ,
                    // Replace tuple constructor inside function application.
                    Term::UF(ref arg_uf) => {
                        match self.datatype_constructor_args(&Term::from(arg_uf)) {
                            Some(args) => args,
                            None => vec![arg],
                        }
                    },
                    Term::OtherOp(ref op) => {
                        match op.as_ref() {
                            Array(ArrayOp::Select(Term::Variable(ref array), ref idx))
                                if self.is_array_tuple_elem(&self.var_sort(array)) =>
                            {
                                self.flatten_select_array_tuple_elem(array, idx)
                            }
                            _ => vec![arg],
                        }
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

    fn fold_core_op(&mut self, op: ICoreOp<ALL>) -> Result<Self::Output, Self::Error> {
        let op = op.super_fold_with(self)?;
        match op {
            // TODO organize this better.
            Eq(ref args) => {
                let new_args: Vec<Option<Vec<Term>>> = args
                    .iter()
                    .map(|arg| {
                        if let Some(args) = self.datatype_constructor_args(arg) {
                            // Replace tuple constructor inside equality by
                            // its arguments.
                            Some(args)
                        } else if let Some((_, var)) = self.datatype_sort_var(arg) {
                            // Replace DT var by its flattened new vars.
                            Some(
                                self.flatten_var_decl((var_symbol(&var), self.var_sort(&var)))
                                    .into_iter()
                                    .map(|(name, _)| Term::Variable(name.into()))
                                    .collect(),
                            )
                        } else if let Term::Variable(var) = arg {
                            //println!("Var {} is not DT has sort {:?}", var_symbol(&var), self.var_sort(&var));
                            if self.contains_tuple_sort(&self.var_sort(var)) {
                                //println!("Contains tuple sort");
                                Some(
                                    self.flatten_var_decl((var_symbol(var), self.var_sort(var)))
                                        .into_iter()
                                        .map(|(name, _)| Term::Variable(name.into()))
                                        .collect(),
                                )
                            } else {
                                None
                            }
                        } else if let Term::OtherOp(ref op) = arg {
                            match op.as_ref() {
                                Array(ArrayOp::Select(Term::Variable(ref array), ref idx))
                                    if self.is_array_tuple_elem(&self.var_sort(array)) =>
                                {
                                    // Replace `select` inside equality,
                                    // where its array has tuple element type,
                                    // but its new indexed arrays.
                                    Some(
                                        self.flatten_var_decl((
                                            var_symbol(array),
                                            self.var_sort(array),
                                        ))
                                        .into_iter()
                                        .map(|(name, _)| {
                                            ArrayOp::Select(name.into(), idx.clone()).into()
                                        })
                                        .collect(),
                                    )
                                }
                                _ => None,
                            }
                        } else {
                            None
                        }
                    })
                    .collect();

                // from SmallVec
                assert!(new_args.len() == 2);

                if new_args[0].is_none() || new_args[1].is_none() {
                    return Ok(op.into());
                }

                let left = new_args[0].as_ref().unwrap();
                let right = new_args[1].as_ref().unwrap();
                assert_eq!(left.len(), right.len());

                let conj: Option<Term> = left
                    .clone()
                    .into_iter()
                    .zip(right.clone().into_iter())
                    .map(|(a, b)| Eq([a, b].into()).into())
                    .collect::<Vec<Term>>()
                    .into_iter()
                    .reduce(|acc, eq| And([acc, eq].into()).into());

                Ok(conj.unwrap())
            }
            _ => Ok(op.into()),
        }
    }

    fn fold_theory_op(&mut self, op: IOp<ALL>) -> Result<Self::Output, Self::Error> {
        let op = op.super_fold_with(self)?;
        match op {
            // We need to transform the element first,
            // so block index folding for now.
            Array(ArrayOp::Select(Term::Variable(ref array), _))
                if self.is_array_tuple_elem(&self.var_sort(array)) =>
            {
                Ok(op.into())
            }
            // Identify `select`s where the index
            // - is a variable and has tuple sort.
            Array(ArrayOp::Select(ref array, Term::Variable(ref idx)))
                if self.has_datatype_sort(idx) =>
            {
                Ok(self
                    // TODO make sure these vars are declared/have a sort.
                    .flatten_var_name(var_symbol(idx))
                    .into_iter()
                    .fold(array.clone(), |acc, x| {
                        ArrayOp::Select(acc, x.into()).into()
                    }))
            }
            // - is a tuple constructor.
            Array(ArrayOp::Select(ref array, ref idx)) => match self.datatype_constructor_args(idx)
            {
                Some(args) => Ok(args
                    .into_iter()
                    .fold(array.clone(), |acc, x| ArrayOp::Select(acc, x).into())),
                _ => Ok(op.into()),
            },
            _ => Ok(op.into()),
        }
    }

    fn fold_const(&mut self, constant: IConst) -> Result<Self::Output, Self::Error> {
        Ok(constant.into())
    }

    fn fold_var(&mut self, var: IVar<QualIdentifier>) -> Result<Self::Output, Self::Error> {
        Ok(var.into())
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
