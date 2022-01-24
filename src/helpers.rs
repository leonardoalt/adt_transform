// SPDX-License-Identifier: GPL-3.0-only

use amzn_smt_ir::{logic::*, IIdentifier, ISymbol, IVar, Identifier, QualIdentifier, Term as IRTerm};

type Term = IRTerm<ALL>;

pub fn identifier_symbol(identifier: &IIdentifier) -> ISymbol {
    match identifier.as_ref() {
        Identifier::Simple { symbol } => symbol.clone(),
        Identifier::Indexed { symbol, .. } => symbol.clone(),
    }
}

pub fn var_symbol(var: &IVar<QualIdentifier>) -> ISymbol {
    match var.as_ref() {
        QualIdentifier::Simple { identifier } => identifier_symbol(identifier),
        QualIdentifier::Sorted { identifier, .. } => identifier_symbol(identifier),
    }
}

pub fn is_variable<'a>(term: &'a Term) -> Option<&'a IVar<QualIdentifier>> {
    match term {
        Term::Variable(var) => Some(var),
        _ => None,
    }
}
