// SPDX-License-Identifier: GPL-3.0-only

use amzn_smt_ir::{IIdentifier, ISymbol, IVar, Identifier, QualIdentifier};

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
