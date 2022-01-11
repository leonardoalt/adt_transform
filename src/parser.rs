use amzn_smt_ir::{logic::*, ParseError, Script, Term as IRTerm};

type Term = IRTerm<ALL>;

///
/// Build an iterator from an input buffer. The input is parsed as a list of commands
/// in SMT-LIB syntax.
///
pub fn parse(smtlib: impl std::io::BufRead) -> Result<Script<Term>, ParseError<ALL>> {
    Script::<Term>::parse(smtlib)
}
