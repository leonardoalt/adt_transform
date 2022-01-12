use amzn_smt_ir::{logic::*, ParseError, Script, Term as IRTerm};

use std::{fs, io};

type Term = IRTerm<ALL>;

///
/// Build an iterator from an input buffer. The input is parsed as a list of commands
/// in SMT-LIB syntax.
///
fn parse(smtlib: impl std::io::BufRead) -> Result<Script<Term>, ParseError<ALL>> {
    Script::<Term>::parse(smtlib)
}

pub fn parse_from_string(content: &str) -> Result<Script<Term>, ParseError<ALL>> {
    parse(content.as_bytes())
}

pub fn parse_from_file(filename: String) -> Result<Script<Term>, ParseError<ALL>> {
    let file = fs::File::open(filename);
    let file =
        file.expect("Error reading input file: did you try to read a file without extension smt2?");
    let reader = io::BufReader::new(file);

    parse(reader)
}
