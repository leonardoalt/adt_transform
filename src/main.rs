// Modified from https://github.com/awslabs/rust-smt-ir/blob/main/amzn-smt-string-fct-updater/src/main.rs
// Therefore:
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use adt_transform::transform::*;
use adt_transform::*;

use std::{env, fs, io};

fn main() {
    let file_to_convert = env::args().nth(1).expect(
        "Expected command line arg specifying SMTLIB file to convert (without file extension)",
    );

    let mut file_ext = ".smtlib";
    let mut file = fs::File::open(file_to_convert.clone() + file_ext);
    if file.is_err() {
        file_ext = ".smt2";
        file = fs::File::open(file_to_convert + file_ext);
    }
    let file = file.expect("Error reading input file: did you accidentally include the file extension, or try to read a file without extension smtlib or smt2?");
    let reader = io::BufReader::new(file);
    let problem = transform::parse(reader).unwrap();

    let problem = ADTFlattener::default().flatten(problem);
    println!("; Auto-generated flattened instance without ADTs.");
    println!("{}", problem.to_string());
}
