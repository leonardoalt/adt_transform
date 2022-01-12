// Modified from https://github.com/awslabs/rust-smt-ir/blob/main/amzn-smt-string-fct-updater/src/main.rs
// Therefore:
// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use adt_transform::parser;
use adt_transform::transform;

use std::env;

fn main() {
    let file_to_convert = env::args().nth(1).expect(
        "Expected command line arg specifying SMTLIB file to convert (without file extension)",
    );
    let problem = parser::parse_from_file(file_to_convert).unwrap();

    let problem = transform::ADTFlattener::default().flatten(problem);
    println!("; Auto-generated flattened instance without ADTs.");
    println!("{}", problem);
}
