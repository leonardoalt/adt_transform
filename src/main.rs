use adt_transform::parser;
use adt_transform::transform;

use std::env;

fn main() {
    let file_to_convert = env::args()
        .nth(1)
        .expect("Expected SMTLIB file with file extension");
    let problem = parser::parse_from_file(file_to_convert).unwrap();

    let problem = transform::ADTFlattener::default().flatten(problem);
    println!("; Auto-generated flattened instance without ADTs.");
    println!("{}", problem);
}
