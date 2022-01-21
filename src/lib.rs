// SPDX-License-Identifier: GPL-3.0-only

pub mod helpers;
pub mod parser;
pub mod transform;

#[cfg(test)]
mod tests {
    use super::*;
    use std::{fs, fs::File, path::Path};

    #[test]
    fn test_transform_dir_no_update() {
        test_transform_dir(false);
    }

    #[test]
    #[ignore]
    fn test_transform_dir_update() {
        test_transform_dir(true);
    }

    fn test_transform_dir(update: bool) {
        let dir = Path::new("./test");
        assert!(dir.is_dir());
        for entry in fs::read_dir(dir).unwrap() {
            let entry = entry.unwrap();
            let path = entry.path();
            if path.extension().unwrap() == "smt2" {
                let expectation = path.clone().with_extension("expectation");
                if !Path::new(&expectation).exists() {
                    assert!(File::create(&expectation).is_ok());
                }
                test_transform(
                    path.to_str().unwrap(),
                    expectation.to_str().unwrap(),
                    update,
                );
            }
        }
    }

    fn test_transform(test_file: &str, expect_file: &str, update: bool) {
        assert!(Path::new(&test_file).exists());
        assert!(Path::new(&expect_file).exists());
        println!("Testing file {}...", test_file);
        let transformed = transform::ADTFlattener::default()
            .flatten(parser::parse_from_file(test_file.to_string()).unwrap())
            .to_string();
        let expected = fs::read_to_string(expect_file).expect("I need to read this file.");
        if transformed != expected {
            if update {
                assert!(fs::write(expect_file, transformed).is_ok());
            } else {
                println!("Expected:\n{}\nGot:\n{}", expected, transformed);
                assert!(false);
            }
        }
    }
}
