pub mod helpers;
pub mod parser;
pub mod transform;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn smoke() {
        assert_eq!(2 + 2, 4);
    }

    #[test]
    fn declare_const() {
        let smt1 = "(declare-datatypes ((my_tuple 0)) (((my_tuple (member1 (Array Int Int)) (member2 Int) ))))
(declare-const t1 my_tuple)";
        let smt2 = "(declare-const t1_my_tuple_member1 (Array Int Int))
(declare-const t1_my_tuple_member2 Int)
";
        assert_eq!(
            run_transform(smt1),
            smt2
        );
    }

    fn run_transform(content: &str) -> String {
        transform::ADTFlattener::default()
            .flatten(
                parser::parse_from_string(content).unwrap()
            )
            .to_string()
    }
}
