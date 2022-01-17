(declare-datatypes ((my_tuple 0)) (((my_tuple (member1 (Array Int Int)) (member2 Int) ))))
(declare-datatypes ((my_nested_tuple 0)) (((my_nested_tuple (nested1 my_tuple) (nested2 Bool) ))))
(declare-datatypes ((my_nested_nested_tuple 0)) (((my_nested_nested_tuple (nested_nested1 my_nested_tuple) (nested_nested2 Bool) ))))

(declare-const t1 my_tuple)
(declare-const n1 my_nested_tuple)
(declare-const nn1 my_nested_nested_tuple)

(assert
(=
	(select (member1 (nested1 (nested_nested1 nn1))) (member2 t1))
	(member2 (nested1 (nested_nested1 nn1)))
)
)

(check-sat)
