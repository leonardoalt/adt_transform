(declare-datatypes ((my_tuple 0)) (((my_tuple (member1 (Array Int Int)) (member2 Int) ))))
(declare-datatypes ((my_nested_tuple 0)) (((my_nested_tuple (nested1 my_tuple) (nested2 Bool) ))))

(declare-const t1 my_tuple)
(declare-const n1 my_nested_tuple)

(assert
	(= (member2 (nested1 n1)) (member2 t1))
)

(check-sat)
