(declare-datatypes ((my_tuple 0)) (((my_tuple (member1 (Array Int Int)) (member2 Int) ))))

(declare-const a (Array Int Int))
(declare-const i Int)

(assert
(=
	(my_tuple a i)
	(my_tuple a i)
)
)

(check-sat)
