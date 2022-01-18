(declare-datatypes ((my_tuple 0)) (((my_tuple (member1 (Array Int Int)) (member2 Int) ))))

(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const t my_tuple)

(assert
(and
	(=
		(my_tuple a i)
		(my_tuple
			(store (member1 t) 2 3)
			(member2 t)
		)
	)
)
)

(check-sat)
