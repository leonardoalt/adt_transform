(declare-datatypes ((my_tuple 0)) (((my_tuple (member1 (Array Int Int)) (member2 Int) ))))

(declare-const a (Array Int Int))
(declare-const i Int)
(declare-const t my_tuple)

(assert
(and
	(=
		(member1 t)
		(store a 2 3)
	)
	(=
		(member2 t)
		42
	)
	(=
		(my_tuple a i)
		t
	)
)
)

(check-sat)
