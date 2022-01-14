(declare-datatypes ((my_tuple 0)) (((my_tuple (member1 (Array Int Int)) (member2 Int) ))))

(declare-const t1 my_tuple)

(assert
	(> (member2 t1) (select (member1 t1) 5))
)

(check-sat)
