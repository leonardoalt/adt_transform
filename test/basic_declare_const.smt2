(declare-datatypes ((my_tuple 0)) (((my_tuple (member1 (Array Int Int)) (member2 Int) ))))

(declare-const t1 my_tuple)
(declare-const t2 my_tuple)

(assert
	(= (select (member1 t1) 3) (member2 t2))
)

(check-sat)
