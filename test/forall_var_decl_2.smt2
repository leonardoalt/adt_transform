(declare-datatypes ((my_tuple 0)) (((my_tuple (member1 (Array Int Int)) (member2 Int) ))))

(declare-const t1 my_tuple)

(assert
(forall ((d Int) (tt my_tuple))
(and
	(= (member1 t1) (member1 tt))
	(> d (member2 tt))
)
)
)

(assert
(forall ((tt Int) (d my_tuple))
(and
	(= (member1 t1) (member1 d))
	(> tt (member2 d))
)
)
)


(check-sat)
