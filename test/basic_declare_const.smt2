(declare-const a Int)
(declare-const b Int)
(declare-const c Int)

(declare-datatypes ((my_tuple 0)) (((my_tuple (member1 (Array Int Int)) (member2 Int) ))))

(declare-const t1 my_tuple)
(declare-const t2 my_tuple)

(declare-fun f (Int my_tuple Int)  Bool)

(assert
(forall ((d Int) (tt my_tuple))
(and
	(= (member1 t1) (member2 t2))
	(= (member1 t1) (member1 tt))
	(> d 0)
	(> a b)
	(> b c)
	(> c a)
)
)
)

(check-sat)
