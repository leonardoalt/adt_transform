(declare-datatypes ((my_tuple 0)) (((my_tuple (member1 (Array Int Int)) (member2 Int) ))))

(declare-const a (Array Int Int))
(declare-const i Int)

(declare-fun f (my_tuple Int) Bool)
(declare-fun g (Int Bool) Bool)

(assert
	(g 5 (f (my_tuple a i) 3))
)

(check-sat)
