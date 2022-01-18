(declare-datatypes ((my_tuple 0)) (((my_tuple (member1 (Array Int Int)) (member2 Int) ))))

(declare-const a (Array Int Int))
(declare-const i Int)

(declare-fun f (my_tuple Int) Bool)

(assert
	(f (my_tuple a i) 3)
)

(check-sat)
