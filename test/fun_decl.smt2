(declare-datatypes ((my_tuple 0)) (((my_tuple (member1 (Array Int Int)) (member2 Int) ))))

(declare-fun f (Int my_tuple Int)  Bool)

(check-sat)
