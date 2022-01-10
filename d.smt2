(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int)) (|a| Int)  ))))

(declare-fun f ( (Array Int Int) Int) Bool)

(declare-const x Int)
(declare-const y Int)
(declare-const s |state_type|)
(declare-const s2 |state_type|)

(assert
(and
	(= x (select (|balances| s) 1))
	(= y (select (|balances| s2) 2))
	(= x y)
))

(check-sat)

