(declare-datatypes ((|state_type| 0)) (((|state_type| (|balances| (Array Int Int))))))

(declare-const x Int)
(declare-const y Int)
(declare-const s |state_type|)

(assert
(and
	(= x (select (|balances| s) 1))
	(= y (select (|balances| s) 2))
	(= x y)
))

(check-sat)

