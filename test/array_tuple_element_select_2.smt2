(set-logic HORN)

(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))

(assert (forall ((a (Array Int |bytes_tuple|)) (b (Array Int |bytes_tuple|)))
(=
	(select a 222)
	(select b 333)
)
))

(check-sat)
