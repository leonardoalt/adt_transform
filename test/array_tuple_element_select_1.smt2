(set-logic HORN)

(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))

(assert (forall ((a (Array Int |bytes_tuple|)))
	true
))

(check-sat)
