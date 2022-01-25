(set-logic HORN)

(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))

(declare-datatypes ((|ecrecover_input_type| 0)) (((|ecrecover_input_type| (|hash| Int) (|v| Int) (|r| Int) (|s| Int)))))

(declare-datatypes ((|crypto_type| 0)) (((|crypto_type| (|ecrecover| (Array |ecrecover_input_type| Int)) (|keccak256| (Array |bytes_tuple| Int)) (|ripemd160| (Array |bytes_tuple| Int)) (|sha256| (Array |bytes_tuple| Int))))))

(assert (forall ((x |crypto_type|) (b |bytes_tuple|) (e |ecrecover_input_type|))
(and
	(= (select (|ecrecover| x) (|ecrecover_input_type| (|bytes_tuple_accessor_length| b) 2 3 4)) 42)
	(= (select (|keccak256| x) (|bytes_tuple| (|bytes_tuple_accessor_array| b) (|bytes_tuple_accessor_length| b))) 42)
	(= (select (|ripemd160| x) b) 42)
	(= (select (|sha256| x) b) 42)
)
))

(check-sat)
