(set-logic HORN)

(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|bytes_tuple_accessor_array| (Array Int Int)) (|bytes_tuple_accessor_length| Int)))))

(declare-fun f (Int (Array |bytes_tuple| Int) Int) Bool)
