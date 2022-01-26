(declare-datatypes ((|bytes_tuple| 0)) (((|bytes_tuple| (|array| (Array Int Int)) (|length| Int)))))

(declare-datatypes ((|abi_type| 0)) (((|abi_type| 
	;(|abiencode| (Array |bytes_tuple| |bytes_tuple|)) 
	(|abiencodepacked_slice| (Array |bytes_tuple| |bytes_tuple|)) 
	;(|abiencodepacked| (Array |bytes_tuple| |bytes_tuple|))
))))

(declare-fun f (|abi_type|) Bool)

(assert
(forall ( (abi_0 |abi_type|) (expr_19 |bytes_tuple|) )
(=
	expr_19
	(select
		(|abiencodepacked_slice|
			abi_0
		)
		expr_19
	)
)
))
