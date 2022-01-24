(declare-datatypes ((|tuple(bytes32,uint8,bytes32,bytes32)| 0)) (((|tuple(bytes32,uint8,bytes32,bytes32)| (|tuple(bytes32,uint8,bytes32,bytes32)_accessor_0| Int) (|tuple(bytes32,uint8,bytes32,bytes32)_accessor_1| Int) (|tuple(bytes32,uint8,bytes32,bytes32)_accessor_2| Int) (|tuple(bytes32,uint8,bytes32,bytes32)_accessor_3| Int)))))

(declare-const t1 |tuple(bytes32,uint8,bytes32,bytes32)|)

(check-sat)
