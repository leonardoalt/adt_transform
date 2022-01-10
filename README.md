SMT ADT Remover
===============

This tool aims at removing ADTs from smtlib2 instances that only use the Tuples
subset of ADTs.

Flattening
----------

The basic strategy is flattening the tuples so that tuple members become
separate variables in the context where they are used.

This implies that:

1) A variable of tuple type is transformed into one or more variables
representing each tuple member.

```
(declare-datatypes ((|my_tuple| 0)) (((|my_tuple| (|member1| (Array Int Int)) (|member2| Int) ))))
(declare-const t |my_tuple|)
```
->
```
(declare-const t_member1 (Array Int Int))
(declare-const t_member2 Int)
```

The same is valid for variable declarations inside quantifiers.

2) A tuple constructor transformation needs to take its context into account.

2.1) If it is used in an equality, we need a new equality for each member.

```
(declare-datatypes ((|my_tuple| 0)) (((|my_tuple| (|member1| (Array Int Int)) (|member2| Int) ))))
(declare-const t1 |my_tuple|)
(declare-const t2 |my_tuple|)

(assert (= t1 t2))
```
->
```
(declare-const t1_member1 (Array Int Int))
(declare-const t1_member2 Int)
(declare-const t2_member1 (Array Int Int))
(declare-const t2_member2 Int)

(assert (and
	(= t1_member1 t2_member1)
	(= t1_member2 t2_member2)
))
```

2.2) If it is used in a function application, we just apply the function on the
new variables instead.

```
(declare-datatypes ((|my_tuple| 0)) (((|my_tuple| (|member1| (Array Int Int)) (|member2| Int) ))))
(declare-fun (|my_tuple|) Bool)

(declare-const t |my_tuple|)
(declare-const a (Array Int Int))
(declare-const i Int)

(assert (f (|my_tuple| a i)))
```
->
```
(declare-fun ( (Array Int Int) Int ) Bool)

(declare-const a (Array Int Int))
(declare-const i Int)

(assert (f a i))
```

2.3) A tuple accessor transformation simply uses the new variable created for
that member.

```
(declare-datatypes ((|my_tuple| 0)) (((|my_tuple| (|member1| (Array Int Int)) (|member2| Int) ))))
(declare-const t |my_tuple|)

(assert (> (|member2| t) 0))
```
->
```
(declare-const t_member1 (Array Int Int))
(declare-const t_member2 Int)

(assert (> t_member2 0))
```

3) Functions that take tuples as parameters may now increase their arity, as
shown in 2.2 above.

4) Recursive tuples are flattened in consecutive stages until there are no more
tuples left.

Tuples as Index Sort of Arrays
------------------------------

TODO
