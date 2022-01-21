SMT ADT Remover
===============

This tool aims at removing ADTs from smtlib2 instances that only use the Tuples
subset of ADTs. Not all syntax is supported, check the Unsupported section below.

Flattening
----------

The basic strategy is flattening the tuples so that tuple members become
separate variables in the context where they are used.

This implies that:

1) A **variable of tuple type** is transformed into one or more variables
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

2) A **tuple constructor** transformation needs to take its context into account.

- 2.1) If it is used in an **equality**, we need a new equality for each member.

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

- 2.2) If it is used in a **function application**, we just apply the function
  on the new variables instead.

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

- 2.3) A **tuple accessor** transformation simply uses the new variable created
  for that member.

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

3) **Functions** that take tuples as parameters may now increase their arity, as
shown in 2.2 above.

4) **Nested tuples** are flattened in consecutive stages until there are no more
tuples left.

Unsupported Syntax
------------------

- Tuples with more than one constructor.
- Tuples whose constructor's name is different from the tuple's name.
- Accessor functions must be applied to a variable of a tuple sort or another
  accessor function (in case of nested tuples). If they are applied over
  another function application or tuple constructor, neither will be flattened.
- Tuples inside `let` and `match` expressions.
- Tuples as array index (see below).

Tuples as Index Sort of Arrays
------------------------------

Flattening tuples that are used as indices of arrays is more complicated.
If we have a tuple `T: (T1, T2)` and an array `A: (Array T Int)`, we need
two arrays:

- `A2: (Array T2 Int)`
- `A1: (Array T1 (Array T2 Int))`

so that `A` is replaced by `A1`.

Let `a` be of sort `A` and `t` of sort `T`.

- `(select a t)` ->

Variable `t` is transformed into `t_1` and `t_2`.

Now we have `a1` of sort `A1`, `t_1` of sort `T1` and `t_2` of sort `T2`.

The resulting select is:
`(select (select a1 t1) t2)`

- `(select a (T x y))` -> `(select (select a1 x) y)`

- `(store a t v)` -> `(store a1 t1 (store (select a1 t1) t2 v))`
That is, `select` until the last tuple member (not included) to retrieve the
innermost array; store the value in the innermost array; store the resulting
array in decreasing index order of tuple member.
