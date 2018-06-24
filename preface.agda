module preface where


type-tt = Set

type-t0 = Set
type-t1 = Set1


data eqv-t {A : type-tt} (q : A) : A -> type-tt where
  eqv-c : (eqv-t q q)

cong : {A B : _} (f : A -> B)
       {x y : _} -> (eqv-t x y) -> (eqv-t (f x) (f y))
cong f eqv-c = eqv-c


data bool-t : type-tt where
  true-c : bool-t
  false-c : bool-t

not : bool-t -> bool-t
not true-c = false-c
not false-c = true-c

or : bool-t -> bool-t -> bool-t
or false-c x = x
or true-c _  = true-c

and : bool-t -> bool-t -> bool-t
and true-c x = x
and false-c _  = false-c

if : {n : _} {A : Set n} -> bool-t -> A -> A -> A
if true-c x y = x
if false-c x y = y


data nat-t : type-tt where
  zero-c : nat-t
  succ-c : nat-t -> nat-t

add : nat-t -> nat-t -> nat-t
add zero-c n = n
add (succ-c m) n = (succ-c (add m n))

mul : nat-t -> nat-t -> nat-t
mul zero-c n = zero-c
mul (succ-c m) n = (add n (mul m n))

nat-associe
  : (x y z : nat-t) ->
    (eqv-t
      (add x (add y z))
      (add (add x y) z))
nat-associe zero-c y z = eqv-c
nat-associe (succ-c x) y z =
  cong succ-c (nat-associe x y z)

-- nat-commute : (x y : nat-t) -> (eqv-t (add x y) (add y x))
-- nat-commute zero-c zero-c = eqv-c
-- nat-commute (succ-c x) zero-c = (cong succ-c (nat-commute x zero-c))
-- nat-commute zero-c y = {!!}
-- nat-commute (succ-c x) y = {!!}


data vect-t (A : type-tt) : nat-t -> type-tt where
  null-vect-c : vect-t A zero-c
  cons-vect-c : {n : nat-t} -> A -> (vect-t A n) -> (vect-t A (succ-c n))
