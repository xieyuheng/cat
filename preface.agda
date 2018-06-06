module preface where

type-tt = Set

data bool-u : type-tt where
  true-c : bool-u
  false-c : bool-u

not : bool-u -> bool-u
not true-c = false-c
not false-c = true-c

or : bool-u -> bool-u -> bool-u
or false-c x = x
or true-c _  = true-c

and : bool-u -> bool-u -> bool-u
and true-c x = x
and false-c _  = false-c

if : {n : _} {A : Set n} -> bool-u -> A -> A -> A
if true-c x y = x
if false-c x y = y

data nat-u : type-tt where
  zero-c : nat-u
  succ-c : nat-u -> nat-u

add : nat-u -> nat-u -> nat-u
add zero-c n = n
add (succ-c m) n = (succ-c (add m n))

mul : nat-u -> nat-u -> nat-u
mul zero-c n = zero-c
mul (succ-c m) n = (add n (mul m n))

nat-eq-p : nat-u -> nat-u -> bool-u
nat-eq-p zero-c zero-c = true-c
nat-eq-p zero-c (succ-c n) = false-c
nat-eq-p (succ-c n) zero-c = false-c
nat-eq-p (succ-c n) (succ-c m) = (nat-eq-p n m)

-- compose : {A : type-tt}
--           {B : A -> type-tt}
--           {C : {x : A} -> (B x) -> type-tt} ->
--           (f : {x : A} (y : B x) -> (C y)) ->
--           (g : (x : A) -> (B x)) ->
--           ((x : A) -> (C (g x)))
-- compose f g = (λ x -> (f (g x)))

data eqv-t {A : type-tt} (q : A) : A -> type-tt where
  eqv-c : (eqv-t q q)

cong : {A B : _} (f : A -> B)
       {x y : _} -> (eqv-t x y) -> (eqv-t (f x) (f y))
cong f eqv-c = eqv-c

-- nat-associe : (x y z : nat-u) ->
--               (eqv-t (add x (add y z)) (add (add x y) z))
-- nat-associe zero-c y z = eqv-c
-- nat-associe (succ-c x) y z = (cong succ-c (nat-associe x y z))

nat-associe : (x y z : nat-u) ->
              (eqv-t (add x (add y z)) (add (add x y) z))
nat-associe zero-c y z = eqv-c
nat-associe (succ-c x) y z = (cong succ-c (nat-associe x y z))

-- nat-commute : (x y : nat-u) -> (eqv-t (add x y) (add y x))
-- nat-commute zero-c zero-c = eqv-c
-- nat-commute (succ-c x) zero-c = (cong succ-c (nat-commute x zero-c))
-- nat-commute zero-c y = {!!}
-- nat-commute (succ-c x) y = {!!}

data vect-u (A : type-tt) : nat-u -> type-tt where
  null-vect-c : vect-u A zero-c
  cons-vect-c : {n : nat-u} -> A -> (vect-u A n) -> (vect-u A (succ-c n))
