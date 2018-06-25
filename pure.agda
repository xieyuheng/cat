module pure where

-- type --

type-tt = Set

type-t0 = Set
type-t1 = Set1

-- eqv --

data eqv-t {A : type-tt} (q : A) : A -> type-tt where
  eqv-c : (eqv-t q q)

cong : {A B : _} (f : A -> B)
       {x y : _} -> (eqv-t x y) -> (eqv-t (f x) (f y))
cong f eqv-c = eqv-c

-- bool --

data bool-t : type-tt where
  true-c : bool-t
  false-c : bool-t

bool-not : bool-t -> bool-t
bool-not true-c = false-c
bool-not false-c = true-c

bool-or : bool-t -> bool-t -> bool-t
bool-or false-c x = x
bool-or true-c _  = true-c

bool-and : bool-t -> bool-t -> bool-t
bool-and true-c x = x
bool-and false-c _  = false-c

if : {n : _} {A : Set n} -> bool-t -> A -> A -> A
if true-c x y = x
if false-c x y = y

-- nat --

data nat-t : type-tt where
  zero-c : nat-t
  succ-c : nat-t -> nat-t

nat-add : nat-t -> nat-t -> nat-t
nat-add zero-c n = n
nat-add (succ-c m) n = (succ-c (nat-add m n))

nat-mul : nat-t -> nat-t -> nat-t
nat-mul zero-c n = zero-c
nat-mul (succ-c m) n = (nat-add n (nat-mul m n))

nat-lt-p : nat-t -> nat-t -> bool-t
nat-lt-p zero-c zero-c = false-c
nat-lt-p zero-c (succ-c _) = true-c
nat-lt-p (succ-c _) zero-c = false-c
nat-lt-p (succ-c m) (succ-c n) = nat-lt-p m n

nat-eq-p : nat-t -> nat-t -> bool-t
nat-eq-p zero-c zero-c = true-c
nat-eq-p zero-c (succ-c _) = false-c
nat-eq-p (succ-c _) zero-c = false-c
nat-eq-p (succ-c m) (succ-c n) = nat-eq-p m n

nat-add-associate
  : (x y z : nat-t) ->
    (eqv-t
      (nat-add x (nat-add y z))
      (nat-add (nat-add x y) z))
nat-add-associate zero-c y z = eqv-c
nat-add-associate (succ-c x) y z =
  cong succ-c (nat-add-associate x y z)

-- nat-commute : (x y : nat-t) -> (eqv-t (add x y) (add y x))
-- nat-commute zero-c zero-c = eqv-c
-- nat-commute (succ-c x) zero-c = (cong succ-c (nat-commute x zero-c))
-- nat-commute zero-c y = {!!}
-- nat-commute (succ-c x) y = {!!}

-- list --

-- vect --

data vect-t (A : type-tt) : nat-t -> type-tt where
  null-vect-c : vect-t A zero-c
  cons-vect-c : {n : nat-t} -> A -> (vect-t A n) -> (vect-t A (succ-c n))
