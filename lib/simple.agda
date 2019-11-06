module simple where

open import pure

-- bool --

data bool-t : type where
  true : bool-t
  false : bool-t

bool-not : bool-t -> bool-t
bool-not true = false
bool-not false = true

bool-or : bool-t -> bool-t -> bool-t
bool-or false x = x
bool-or true _  = true

bool-and : bool-t -> bool-t -> bool-t
bool-and true x = x
bool-and false _  = false

if : {n : _} {A : Set n} -> bool-t -> A -> A -> A
if true x y = x
if false x y = y

-- nat --

data nat-t : type where
  zero : nat-t
  succ : nat-t -> nat-t

nat-add : nat-t -> nat-t -> nat-t
nat-add zero y = y
nat-add (succ x) y = succ (nat-add x y)

nat-mul : nat-t -> nat-t -> nat-t
nat-mul zero y = zero
nat-mul (succ x) y = nat-add y (nat-mul x y)

nat-lt-p : nat-t -> nat-t -> bool-t
nat-lt-p zero zero = false
nat-lt-p zero (succ _) = true
nat-lt-p (succ _) zero = false
nat-lt-p (succ x) (succ y) = nat-lt-p x y

nat-eq-p : nat-t -> nat-t -> bool-t
nat-eq-p zero zero = true
nat-eq-p zero (succ _) = false
nat-eq-p (succ _) zero = false
nat-eq-p (succ x) (succ y) = nat-eq-p x y

nat-add-associate :
  (x y z : nat-t) ->
  (eqv-t
    (nat-add x (nat-add y z))
    (nat-add (nat-add x y) z))
nat-add-associate zero y z = eqv
nat-add-associate (succ x) y z =
  eqv-apply succ (nat-add-associate x y z)

nat-add-zero-commute :
  (x : nat-t) ->
  (eqv-t
    (nat-add zero x)
    (nat-add x zero))
nat-add-zero-commute zero = eqv
nat-add-zero-commute (succ x) =
  eqv-apply succ (nat-add-zero-commute x)

nat-add-succ-commute-1 :
  (x y : nat-t) ->
  (eqv-t
    (nat-add (succ x) y)
    (succ (nat-add x y)))
nat-add-succ-commute-1 zero y = eqv
nat-add-succ-commute-1 (succ x) y =
  eqv-apply succ (nat-add-succ-commute-1 x y)

nat-add-succ-commute-2 :
  (x y : nat-t) ->
  (eqv-t
    (nat-add x (succ y))
    (succ (nat-add x y)))
nat-add-succ-commute-2 zero y = eqv
nat-add-succ-commute-2 (succ x) y =
  eqv-apply succ (nat-add-succ-commute-2 x y)

nat-add-commute :
  (x y : nat-t) ->
  (eqv-t
    (nat-add x y)
    (nat-add y x))
nat-add-commute zero y =
  nat-add-zero-commute y
nat-add-commute (succ x) y =
  eqv-compose
    (eqv-apply succ (nat-add-commute x y))
    (eqv-swap (nat-add-succ-commute-2 y x))

-- list --

-- vec --

data vec-t (A : type) : nat-t -> type where
  null-vec : vec-t A zero
  cons-vec : {n : nat-t} ->
    A -> (vec-t A n) -> (vec-t A (succ n))
