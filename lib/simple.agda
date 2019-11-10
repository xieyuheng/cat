{-# OPTIONS --prop #-}

module simple where

open import pure

-- bool

data bool-t : type0 where
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

-- nat

data nat-t : type0 where
  zero : nat-t
  succ : nat-t -> nat-t

nat-add : nat-t -> nat-t -> nat-t
nat-add zero y = y
nat-add (succ x) y = succ (nat-add x y)

nat-mul : nat-t -> nat-t -> nat-t
nat-mul zero y = zero
nat-mul (succ x) y = nat-add y (nat-mul x y)

data bot : type0 where

bot-elim : bot ->
  {lv2 : level-t} -> {whatever : type lv2} -> whatever
bot-elim ()

negate : {lv : level-t} -> prop lv -> type lv
negate a = a -> bot

data dec {lv : level-t} (A : prop lv) : type lv where
  yes : A -> dec A
  no  : negate A -> dec A

nat-eq-inj : (a b : nat-t) -> eqv-t (succ a) (succ b) -> eqv-t a b
nat-eq-inj a b refl = refl

nat-eq-p : (a b : nat-t) -> dec (eqv-t a b)
nat-eq-p zero zero = yes refl
nat-eq-p zero (succ _) = no \ ()
nat-eq-p (succ _) zero = no \ ()
nat-eq-p (succ x) (succ y) with nat-eq-p x y
... | yes p = yes (eqv-apply succ p)
... | no  p = no \ q -> p (nat-eq-inj x y q)

data nat-lt : (a b : nat-t) -> prop0 where
  zero-lt-n    : {n : nat-t} -> nat-lt zero n
  succ-lt-succ : {m n : nat-t} -> (p : nat-lt m n) -> nat-lt (succ m) (succ n)

nat-lt-inj : (a b : nat-t) -> nat-lt (succ a) (succ b) -> nat-lt a b
nat-lt-inj a b (succ-lt-succ p) = p

nat-lt-p : (a b : nat-t) -> dec (nat-lt a b)
nat-lt-p zero zero = yes zero-lt-n
nat-lt-p zero (succ _) = yes zero-lt-n
nat-lt-p (succ _) zero = no \ ()
nat-lt-p (succ x) (succ y) with nat-lt-p x y
... | yes p = yes (succ-lt-succ p)
... | no  p = no \ q -> p (nat-lt-inj x y q)

nat-add-associate :
  (x y z : nat-t) ->
  (eqv-t
    (nat-add x (nat-add y z))
    (nat-add (nat-add x y) z))
nat-add-associate zero y z = refl
nat-add-associate (succ x) y z =
  eqv-apply succ (nat-add-associate x y z)

nat-add-zero-commute :
  (x : nat-t) ->
  (eqv-t
    (nat-add zero x)
    (nat-add x zero))
nat-add-zero-commute zero = refl
nat-add-zero-commute (succ x) =
  eqv-apply succ (nat-add-zero-commute x)

nat-add-succ-commute-1 :
  (x y : nat-t) ->
  (eqv-t
    (nat-add (succ x) y)
    (succ (nat-add x y)))
nat-add-succ-commute-1 zero y = refl
nat-add-succ-commute-1 (succ x) y =
  eqv-apply succ (nat-add-succ-commute-1 x y)

nat-add-succ-commute-2 :
  (x y : nat-t) ->
  (eqv-t
    (nat-add x (succ y))
    (succ (nat-add x y)))
nat-add-succ-commute-2 zero y = refl
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

-- list

data list-t {lv : level-t} (A : type lv) : type lv where
  null-list : list-t A
  cons-list :  A -> (list-t A) -> (list-t A)

-- vec

data vec-t {lv : level-t} (A : type lv) : nat-t -> type lv where
  null-vec : vec-t A zero
  cons-vec : {n : nat-t} ->
    A -> (vec-t A n) -> (vec-t A (succ n))
