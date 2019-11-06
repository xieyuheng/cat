open import pure

-- bool --

data bool-t : type-t where
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

data nat-t : type-t where
  zero-c : nat-t
  succ-c : nat-t -> nat-t

nat-add : nat-t -> nat-t -> nat-t
nat-add zero-c y = y
nat-add (succ-c x) y = succ-c (nat-add x y)

nat-mul : nat-t -> nat-t -> nat-t
nat-mul zero-c y = zero-c
nat-mul (succ-c x) y = nat-add y (nat-mul x y)

nat-lt-p : nat-t -> nat-t -> bool-t
nat-lt-p zero-c zero-c = false-c
nat-lt-p zero-c (succ-c _) = true-c
nat-lt-p (succ-c _) zero-c = false-c
nat-lt-p (succ-c x) (succ-c y) = nat-lt-p x y

nat-eq-p : nat-t -> nat-t -> bool-t
nat-eq-p zero-c zero-c = true-c
nat-eq-p zero-c (succ-c _) = false-c
nat-eq-p (succ-c _) zero-c = false-c
nat-eq-p (succ-c x) (succ-c y) = nat-eq-p x y

nat-add-associate :
  (x y z : nat-t) ->
  (eqv-t
    (nat-add x (nat-add y z))
    (nat-add (nat-add x y) z))
nat-add-associate zero-c y z = eqv-c
nat-add-associate (succ-c x) y z =
  eqv-apply succ-c (nat-add-associate x y z)

nat-add-zero-commute :
  (x : nat-t) ->
  (eqv-t
    (nat-add zero-c x)
    (nat-add x zero-c))
nat-add-zero-commute zero-c = eqv-c
nat-add-zero-commute (succ-c x) =
  eqv-apply succ-c (nat-add-zero-commute x)

nat-add-succ-commute-1 :
  (x y : nat-t) ->
  (eqv-t
    (nat-add (succ-c x) y)
    (succ-c (nat-add x y)))
nat-add-succ-commute-1 zero-c y = eqv-c
nat-add-succ-commute-1 (succ-c x) y =
  eqv-apply succ-c (nat-add-succ-commute-1 x y)

nat-add-succ-commute-2 :
  (x y : nat-t) ->
  (eqv-t
    (nat-add x (succ-c y))
    (succ-c (nat-add x y)))
nat-add-succ-commute-2 zero-c y = eqv-c
nat-add-succ-commute-2 (succ-c x) y =
  eqv-apply succ-c (nat-add-succ-commute-2 x y)

nat-add-commute :
  (x y : nat-t) ->
  (eqv-t
    (nat-add x y)
    (nat-add y x))
nat-add-commute zero-c y =
  nat-add-zero-commute y
nat-add-commute (succ-c x) y =
  eqv-compose
    (eqv-apply succ-c (nat-add-commute x y))
    (eqv-swap (nat-add-succ-commute-2 y x))

-- list --

-- vect --

data vect-t (A : type-t) : nat-t -> type-t where
  null-vect-c :
    vect-t A zero-c
  cons-vect-c :
    {n : nat-t} -> A -> (vect-t A n) -> (vect-t A (succ-c n))
