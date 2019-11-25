{-# OPTIONS --type-in-type #-}
{-# OPTIONS --prop #-}

module basic where

open import Agda.Primitive public

-- type

type : Set
type = Set

-- prop

prop : type
prop = Prop

data and-t (A B : prop) : prop where
  and : (a : A) -> (b : B) -> and-t A B

and-fst : {A B : prop} ->
  and-t A B -> A
and-fst (and a b) = a

and-snd : {A B : prop} ->
  and-t A B -> B
and-snd (and a b) = b

data prop-sigma-t (A : type) (D : A -> prop) : prop where
  sigma : (a : A) -> D a -> prop-sigma-t A D

-- the

the : (A : prop) -> (p : A) -> A
the A p = p

-- eqv

data eqv-t {A : type} (p : A) : A -> prop where
  refl : eqv-t p p

{-# BUILTIN EQUALITY eqv-t #-}

the-eqv-t : (A : type) (p : A) -> A -> prop
the-eqv-t A = eqv-t

the-same : (A : type) (p : A) -> eqv-t p p
the-same A p = refl

same : {A : type} (p : A) -> eqv-t p p
same p = refl

eqv-apply :
  {A B : type} {x y : A} ->
  (f : A -> B) -> eqv-t x y -> eqv-t (f x) (f y)
eqv-apply f refl = refl

eqv-compose :
  {A : type} {x y z : A} ->
  eqv-t x y -> eqv-t y z -> eqv-t x z
eqv-compose refl refl = refl

eqv-swap :
  {A : type} {x y : A} ->
  eqv-t x y -> eqv-t y x
eqv-swap refl = refl

eqv-replace :
  {A : type} {x y : A} ->
  (equation : eqv-t x y) ->
  (motive : A -> prop) ->
  motive x ->
  motive y
eqv-replace refl motive base = base

-- sigma

data sigma-t (A : type) (D : A -> type) : type where
  sigma : (a : A) -> D a -> sigma-t A D

sigma-fst : {A : type} {D : A -> type} ->
  sigma-t A D -> A
sigma-fst (sigma a b) = a

sigma-snd : {A : type} {D : A -> type} ->
  (si : sigma-t A D) -> D (sigma-fst si)
sigma-snd (sigma a b) = b

-- pi

data pi-t (A : type) (D : A -> type) : type where
  pi : ((a : A) -> D a) -> pi-t A D

-- eqv-reasoning

module eqv-reasoning {A : type} where

  infix  1 eqv-begin_
  infixr 2 _=[]_
  infixr 2 _=[_]_
  infixr 2 _eqv-step-to_
  infixr 2 _eqv-step_to_
  infix  3 _eqv-end

  eqv-begin_ : {x y : A}
    -> eqv-t x y
    -> eqv-t x y
  eqv-begin eqv-x-y = eqv-x-y

  _=[]_ : (x : A) {y : A}
    -> eqv-t x y
    -> eqv-t x y
  x =[] eqv-x-y = eqv-x-y

  _=[_]_ : (x : A) {y z : A}
    -> eqv-t x y
    -> eqv-t y z
    -> eqv-t x z
  x =[ eqv-x-y ] eqv-y-z = eqv-compose eqv-x-y eqv-y-z

  _eqv-step-to_ : (x : A) {y : A}
    -> eqv-t x y
    -> eqv-t x y
  x eqv-step-to eqv-x-y = eqv-x-y

  _eqv-step_to_ : (x : A) {y z : A}
    -> eqv-t x y
    -> eqv-t y z
    -> eqv-t x z
  x eqv-step eqv-x-y to eqv-y-z = eqv-compose eqv-x-y eqv-y-z

  _eqv-end : (x : A) -> eqv-t x x
  x eqv-end = refl

-- string

open import Agda.Builtin.String

string-t : type
string-t = String

-- unit

data unit-t : type where
  unit : unit-t

-- bool

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

bool-if : {A : type} -> bool-t -> A -> A -> A
bool-if true x y = x
bool-if false x y = y

-- nat

data nat-t : type where
  zero : nat-t
  succ : nat-t -> nat-t

nat-add : nat-t -> nat-t -> nat-t
nat-add zero y = y
nat-add (succ x) y = succ (nat-add x y)

nat-mul : nat-t -> nat-t -> nat-t
nat-mul zero y = zero
nat-mul (succ x) y = nat-add y (nat-mul x y)

nat-add-associate :
  (x y z : nat-t) ->
  eqv-t
    (nat-add x (nat-add y z))
    (nat-add (nat-add x y) z)
nat-add-associate zero y z = refl
nat-add-associate (succ x) y z =
  eqv-apply succ (nat-add-associate x y z)

nat-add-zero-commute :
  (x : nat-t) ->
  eqv-t
    (nat-add zero x)
    (nat-add x zero)
nat-add-zero-commute zero = refl
nat-add-zero-commute (succ x) =
  eqv-apply succ (nat-add-zero-commute x)

nat-add-succ-commute-1 :
  (x y : nat-t) ->
  eqv-t
    (nat-add (succ x) y)
    (succ (nat-add x y))
nat-add-succ-commute-1 zero y = refl
nat-add-succ-commute-1 (succ x) y =
  eqv-apply succ (nat-add-succ-commute-1 x y)

nat-add-succ-commute-2 :
  (x y : nat-t) ->
  eqv-t
    (nat-add x (succ y))
    (succ (nat-add x y))
nat-add-succ-commute-2 zero y = refl
nat-add-succ-commute-2 (succ x) y =
  eqv-apply succ (nat-add-succ-commute-2 x y)

nat-add-commute :
  (x y : nat-t) ->
  eqv-t
    (nat-add x y)
    (nat-add y x)
nat-add-commute zero y =
  nat-add-zero-commute y
nat-add-commute (succ x) y =
  eqv-compose
    (eqv-apply succ (nat-add-commute x y))
    (eqv-swap (nat-add-succ-commute-2 y x))

-- list

data list-t (A : type) : type where
  null-list : list-t A
  cons-list :  A -> (list-t A) -> (list-t A)

-- vec

data vec-t (A : type) : nat-t -> type where
  null-vec : vec-t A zero
  cons-vec : {n : nat-t} ->
    A -> (vec-t A n) -> (vec-t A (succ n))
