module pure where

open import Agda.Primitive public

-- type --

type : forall l -> Set (lsuc l)
type l = Set l
type0 = Set
type1 = type lzero

private
  variable
    l : Level
    A B : type l

-- eqv --

data eqv-t {A : type l} (q : A) : A -> type l where
  eqv : (eqv-t q q)

{-# BUILTIN EQUALITY eqv-t #-}

eqv-apply : forall {x y}
  (f : A -> B) -> (eqv-t x y) -> (eqv-t (f x) (f y))
eqv-apply f eqv = eqv

eqv-compose :
  {x y z : A} ->
  (eqv-t x y) -> (eqv-t y z) -> (eqv-t x z)
eqv-compose eqv eqv = eqv

eqv-swap :
  {x y : A} ->
  (eqv-t x y) -> (eqv-t y x)
eqv-swap eqv = eqv
