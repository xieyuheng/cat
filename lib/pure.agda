module pure where

open import Agda.Primitive

-- type --

type = Set
type1 = Set1

-- eqv --

data eqv-t {A : type} (q : A) : A -> type where
  eqv : (eqv-t q q)

{-# BUILTIN EQUALITY eqv-t #-}

eqv-apply : forall {A B} {x y}
  (f : A -> B) -> (eqv-t x y) -> (eqv-t (f x) (f y))
eqv-apply f eqv = eqv

eqv-compose :
  {A : type} ->
  {x y z : A} ->
  (eqv-t x y) -> (eqv-t y z) -> (eqv-t x z)
eqv-compose eqv eqv = eqv

eqv-swap :
  {A : type} ->
  {x y : A} ->
  (eqv-t x y) -> (eqv-t y x)
eqv-swap eqv = eqv
