{-# OPTIONS --prop --safe #-}

module pure where

open import Agda.Primitive public

-- level

level-t : Set
level-t = Level

lsucc : level-t -> level-t
lsucc = lsuc

prop : (lv : level-t) -> Set (lsucc lv)
prop lv = Prop lv

type : (lv : level-t) -> Set (lsucc lv)
type lv = Set lv

lone : level-t
lone = lsucc lzero

ltwo : level-t
ltwo = lsucc lone

type0 : type lone
type0 = type lzero

type1 : type ltwo
type1 = type lone

prop0 : type lone
prop0 = prop lzero

prop1 : type ltwo
prop1 = prop lone

-- the

the : {lv : level-t} (A : type lv) -> (p : A) -> A
the A p = p

-- eqv

data eqv-t {lv : level-t} {A : type lv} (p : A) : A -> prop lv where
  refl : eqv-t p p

{-# BUILTIN EQUALITY eqv-t #-}

the-eqv-t : {lv : level-t} (A : type lv) (p : A) -> A -> prop lv
the-eqv-t A = eqv-t

the-same : {lv : level-t} (A : type lv) (p : A) -> eqv-t p p
the-same A p = refl

same : {lv : level-t} {A : type lv} (p : A) -> eqv-t p p
same p = refl

eqv-apply :
  {lv : level-t}
  {A B : type lv} {x y : A} ->
  (f : A -> B) -> (eqv-t x y) -> (eqv-t (f x) (f y))
eqv-apply f refl = refl

eqv-compose :
  {lv : level-t}
  {A : type lv} {x y z : A} ->
  (eqv-t x y) -> (eqv-t y z) -> (eqv-t x z)
eqv-compose refl refl = refl

eqv-swap :
  {lv : level-t}
  {A : type lv} {x y : A} ->
  (eqv-t x y) -> (eqv-t y x)
eqv-swap refl = refl
