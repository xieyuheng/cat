{-# OPTIONS --prop #-}

module groupoid where

open import basic
open import category
open category-t
open iso-t

-- NOTE
-- - The `groupoid-t` is defined by taken a category as an argument,
--   which might be better expressed by using inherence.
-- - Projection syntax is not scalable,
--   `(inv-iso f) .morphism` should be `inv-iso(f).morphism`.
--   `((f x) .m1 x1) .m2 x2` should be `f(x).m1(x1).m2(x2)`

record groupoid-t
  {lv : level-t}
  (cat : category-t lv)
  : type (lsucc lv) where
  field
    inv : {a b : cat .object-t} ->
      cat .morphism-t a b -> cat .morphism-t b a
    inv-iso : {a b : cat .object-t} ->
      cat .morphism-t a b -> iso-t cat a b
    inv-iso-eqv-morphism : {a b : cat .object-t} ->
      (f : cat .morphism-t a b) ->
      eqv-t ((inv-iso f) .morphism) f
    inv-iso-eqv-inverse : {a b : cat .object-t} ->
      (f : cat .morphism-t a b) ->
      eqv-t ((inv-iso f) .inverse) (inv f)

-- NOTE
-- the `iso-t cat a b f (inv f)` below
-- is where fulfilling type system is useful

-- record groupoid-t
--   {lv : level-t}
--   (cat : category-t lv)
--   : type (lsucc lv) where
--   field
--     inv : {a b : cat .object-t} ->
--       cat .morphism-t a b -> cat .morphism-t b a
--     inv-iso : {a b : cat .object-t} ->
--       (f : cat .morphism-t a b) -> iso-t cat a b f (inv f)
