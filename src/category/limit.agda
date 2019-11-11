{-# OPTIONS --prop #-}

module category.limit where

open import basic

open import category
open category-t

open import category.functor
open functor-t

record cone-t
  {lv : level-t}
  {shape cat : category-t lv}
  (diagram : functor-t shape cat)
  (apex : cat .object-t)
  : type (lsucc lv) where
  field
    line :
      (index : shape .object-t) ->
      cat .morphism-t apex (diagram .map index)

record limit-t
  {lv : level-t}
  (shape cat : category-t lv)
  : type (lsucc lv) where
  field
    object : cat .object-t
    diagram : functor-t shape cat
    cone : cone-t diagram object
    -- universal :
