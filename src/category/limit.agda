{-# OPTIONS --prop #-}

module category.limit where

open import basic

open import category
open category-t

open import category.functor
open functor-t

record limit-t
  {lv : level-t}
  (shape cat : category-t lv)
  : type (lsucc lv) where
  field
    diagram : functor-t shape cat
