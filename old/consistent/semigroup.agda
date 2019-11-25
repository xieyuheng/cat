{-# OPTIONS --prop --allow-unsolved-metas #-}

module semigroup where

open import basic
open eqv-reasoning

record semigroup-t (lv : level-t)
  : type (lsucc lv) where
  field
    elem-t : type lv
    mul : elem-t -> elem-t -> elem-t
    mul-associative :
      (x y z : elem-t) ->
      the-eqv-t elem-t
        (mul x (mul y z))
        (mul (mul x y) z)
