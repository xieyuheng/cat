{-# OPTIONS --prop --allow-unsolved-metas #-}

module group where

open import basic
open eqv-reasoning

open import category
open category-t

record group-t (lv : level-t)
  : type (lsucc lv) where
  field
    elem-t : type lv
    mul : elem-t -> elem-t -> elem-t
    mul-associative :
      (x y z : elem-t) ->
      the-eqv-t elem-t
        (mul x (mul y z))
        (mul (mul x y) z)

    id : elem-t
    id-left : (x : elem-t) -> the-eqv-t elem-t (mul id x) x
    id-right : (x : elem-t) -> the-eqv-t elem-t (mul x id) x

    inv : (x : elem-t) -> elem-t
    left-inv : (x : elem-t) -> the-eqv-t elem-t (mul (inv x) x) id
    right-inv : (x : elem-t) -> the-eqv-t elem-t (mul x (inv x)) id

  div : elem-t -> elem-t -> elem-t
  div x y = mul x (inv y)

group-category : {lv : level-t} -> category-t lv
group-category = {!!}
