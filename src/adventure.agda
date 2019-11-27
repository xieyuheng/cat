{-# OPTIONS --type-in-type #-}
{-# OPTIONS --prop #-}
{-# OPTIONS --allow-unsolved-metas #-}

module adventure where

open import basic
open eqv-reasoning

record adventure-t : type where
  infixl 2 _*_
  field
    elem-t : type

    cut : elem-t -> elem-t
    _*_ : elem-t -> elem-t -> elem-t

    mul-cut : (f g : elem-t) ->
      eqv-t (cut (f * g)) ((cut f) * (cut g))
    mul-associative : (f g h : elem-t) ->
      eqv-t (f * (g * h)) ((f * g) * h)

    id : elem-t
    id-left : (f : elem-t) ->
      eqv-t (id * f) f
    id-right : (f : elem-t) ->
      eqv-t (f * id) f
    id-cut :
      eqv-t (cut id) id

    error : elem-t
    error-left : (f : elem-t) ->
      eqv-t (error * f) error
    error-right : (f : elem-t) ->
      eqv-t (f * error) error
    error-cut :
      eqv-t (cut error) error
