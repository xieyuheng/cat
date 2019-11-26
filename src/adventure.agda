{-# OPTIONS --type-in-type #-}
{-# OPTIONS --prop #-}
{-# OPTIONS --allow-unsolved-metas #-}

module adventure where

open import basic
open eqv-reasoning

record adventure-t : type where
  infixl 2 _*_
  field
    jojo-t : type

    cut : jojo-t -> jojo-t
    _*_ : jojo-t -> jojo-t -> jojo-t

    mul-cut : (f g : jojo-t) ->
      eqv-t (cut (f * g)) ((cut f) * (cut g))
    mul-associative : (f g h : jojo-t) ->
      eqv-t (f * (g * h)) ((f * g) * h)

    id : jojo-t
    id-left : (f : jojo-t) ->
      eqv-t (id * f) f
    id-right : (f : jojo-t) ->
      eqv-t (f * id) f
    id-cut :
      eqv-t (cut id) id

    error : jojo-t
    error-left : (f : jojo-t) ->
      eqv-t (error * f) error
    error-right : (f : jojo-t) ->
      eqv-t (f * error) error
    error-cut :
      eqv-t (cut error) error

    quo : jojo-t -> jojo-t
    exe : jojo-t
    quo-exe : (x : jojo-t) ->
      eqv-t ((quo x) * exe) x
    quo-cut : (x : jojo-t) ->
      eqv-t (cut (quo x)) (quo (cut x))

    drop : jojo-t
    drop-quo : (x : jojo-t) ->
      eqv-t ((quo x) * drop) id

    dup : jojo-t
    dup-quo : (x : jojo-t) ->
      eqv-t ((quo x) * dup) ((quo x) * (quo x))

    swap : jojo-t
    swap-quo : (x y : jojo-t) ->
      eqv-t ((quo x) * (quo y) * swap) ((quo y) * (quo x))

    pair fst snd : jojo-t
    pair-fst : (x y : jojo-t) ->
      eqv-t (x * y * pair * fst) x
    pair-snd : (x y : jojo-t) ->
      eqv-t (x * y * pair * snd) y

    branch left right : jojo-t
    branch-left : (x y : jojo-t) ->
      eqv-t (left * x * y * branch) x
    branch-right : (x y : jojo-t) ->
      eqv-t (right * x * y * branch) y
