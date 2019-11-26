{-# OPTIONS --type-in-type #-}
{-# OPTIONS --prop #-}
{-# OPTIONS --allow-unsolved-metas #-}

module adventure where

open import basic
open eqv-reasoning

record adventure-t : type where
  field
    jojo-t : type

    cut : jojo-t -> jojo-t
    mul : jojo-t -> jojo-t -> jojo-t

    cut-respect-mul : (f g : jojo-t) ->
      eqv-t (cut (mul f g)) (mul (cut f) (cut g))
    mul-associative : (f g h : jojo-t) ->
      eqv-t (mul f (mul g h)) (mul (mul f g) h)

    id : jojo-t

    id-left : (f : jojo-t) ->
      eqv-t f (mul id f)
    id-right : (f : jojo-t) ->
      eqv-t f (mul f id)

    id-cut-idempotent : eqv-t (cut id) id

    error : jojo-t

    error-left : (f : jojo-t) ->
      eqv-t error (mul error f)
    error-right : (f : jojo-t) ->
      eqv-t error (mul f error)

    error-cut-idempotent : eqv-t (cut error) error
