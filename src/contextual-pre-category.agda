{-# OPTIONS --type-in-type #-}
{-# OPTIONS --prop #-}
{-# OPTIONS --allow-unsolved-metas #-}

module contextual-pre-category where

open import basic
open eqv-reasoning

record contextual-pre-category-t : type where
  field
    object-t : type
    morphism-t : object-t -> object-t -> type
    id : (a : object-t) -> morphism-t a a
    compose : {a b c : object-t} ->
      morphism-t a b ->
      morphism-t b c ->
      morphism-t a c
    id-left : {a b : object-t} ->
      (f : morphism-t a b) ->
      the-eqv-t (morphism-t a b)
        (compose (id a) f) f
    id-right : {a b : object-t} ->
      (f : morphism-t a b) ->
      the-eqv-t (morphism-t a b)
        (compose f (id b)) f
    compose-associative : {a b c d : object-t} ->
      (f : morphism-t a b) ->
      (g : morphism-t b c) ->
      (h : morphism-t c d) ->
      the-eqv-t (morphism-t a d)
        (compose f (compose g h))
        (compose (compose f g) h)

    length : object-t -> nat-t
    point : object-t
    father : object-t -> object-t
    previous : (x : object-t) -> morphism-t x (father x)

    lift-object :
      (x : object-t) ->
      -- TODO x != point
      {y : object-t} ->
      (f : morphism-t y (father x)) ->
      object-t

    lift-morphism :
      (x : object-t) ->
      {y : object-t} ->
      (f : morphism-t y (father x)) ->
      morphism-t (lift-object x f) x

    point-length-zero :
      eqv-t (length point) zero
      -- TODO point is the only zero-length object

    father-length :
      (x : object-t) ->
      -- TODO x != point
      eqv-t (length x) (succ (length (father x)))
      -- TODO instead of x != point
      -- we can also use
      -- eqv-t (length (father x)) (desc (length x))
      -- where (desc zero) == zero

    point-father :
      eqv-t (father point) point

    -- TODO point is terminal object

    lift-father :
      (x : object-t) ->
      -- TODO x != point
      {y : object-t} ->
      (f : morphism-t y (father x)) ->
      eqv-t (father (lift-object x f)) y

    -- TODO how to do this concretely ?
    compose-with-boundary-eqv : {a b1 b2 c : object-t} ->
      eqv-t b1 b2 ->
      morphism-t a b1 ->
      morphism-t b2 c ->
      morphism-t a c

    lift-father-pullback :
      (x : object-t) ->
      -- TODO x != point
      {y : object-t} ->
      (f : morphism-t y (father x)) ->
      {z : object-t} ->
      the-eqv-t (morphism-t (lift-object x f) (father x))
        (compose (lift-morphism x f) (previous x))
        (compose-with-boundary-eqv (lift-father x f)
          (previous (lift-object x f)) f)

    -- TODO
    lift-object-id :
      (x : object-t) ->
      -- TODO x != point
      eqv-t (lift-object x (id (father x))) x

    -- lift-morphism-id :
    --   (x : object-t) ->
    --   -- TODO x != point
    --   the-eqv-t (morphism-t (lift-object x (id (father x))) x)
    --     (lift-morphism x (id (father x)))
    --     -- TODO how to use (lift-object-id x) ?
    --     (id x)

    -- TODO
    -- lift-object-compose

    -- TODO
    -- lift-morphism-compose

    -- TODO
    -- object-set-of-length : nat-t -> (set-t object-t)

    -- TODO
    -- object-set-of-father : (x : object-t) -> (set-t object-t)
    -- where { y in the set, eqv-t (father y) x }

    -- TODO
    -- another function defined by object-set-of-length
