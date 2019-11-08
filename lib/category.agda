{-# OPTIONS --prop --safe #-}

module category where

open import pure
open import simple

-- NOTE
-- - Should `morphism-t` be at one level higher than `object-t`?
-- - Should we not use the general `the-eqv-t` but use `the-morphism-eqv-t`?
--   We will need equivalence relation to do this.
-- - How should we handle `homset`?
--   We will need `set-t` to do this.
-- We delay these decisions until we running into troubles.

record category-t {lv : level-t} : type (lsucc lv) where
  field
    object-t : type lv
    morphism-t : object-t -> object-t -> type lv
    id : (a : object-t) -> morphism-t a a
    compose : {a b c : object-t} ->
      morphism-t a b -> morphism-t b c -> morphism-t a c
    left-id : {a b : object-t} ->
      (f : morphism-t a b) ->
      (the-eqv-t (morphism-t a b)
        (compose (id a) f) f)
    right-id : {a b : object-t} ->
      (f : morphism-t a b) ->
      (the-eqv-t (morphism-t a b)
        (compose f (id b)) f)
    associative : {a b c d : object-t} ->
      (f : morphism-t a b) ->
      (g : morphism-t b c) ->
      (h : morphism-t c d) ->
      (the-eqv-t (morphism-t a d)
        (compose f (compose g h))
        (compose (compose f g) h))

  dom : {a b : object-t} -> (morphism-t a b) -> object-t
  dom {a} {b} f = a

  cod : {a b : object-t} -> (morphism-t a b) -> object-t
  cod {a} {b} f = b

  record iso-t (a b : object-t) : type lv where
    constructor iso-intro
    field
      morphism : morphism-t a b
      inverse : morphism-t b a
      left-inverse :
        (the-eqv-t (morphism-t a a)
          (compose morphism inverse)
          (id a))
      right-inverse :
        (the-eqv-t (morphism-t b b)
          (compose inverse morphism)
          (id b))
  open iso-t

  iso-t-eta : {x y : object-t} (i0 i1 : iso-t x y) ->
    the-eqv-t (morphism-t x y) (i0 .morphism) (i1 .morphism) ->
    the-eqv-t (morphism-t y x) (i0 .inverse) (i1 .inverse) ->
    the-eqv-t (iso-t x y) i0 i1
  iso-t-eta (iso-intro f g p0 q0) (iso-intro f g p1 q1) refl refl = refl

  record terminal-t : type lv where
    field
      object : object-t
      morphism : (x : object-t) -> (morphism-t x object)
      morphism-unique : {x : object-t}
        (f : morphism-t x object)
        (g : morphism-t x object) ->
        (the-eqv-t (morphism-t x object) f g)
  open terminal-t

  module _ (t0 t1 : terminal-t) where
    private
      x = t0 .object
      y = t1 .object
      f = t1 .morphism x
      g = t0 .morphism y
    terminal-iso : iso-t x y
    terminal-iso .morphism = f
    terminal-iso .inverse = g
    terminal-iso .left-inverse = t0 .morphism-unique (compose f g) (id x)
    terminal-iso .right-inverse = t1 .morphism-unique (compose g f) (id y)

  module _ (t0 t1 : terminal-t) where
    private
      x = t0 .object
      y = t1 .object
    module _ (i0 i1 : iso-t x y) where
      private
        f = i0 .morphism
        g = i1 .morphism
        f-inv = i0 .inverse
        g-inv = i1 .inverse
      terminal-iso-unique : the-eqv-t (iso-t x y) i0 i1
      terminal-iso-unique = iso-t-eta i0 i1 h1 h2 where
        h1 : the-eqv-t (morphism-t x y) f g
        h1 = t1 .morphism-unique f g
        h2 : the-eqv-t (morphism-t y x) f-inv g-inv
        h2 = t0 .morphism-unique f-inv g-inv

  -- TODO
  -- initial
  -- initial-iso
  -- initial-iso-unique

  opposite : category-t
  opposite .object-t = object-t
  opposite .morphism-t a b = morphism-t b a
  opposite .id = id
  opposite .compose f g = compose g f
  opposite .left-id = right-id
  opposite .right-id = left-id
  opposite .associative f g h = eqv-swap (associative h g f)

  record product-candidate-t (fst snd : object-t) : type lv where
    field
      object : object-t
      fst-proj : morphism-t object fst
      snd-proj : morphism-t object snd
  open product-candidate-t

  record product-t (fst snd : object-t) : type lv where
    field
      this : product-candidate-t fst snd
      factor : (cand : product-candidate-t fst snd) -> (morphism-t (cand .object) (this .object))
      factor-commute : {cand : product-candidate-t fst snd} ->
        (and-t
          (the-eqv-t (morphism-t (cand .object) fst)
            (compose (factor cand) (this .fst-proj))
            (cand .fst-proj))
          (the-eqv-t (morphism-t (cand .object) snd)
            (compose (factor cand) (this .snd-proj))
            (cand .snd-proj)))
      factor-unique : {cand : product-candidate-t fst snd} ->
        (f : morphism-t (cand .object) (this .object)) ->
        (g : morphism-t (cand .object) (this .object)) ->
        (eqv-t f g)

    -- object = this.object
    -- fst-proj = this.fst-proj
    -- snd-proj = this.snd-proj
  open product-t
