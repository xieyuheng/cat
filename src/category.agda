{-# OPTIONS --prop --allow-unsolved-metas #-}

module category where

open import basic
open eqv-reasoning

-- NOTE
-- - Should `morphism-t` be at one level higher than `object-t`?
-- - Should we not use the general `the-eqv-t` but use `the-morphism-eqv-t`?
--   We will need equivalence relation to do this.
-- - How should we handle `homset`?
--   We will need `set-t` to do this.
-- - By `object-t : type lv` our model of category theory is limited to small categories,
--   where objects form a set.
-- We delay these decisions until we running into troubles.

record category-t (lv : level-t)
  : type (lsucc lv) where
  field
    object-t : type lv
    morphism-t : object-t -> object-t -> type lv
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

  morphism-dom : {a b : object-t} -> morphism-t a b -> object-t
  morphism-dom {a} {b} f = a

  morphism-cod : {a b : object-t} -> morphism-t a b -> object-t
  morphism-cod {a} {b} f = b

  record iso-t (a b : object-t) : type lv where
    constructor iso-intro
    field
      morphism : morphism-t a b
      inverse : morphism-t b a
      inverse-left :
        the-eqv-t (morphism-t a a)
          (compose morphism inverse)
          (id a)
      inverse-right :
        the-eqv-t (morphism-t b b)
          (compose inverse morphism)
          (id b)
  open iso-t

  iso-eta : {x y : object-t} (i0 i1 : iso-t x y) ->
    the-eqv-t (morphism-t x y) (i0 .morphism) (i1 .morphism) ->
    the-eqv-t (morphism-t y x) (i0 .inverse) (i1 .inverse) ->
    the-eqv-t (iso-t x y) i0 i1
  iso-eta (iso-intro f g p0 q0) (iso-intro f g p1 q1) refl refl = refl

  record terminal-t : type lv where
    field
      object : object-t
      morphism : (x : object-t) -> morphism-t x object
      morphism-unique : {x : object-t}
        (f : morphism-t x object)
        (g : morphism-t x object) ->
        the-eqv-t (morphism-t x object) f g
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
    terminal-iso .inverse-left = t0 .morphism-unique (compose f g) (id x)
    terminal-iso .inverse-right = t1 .morphism-unique (compose g f) (id y)

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
      terminal-iso-unique = iso-eta i0 i1 h1 h2 where
        h1 : the-eqv-t (morphism-t x y) f g
        h1 = t1 .morphism-unique f g
        h2 : the-eqv-t (morphism-t y x) f-inv g-inv
        h2 = t0 .morphism-unique f-inv g-inv

  -- NOTE
  -- If we have fulfilling type system,
  --   the above used of `module _` can be avoid.
  -- terminal-iso-unique :
  --   {x y : object-t}
  --   (t0 : terminal-t x) ->
  --   (t1 : terminal-t y) ->
  --   (i0 i1 : iso-t x y) ->
  --   the-eqv-t (iso-t x y) i0 i1



  -- TODO
  -- initial-t

  opposite : category-t lv
  opposite .object-t = object-t
  opposite .morphism-t a b = morphism-t b a
  opposite .id = id
  opposite .compose f g = compose g f
  opposite .id-left = id-right
  opposite .id-right = id-left
  opposite .compose-associative f g h =
    eqv-swap (compose-associative h g f)

  record product-candidate-t (fst snd : object-t) : type lv where
    field
      object : object-t
      fst-proj : morphism-t object fst
      snd-proj : morphism-t object snd
  open product-candidate-t

  -- TODO
  -- maybe product-commute-t

  record product-t (fst snd : object-t) : type lv where
    field
      this : product-candidate-t fst snd
      factorize :
        (cand : product-candidate-t fst snd) ->
        morphism-t (cand .object) (this .object)
      factorize-commute :
        (cand : product-candidate-t fst snd) ->
        and-t
          (eqv-t (compose (factorize cand) (this .fst-proj)) (cand .fst-proj))
          (eqv-t (compose (factorize cand) (this .snd-proj)) (cand .snd-proj))
      factor-unique :
        (cand : product-candidate-t fst snd) ->
        (f : morphism-t (cand .object) (this .object)) ->
        eqv-t (compose f (this .fst-proj)) (cand .fst-proj) ->
        eqv-t (compose f (this .snd-proj)) (cand .snd-proj) ->
        (g : morphism-t (cand .object) (this .object)) ->
        eqv-t (compose g (this .fst-proj)) (cand .fst-proj) ->
        eqv-t (compose g (this .snd-proj)) (cand .snd-proj) ->
        eqv-t f g
  open product-t

  module _ {fst snd : object-t} (p0 p1 : product-t fst snd) where
    private
      x = p0 .this .object
      y = p1 .this .object
      f = p1 .factorize (p0 .this)
      g = p0 .factorize (p1 .this)
    product-iso : iso-t x y
    product-iso .morphism = f
    product-iso .inverse = g
    product-iso .inverse-left =
      p0 .factor-unique
        (p0 .this)
        (compose f g) eqv-f-g-fst eqv-f-g-snd
        (id x) (id-left (p0 .this .fst-proj)) (id-left (p0 .this .snd-proj))
      where
        eqv-f-g-fst : eqv-t (compose (compose f g) (p0 .this .fst-proj)) (p0 .this .fst-proj)
        eqv-f-g-fst =
          eqv-begin
            compose (compose f g) (p0 .this .fst-proj)
          =[ eqv-swap (compose-associative f g (p0 .this .fst-proj)) ]
            compose f (compose g (p0 .this .fst-proj))
          =[ eqv-apply (compose f) (and-fst (p0 .factorize-commute (p1 .this))) ]
            compose f (p1 .this .fst-proj)
          =[ and-fst (p1 .factorize-commute (p0 .this)) ]
            p0 .this .fst-proj
          eqv-end
        eqv-f-g-snd : eqv-t (compose (compose f g) (p0 .this .snd-proj)) (p0 .this .snd-proj)
        eqv-f-g-snd =
          eqv-begin
            compose (compose f g) (p0 .this .snd-proj)
          =[ eqv-swap (compose-associative f g (p0 .this .snd-proj)) ]
            compose f (compose g (p0 .this .snd-proj))
          =[ eqv-apply (compose f) (and-snd (p0 .factorize-commute (p1 .this))) ]
            compose f (p1 .this .snd-proj)
          =[ and-snd (p1 .factorize-commute (p0 .this)) ]
            p0 .this .snd-proj
          eqv-end
    product-iso .inverse-right = {!!}

  module _ {fst snd : object-t} (p0 p1 : product-t fst snd) where
    private
      x = p0 .this .object
      y = p1 .this .object
    module _ (i0 i1 : iso-t x y) where
      product-iso-unique : the-eqv-t (iso-t x y) i0 i1
      product-iso-unique = {!!}

  -- TODO
  -- sum-t

  -- pullback-t

  -- pushout-t

empty-category : {lv : level-t} -> category-t lv
empty-category = {!!}
