module category where

open import pure
open import simple

private
  variable
    l : Level

record category-t l : type (lsuc l) where
  inductive
  infixl 6 _∙_
  field
    object-t : type l
    morphism-t : object-t -> object-t -> type l
    id : (a : object-t) -> morphism-t a a
    _∙_ : {a b c : object-t} ->
      morphism-t a b -> morphism-t b c -> morphism-t a c
    left-id : {a b : object-t} ->
      (f : morphism-t a b) ->
      (eqv-t {A = morphism-t a b}
        (id a ∙ f) f)
    right-id : {a b : object-t} ->
      (f : morphism-t a b) ->
      (eqv-t {A = morphism-t a b}
        (f ∙ id b) f)
    associative : {a b c d : object-t} ->
      (f : morphism-t a b) ->
      (g : morphism-t b c) ->
      (h : morphism-t c d) ->
      (eqv-t {A = morphism-t a d}
        (f ∙ (g ∙ h))
        ((f ∙ g) ∙ h))

  record iso-t (a b : object-t) : type l where
    field
      morphism : morphism-t a b
      inverse : morphism-t b a
      left-inverse :
        (eqv-t {A = morphism-t a a}
          (morphism ∙ inverse)
          (id a))
      right-inverse :
        (eqv-t {A = morphism-t b b}
          (inverse ∙ morphism)
          (id b))

  record terminal-t : type l where
    field
      object : object-t
      morphism : (x : object-t) -> (morphism-t x object)
      morphism-unique : {x : object-t}
        (f : (morphism-t x object))
        (g : (morphism-t x object)) ->
        (eqv-t {A = morphism-t x object} f g)


--   terminal-iso : (t0 t1 : terminal-t) -> (iso-t (terminal-t.object t0) (terminal-t.object t1))
--   terminal-iso t0 t1 =
--     let
--       x : object-t
--       x = terminal-t.object t0
--       y : object-t
--       y = terminal-t.object t1
--       f : morphism-t x y
--       f = terminal-t.morphism t1 x
--       g : morphism-t y x
--       g = terminal-t.morphism t0 y
--     in record
--       { morphism = f
--       ; inverse = g
--       ; left-inverse = terminal-t.morphism-unique t0 (compose f g) (id x)
--       ; right-inverse = terminal-t.morphism-unique t1 (compose g f) (id y)
--       }

  module _ (t0 t1 : terminal-t) where
    private
      open iso-t
      open terminal-t
      x = t0 .object
      y = t1 .object
      f = t1 .morphism x
      g = t0 .morphism y

    terminal-iso : iso-t x y
    terminal-iso .morphism = f
    terminal-iso .inverse = g
    terminal-iso .left-inverse = t0 .morphism-unique (f ∙ g) (x .id)
    terminal-iso .right-inverse = t1 .morphism-unique (g ∙ f) (y .id)
