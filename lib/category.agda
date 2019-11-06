open import pure

module category where

record category-t : type1 where
  field
    object-t : type
    morphism-t : object-t -> object-t -> type
    id : (a : object-t) -> morphism-t a a
    compose : {a b c : object-t} ->
      morphism-t a b -> morphism-t b c -> morphism-t a c
    left-id : {a b : object-t} ->
      (f : morphism-t a b) -> (eqv-t (compose (id a) f) f)
    right-id : {a b : object-t} ->
      (f : morphism-t a b) -> (eqv-t (compose f (id b)) f)
    associative : {a b c d : object-t} ->
      (f : morphism-t a b) ->
      (g : morphism-t b c) ->
      (h : morphism-t c d) ->
      (eqv-t (compose f (compose g h)) (compose (compose f g) h))

  record iso-t (a b : object-t) : type where
    field
      morphism : morphism-t a b
      inverse : morphism-t b a
      left-inverse : (eqv-t (compose morphism inverse) (id a))
      right-inverse : (eqv-t (compose inverse morphism) (id b))
