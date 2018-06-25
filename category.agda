open import pure

module category where

record category-ct : type-t1 where
  field
    object-t
      : type-tt
    arrow-t
      : object-t -> object-t -> type-tt
    arrow-eqv-t
      : {a b : object-t} ->
        arrow-t a b ->
        arrow-t a b -> type-tt
    identity
      : (a : object-t) -> arrow-t a a
    compose
      : {a b c : object-t} ->
        arrow-t a b ->
        arrow-t b c ->
        arrow-t a c
    identity-left
      : {a b : object-t} ->
        (f : arrow-t a b) ->
        (arrow-eqv-t (compose (identity a) f) f)
    identity-right
      : {a b : object-t} ->
        (f : arrow-t a b) ->
        (arrow-eqv-t (compose f (identity b)) f)
    compose-associative
      : {a b c d : object-t} ->
        (f : arrow-t a b) ->
        (g : arrow-t b c) ->
        (h : arrow-t c d) ->
        (arrow-eqv-t (compose f (compose g h)) (compose (compose f g) h))
