open import preface

module category
  (object : type-tt)
  (arrow : object -> object -> type-tt)
  (arrow-eq
    : {a b : object} ->
      arrow a b ->
      arrow a b -> type-tt)
  (identity : (a : object) -> arrow a a)
  (compose
    : {a b c : object} ->
      arrow a b ->
      arrow b c ->
      arrow a c)
  (identityLeft
    : {a b : object} ->
      (f : arrow a b) ->
      (arrow-eq (compose (identity a) f) f))
  (identityRight
    : {a b : object} ->
      (f : arrow a b) ->
      (arrow-eq (compose f (identity b)) f))
  (composeAssociative
    : {a b c d : object} ->
      (f : arrow a b) ->
      (g : arrow b c) ->
      (h : arrow c d) ->
      (arrow-eq (compose f (compose g h)) (compose (compose f g) h))) where
