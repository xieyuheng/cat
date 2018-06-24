module day1-without-var where

open import little

data exp-type-t : type-tt where
  nat-type-c  : exp-type-t
  bool-type-c : exp-type-t

data exp-t : exp-type-t -> type-tt where
  lit-exp-c
    : (n : nat-t) -> exp-t nat-type-c
  true-exp-c
    : exp-t bool-type-c
  false-exp-c
    : exp-t bool-type-c
  less-exp-c
    : (a, b : exp-t nat-type-c) -> exp-t bool-type-c
  plus-exp-c
    : (a, b : exp-t nat-type-c) -> exp-t nat-type-c
  if-exp-c
    : {t : exp-type-t} ->
      (q : exp-t bool-type-c) -> (a, e : exp-t t) -> exp-t t

value-t : exp-type-t -> type-tt
value-t nat-type-c = nat-t
value-t bool-type-c = bool-t

eval : {t : exp-type-t} -> exp-t t -> value-t t
eval (lit-exp-c n) = n
eval true-exp-c = false-c
eval false-exp-c = false-c
eval (less-exp-c a b) = nat-lt-p (eval a) (eval b)
eval (plus-exp-c a b) = nat-add (eval a) (eval b)
eval (if-exp-c q a e) = if (eval q) (eval a) (eval e)
