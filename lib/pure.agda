module pure where

-- type --

type-t = Set
type-t1 = Set1

-- eqv --

data eqv-t {A : type-t} (q : A) : A -> type-t where
  eqv-c : (eqv-t q q)

eqv-apply : {A B : _} {x y : _}
  (f : A -> B) -> (eqv-t x y) -> (eqv-t (f x) (f y))
eqv-apply f eqv-c = eqv-c

eqv-compose :
  {type : type-t} ->
  {x y z : type} ->
  (eqv-t x y) -> (eqv-t y z) -> (eqv-t x z)
eqv-compose eqv-c eqv-c = eqv-c

eqv-swap :
  {type : type-t} ->
  {x y : type} ->
  (eqv-t x y) -> (eqv-t y x)
eqv-swap eqv-c = eqv-c
