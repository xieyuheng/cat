{-# OPTIONS --type-in-type #-}
{-# OPTIONS --prop #-}
{-# OPTIONS --allow-unsolved-metas #-}

module adventure.jojo where

open import basic
open eqv-reasoning

data env-t : type where
  -- TODO

data ctx-t : type where
  -- TODO

data jo-t : type where
  var-c : string-t -> jo-t
  jojo-c : list-t jo-t -> jo-t
  cut-c : jo-t -> jo-t

data val-t : type where
  val-var-c : string-t -> val-t
  val-jojo-c : env-t -> list-t jo-t -> val-t

--     quo : elem-t -> elem-t
--     exe : elem-t
--     quo-exe : (x : elem-t) ->
--       eqv-t ((quo x) * exe) x
--     quo-cut : (x : elem-t) ->
--       eqv-t (cut (quo x)) (quo (cut x))

--     drop : elem-t
--     drop-quo : (x : elem-t) ->
--       eqv-t ((quo x) * drop) id

--     dup : elem-t
--     dup-quo : (x : elem-t) ->
--       eqv-t ((quo x) * dup) ((quo x) * (quo x))

--     swap : elem-t
--     swap-quo : (x y : elem-t) ->
--       eqv-t ((quo x) * (quo y) * swap) ((quo y) * (quo x))

--     pair fst snd : elem-t
--     pair-fst : (x y : elem-t) ->
--       eqv-t (x * y * pair * fst) x
--     pair-snd : (x y : elem-t) ->
--       eqv-t (x * y * pair * snd) y

--     branch left right : elem-t
--     branch-left : (x y : elem-t) ->
--       eqv-t (left * x * y * branch) x
--     branch-right : (x y : elem-t) ->
--       eqv-t (right * x * y * branch) y
