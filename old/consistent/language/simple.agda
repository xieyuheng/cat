{-# OPTIONS --prop --allow-unsolved-metas #-}

module language.simple where

-- Simple typed lambda calculus in de Bruijn style.

open import basic
open eqv-reasoning

data env-t : type0 where
  env-empty : env-t
  env-ext : string-t -> env-t -> env-t

data exp-t : type0 where
  var-c : string-t -> exp-t
  ap-c : exp-t -> exp-t -> exp-t
  fn-c : string-t -> exp-t -> exp-t -> exp-t

data val-t : type0 where
  val-var-c : string-t -> val-t
  val-ap-c : val-t -> val-t -> val-t
  val-fn-c : string-t -> val-t -> val-t -> env-t -> val-t

-- TODO
