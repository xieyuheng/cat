{-# OPTIONS --prop #-}

module transformation where

open import pure
open import basic
open import category
open category-t
open import functor
open functor-t

record transformation-t
  {lv : level-t}
  {dom cod : category-t lv}
  (src tar : functor-t dom cod)
  : type (lsucc lv) where
  field
    component :
      (a : dom .object-t) ->
      cod .morphism-t (src .map a) (tar .map a)
    natural :
      {a b : dom .object-t}
      (f : dom .morphism-t a b) ->
      the-eqv-t (cod .morphism-t (src .map a) (tar .map b))
        (cod .compose (component a) (tar .fmap f))
        (cod .compose (src .fmap f) (component b))
