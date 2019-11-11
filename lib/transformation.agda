{-# OPTIONS --prop #-}

module transformation where

open import pure
open import simple
open import category
open category-t
open import functor
open functor-t

record transformation-t (lv : level-t) : type (lsucc lv) where
  field
    dom : category-t lv
    cod : category-t lv
    src : functor-t dom cod
    tar : functor-t dom cod
    component :
      (a : dom .object-t) ->
      cod .morphism-t (src .map a) (tar .map a)
    natural :
      {a b : dom .object-t}
      (f : dom .morphism-t a b) ->
      the-eqv-t (cod .morphism-t (src .map a) (tar .map b))
        (cod .compose (component a) (tar .fmap f))
        (cod .compose (src .fmap f) (component b))
