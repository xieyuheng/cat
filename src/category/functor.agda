{-# OPTIONS --type-in-type #-}
{-# OPTIONS --prop #-}
{-# OPTIONS --allow-unsolved-metas #-}

module category.functor where

open import basic

open import category
open category-t

record functor-t (dom cod : category-t) : type where
  field
    map : dom .object-t  -> cod .object-t
    fmap : {a b : dom .object-t} ->
      dom .morphism-t a b ->
      cod .morphism-t (map a) (map b)
    fmap-compose : {a b c : dom .object-t} ->
      (f : dom .morphism-t a b) ->
      (g : dom .morphism-t b c) ->
      the-eqv-t (cod .morphism-t (map a) (map c))
        (fmap (dom .compose f g))
        (cod .compose (fmap f) (fmap g))
    fmap-id : {a : dom .object-t} ->
      the-eqv-t (cod .morphism-t (map a) (map a))
        (fmap (dom .id a))
        (cod .id (map a))
