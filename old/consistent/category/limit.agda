{-# OPTIONS --prop #-}

module category.limit where

open import basic

open import category
open category-t

open import category.functor
open functor-t

-- NOTE
-- useing fulfilling type system
-- one can avoid choosing between argument and field

record cone-t
  {lv : level-t}
  (shape cat : category-t lv)
  (diagram : functor-t shape cat)
  (apex : cat .object-t)
  : type (lsucc lv) where
  field
    line :
      (index : shape .object-t) ->
      cat .morphism-t apex (diagram .map index)
open cone-t

record limit-t
  {lv : level-t}
  (shape cat : category-t lv)
  : type (lsucc lv) where
  field
    diagram : functor-t shape cat
    apex : cat .object-t
    cone : cone-t shape cat diagram apex
    mediate :
      (other-apex : cat .object-t) ->
      (other-cone : cone-t shape cat diagram other-apex) ->
      cat .morphism-t other-apex apex
    mediating-morphism-commute :
      (other-apex : cat .object-t)
      (other-cone : cone-t shape cat diagram other-apex)
      (index : shape .object-t) ->
      the-eqv-t (cat .morphism-t other-apex (diagram .map index))
        (other-cone .line index)
        (cat .compose (mediate other-apex other-cone) (cone .line index))
    mediating-morphism-unique :
      (other-apex : cat .object-t)
      (other-cone : cone-t shape cat diagram other-apex)
      (other-mediating-morphism : (cat .morphism-t other-apex apex)) ->
      (index : shape .object-t) ->
      the-eqv-t (cat .morphism-t other-apex (diagram .map index))
        (other-cone .line index)
        (cat .compose other-mediating-morphism (cone .line index)) ->
      eqv-t other-mediating-morphism (mediate other-apex other-cone)
