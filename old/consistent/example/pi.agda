{-# OPTIONS --prop #-}

module example.pi where

open import basic

bool-or-nat : bool-t -> type0
bool-or-nat true = bool-t
bool-or-nat false = nat-t

p : (b : bool-t) -> bool-or-nat b
p true = true
p false = zero

pp : pi-t bool-t bool-or-nat
pp = pi p
