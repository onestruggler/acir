{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0033 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.Tietze.drel61 as Tdrel61
p0 : CX02 • X2 ≈ X2 • CX02
p0 = Tdrel61.proved

p1 : CX02 • X2 ≈ CX02 • X2
p1 = refl

p2 : X2 • CX02 ≈ X2 • CX02
p2 = refl

p3 : CX02 • X2 ≈ X2 • CX02
p3 = trans (sym p1) (trans p0 p2)

proved : CX02 • X2 ≈ X2 • CX02
proved = p3
