{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0125 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

import Examples.Groups.CCX+HH-3qubit.Tietze.drel106 as Tdrel106
p0 : X0 • X2 • CX02 ≈ CX02 • X0
p0 = Tdrel106.proved

p1 : X0 • X2 • CX02 ≈ X0 • X2 • CX02
p1 = refl

p2 : CX02 • X0 ≈ CX02 • X0
p2 = refl

p3 : X0 • X2 • CX02 ≈ CX02 • X0
p3 = trans (sym p1) (trans p0 p2)

proved : X0 • X2 • CX02 ≈ CX02 • X0
proved = p3
