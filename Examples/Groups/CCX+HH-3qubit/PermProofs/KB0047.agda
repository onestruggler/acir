{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0047 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

p0 : X0 • CX10 ≈ CX10 • X0
p0 = by-assoc-and (axiom r038) Eq.refl Eq.refl

p1 : X0 • CX10 ≈ X0 • CX10
p1 = refl

p2 : CX10 • X0 ≈ CX10 • X0
p2 = refl

p3 : X0 • CX10 ≈ CX10 • X0
p3 = trans (sym p1) (trans p0 p2)

p4 : CX10 • X0 ≈ X0 • CX10
p4 = sym p3

proved : CX10 • X0 ≈ X0 • CX10
proved = p4
