{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0081 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

p0 : CX02 ≈ SWAP12 • CX01 • SWAP12
p0 = by-assoc-and (axiom r009) Eq.refl Eq.refl

p1 : CX02 ≈ CX02
p1 = refl

p2 : SWAP12 • CX01 • SWAP12 ≈ SWAP12 • CX01 • SWAP12
p2 = refl

p3 : CX02 ≈ SWAP12 • CX01 • SWAP12
p3 = trans (sym p1) (trans p0 p2)

p4 : SWAP12 • CX01 • SWAP12 ≈ CX02
p4 = sym p3

proved : SWAP12 • CX01 • SWAP12 ≈ CX02
proved = p4
