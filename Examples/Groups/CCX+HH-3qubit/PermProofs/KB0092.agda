{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0092 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

p0 : X2 ≈ SWAP02 • X0 • SWAP02
p0 = by-assoc-and (axiom r015) Eq.refl Eq.refl

p1 : X2 ≈ X2
p1 = refl

p2 : SWAP02 • X0 • SWAP02 ≈ SWAP02 • X0 • SWAP02
p2 = refl

p3 : X2 ≈ SWAP02 • X0 • SWAP02
p3 = trans (sym p1) (trans p0 p2)

p4 : SWAP02 • X0 • SWAP02 ≈ X2
p4 = sym p3

proved : SWAP02 • X0 • SWAP02 ≈ X2
proved = p4
