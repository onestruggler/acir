{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Proofs.KB0040 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

p0 : X1 ≈ SWAP01 • X0 • SWAP01
p0 = by-assoc-and (axiom r028) Eq.refl Eq.refl

p1 : X1 ≈ X1
p1 = refl

p2 : SWAP01 • X0 • SWAP01 ≈ SWAP01 • X0 • SWAP01
p2 = refl

p3 : X1 ≈ SWAP01 • X0 • SWAP01
p3 = trans (sym p1) (trans p0 p2)

p4 : SWAP01 • X0 • SWAP01 ≈ X1
p4 = sym p3

proved : SWAP01 • X0 • SWAP01 ≈ X1
proved = p4
