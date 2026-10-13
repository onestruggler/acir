{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0084 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

p0 : SWAP02 ≈ CX02 • CX20 • CX02
p0 = by-assoc-and (axiom r010) Eq.refl Eq.refl

p1 : SWAP02 ≈ SWAP02
p1 = refl

p2 : CX02 • CX20 • CX02 ≈ CX02 • CX20 • CX02
p2 = refl

p3 : SWAP02 ≈ CX02 • CX20 • CX02
p3 = trans (sym p1) (trans p0 p2)

p4 : CX02 • CX20 • CX02 ≈ SWAP02
p4 = sym p3

proved : CX02 • CX20 • CX02 ≈ SWAP02
proved = p4
