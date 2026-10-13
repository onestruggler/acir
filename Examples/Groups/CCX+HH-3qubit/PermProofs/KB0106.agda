{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0106 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

p0 : CCX01 ≈ SWAP12 • CCX02 • SWAP12
p0 = by-assoc-and (axiom r033) Eq.refl Eq.refl

p1 : CCX01 ≈ CCX01
p1 = refl

p2 : SWAP12 • CCX02 • SWAP12 ≈ SWAP12 • CCX02 • SWAP12
p2 = refl

p3 : CCX01 ≈ SWAP12 • CCX02 • SWAP12
p3 = trans (sym p1) (trans p0 p2)

p4 : SWAP12 • CCX02 • SWAP12 ≈ CCX01
p4 = sym p3

proved : SWAP12 • CCX02 • SWAP12 ≈ CCX01
proved = p4
