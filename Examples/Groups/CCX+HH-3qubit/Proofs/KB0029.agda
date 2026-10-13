{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Proofs.KB0029 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

p0 : SWAP01 ≈ CX01 • CX10 • CX01
p0 = by-assoc-and (axiom r013) Eq.refl Eq.refl

p1 : SWAP01 ≈ SWAP01
p1 = refl

p2 : CX01 • CX10 • CX01 ≈ CX01 • CX10 • CX01
p2 = refl

p3 : SWAP01 ≈ CX01 • CX10 • CX01
p3 = trans (sym p1) (trans p0 p2)

p4 : CX01 • CX10 • CX01 ≈ SWAP01
p4 = sym p3

proved : CX01 • CX10 • CX01 ≈ SWAP01
proved = p4
