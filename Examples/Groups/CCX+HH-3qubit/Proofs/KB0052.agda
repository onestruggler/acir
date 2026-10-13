{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Proofs.KB0052 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0001 as B1
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0028 as B28

p0 : K01 • CX01 • CX01 ≈ CX10 • K01 • CX01
p0 = by-assoc-and (under (ε) (CX01) B28.proved) Eq.refl Eq.refl

p1 : K01 • CX01 • CX01 ≈ K01
p1 = by-assoc-and (under (K01) (ε) B1.proved) Eq.refl Eq.refl

p2 : CX10 • K01 • CX01 ≈ K01
p2 = trans (sym p0) p1

p3 : CX10 • K01 • CX01 ≈ CX10 • CX10 • K01
p3 = by-assoc-and (under (CX10) (ε) B28.proved) Eq.refl Eq.refl

p4 : CX10 • K01 • CX01 ≈ CX10 • CX10 • K01
p4 = trans p3 (refl)

p5 : K01 ≈ K01
p5 = refl

p6 : CX10 • CX10 • K01 ≈ K01
p6 = trans (sym p4) (trans p2 p5)

proved : CX10 • CX10 • K01 ≈ K01
proved = p6
