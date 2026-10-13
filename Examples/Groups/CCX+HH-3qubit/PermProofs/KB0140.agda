{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0140 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0031 as B31

p0 : X0 • CCX01 ≈ CCX01 • CX12 • X0
p0 = by-assoc-and (axiom r042) Eq.refl Eq.refl

p1 : X0 • CCX01 ≈ X0 • CCX01
p1 = refl

p2 : CCX01 • CX12 • X0 ≈ CX12 • CCX01 • X0
p2 = by-assoc-and (under (ε) (X0) B31.proved) Eq.refl Eq.refl

p3 : CCX01 • CX12 • X0 ≈ CX12 • CCX01 • X0
p3 = trans p2 (refl)

p4 : X0 • CCX01 ≈ CX12 • CCX01 • X0
p4 = trans (sym p1) (trans p0 p3)

p5 : CX12 • CCX01 • X0 ≈ X0 • CCX01
p5 = sym p4

proved : CX12 • CCX01 • X0 ≈ X0 • CCX01
proved = p5
