{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0814 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0813 as B813

p0 : CCX01 • CX01 • X0 • CCX01 • CCX01 ≈ CX12 • CX01 • X0 • CCX01
p0 = by-assoc-and (under (ε) (CCX01) B813.proved) Eq.refl Eq.refl

p1 : CCX01 • CX01 • X0 • CCX01 • CCX01 ≈ CCX01 • CX01 • X0
p1 = by-assoc-and (under (CCX01 • CX01 • X0) (ε) B11.proved) Eq.refl Eq.refl

p2 : CX12 • CX01 • X0 • CCX01 ≈ CCX01 • CX01 • X0
p2 = trans (sym p0) p1

p3 : CX12 • CX01 • X0 • CCX01 ≈ CX12 • CX01 • X0 • CCX01
p3 = refl

p4 : CCX01 • CX01 • X0 ≈ CCX01 • CX01 • X0
p4 = refl

p5 : CX12 • CX01 • X0 • CCX01 ≈ CCX01 • CX01 • X0
p5 = trans (sym p3) (trans p2 p4)

proved : CX12 • CX01 • X0 • CCX01 ≈ CCX01 • CX01 • X0
proved = p5
