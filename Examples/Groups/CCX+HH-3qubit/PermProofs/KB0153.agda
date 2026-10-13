{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0153 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0121 as B121

p0 : X0 • X0 • CX12 • CCX01 ≈ X0 • CCX01 • X0
p0 = by-assoc-and (under (X0) (ε) B121.proved) Eq.refl Eq.refl

p1 : X0 • X0 • CX12 • CCX01 ≈ CX12 • CCX01
p1 = by-assoc-and (under (ε) (CX12 • CCX01) B12.proved) Eq.refl Eq.refl

p2 : X0 • CCX01 • X0 ≈ CX12 • CCX01
p2 = trans (sym p0) p1

p3 : X0 • CCX01 • X0 ≈ X0 • CCX01 • X0
p3 = refl

p4 : CX12 • CCX01 ≈ CX12 • CCX01
p4 = refl

p5 : X0 • CCX01 • X0 ≈ CX12 • CCX01
p5 = trans (sym p3) (trans p2 p4)

proved : X0 • CCX01 • X0 ≈ CX12 • CCX01
proved = p5
