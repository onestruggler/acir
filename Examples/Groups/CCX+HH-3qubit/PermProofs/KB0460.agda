{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0460 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0022 as B22
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0035 as B35
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0144 as B144

p0 : CX01 • X1 • CX12 • X1 ≈ CX01 • X2 • CX12
p0 = by-assoc-and (under (CX01) (ε) B144.proved) Eq.refl Eq.refl

p1 : CX01 • X1 • CX12 • X1 ≈ X1 • CX01 • CX12 • X1
p1 = by-assoc-and (under (ε) (CX12 • X1) B35.proved) Eq.refl Eq.refl

p2 : CX01 • X2 • CX12 ≈ X1 • CX01 • CX12 • X1
p2 = trans (sym p0) p1

p3 : CX01 • X2 • CX12 ≈ X2 • CX01 • CX12
p3 = by-assoc-and (under (ε) (CX12) B22.proved) Eq.refl Eq.refl

p4 : CX01 • X2 • CX12 ≈ X2 • CX01 • CX12
p4 = trans p3 (refl)

p5 : X1 • CX01 • CX12 • X1 ≈ X1 • CX01 • CX12 • X1
p5 = refl

p6 : X2 • CX01 • CX12 ≈ X1 • CX01 • CX12 • X1
p6 = trans (sym p4) (trans p2 p5)

p7 : X1 • CX01 • CX12 • X1 ≈ X2 • CX01 • CX12
p7 = sym p6

proved : X1 • CX01 • CX12 • X1 ≈ X2 • CX01 • CX12
proved = p7
