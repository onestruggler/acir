{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB3939 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0131 as B131
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0324 as B324
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0642 as B642
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1258 as B1258

p0 : CX10 • CCX12 • X2 • CCX01 • X0 • CX20 ≈ CX10 • CCX12 • CCX01 • CX20 • X2
p0 = by-assoc-and (under (CX10 • CCX12) (ε) B642.proved) Eq.refl Eq.refl

p1 : CX10 • CCX12 • X2 • CCX01 • X0 • CX20 ≈ X2 • CCX12 • CCX01 • X0 • CX20
p1 = by-assoc-and (under (ε) (CCX01 • X0 • CX20) B131.proved) Eq.refl Eq.refl

p2 : CX10 • CCX12 • CCX01 • CX20 • X2 ≈ X2 • CCX12 • CCX01 • X0 • CX20
p2 = trans (sym p0) p1

p3 : CX10 • CCX12 • CCX01 • CX20 • X2 ≈ CX10 • CX20 • CCX01 • CCX12 • X2
p3 = by-assoc-and (under (CX10) (X2) B324.proved) Eq.refl Eq.refl

p4 : CX10 • CCX12 • CCX01 • CX20 • X2 ≈ CX10 • CX20 • CCX01 • CCX12 • X2
p4 = trans p3 (refl)

p5 : X2 • CCX12 • CCX01 • X0 • CX20 ≈ X2 • CX20 • CCX01 • X0 • CCX12
p5 = by-assoc-and (under (X2) (ε) B1258.proved) Eq.refl Eq.refl

p6 : X2 • CCX12 • CCX01 • X0 • CX20 ≈ X2 • CX20 • CCX01 • X0 • CCX12
p6 = trans p5 (refl)

p7 : CX10 • CX20 • CCX01 • CCX12 • X2 ≈ X2 • CX20 • CCX01 • X0 • CCX12
p7 = trans (sym p4) (trans p2 p6)

proved : CX10 • CX20 • CCX01 • CCX12 • X2 ≈ X2 • CX20 • CCX01 • X0 • CCX12
proved = p7
