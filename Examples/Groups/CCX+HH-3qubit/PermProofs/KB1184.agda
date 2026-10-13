{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1184 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0046 as B46
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0293 as B293
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0366 as B366

p0 : CCX01 • CCX12 • CX12 • X0 ≈ CX10 • CCX01 • CCX12 • X0
p0 = by-assoc-and (under (ε) (X0) B293.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX12 • CX12 • X0 ≈ CCX01 • CCX12 • X0 • CX12
p1 = by-assoc-and (under (CCX01 • CCX12) (ε) B45.proved) Eq.refl Eq.refl

p2 : CX10 • CCX01 • CCX12 • X0 ≈ CCX01 • CCX12 • X0 • CX12
p2 = trans (sym p0) p1

p3 : CX10 • CCX01 • CCX12 • X0 ≈ CX10 • CCX01 • X0 • CCX12
p3 = by-assoc-and (under (CX10 • CCX01) (ε) B46.proved) Eq.refl Eq.refl

p4 : CX10 • CCX01 • X0 • CCX12 ≈ X0 • CCX01 • CX10 • CCX12
p4 = by-assoc-and (under (ε) (CCX12) B366.proved) Eq.refl Eq.refl

p5 : CX10 • CCX01 • CCX12 • X0 ≈ X0 • CCX01 • CX10 • CCX12
p5 = trans p3 (trans p4 (refl))

p6 : CCX01 • CCX12 • X0 • CX12 ≈ CCX01 • X0 • CCX12 • CX12
p6 = by-assoc-and (under (CCX01) (CX12) B46.proved) Eq.refl Eq.refl

p7 : CCX01 • CCX12 • X0 • CX12 ≈ CCX01 • X0 • CCX12 • CX12
p7 = trans p6 (refl)

p8 : X0 • CCX01 • CX10 • CCX12 ≈ CCX01 • X0 • CCX12 • CX12
p8 = trans (sym p5) (trans p2 p7)

p9 : CCX01 • X0 • CCX12 • CX12 ≈ X0 • CCX01 • CX10 • CCX12
p9 = sym p8

proved : CCX01 • X0 • CCX12 • CX12 ≈ X0 • CCX01 • CX10 • CCX12
proved = p9
