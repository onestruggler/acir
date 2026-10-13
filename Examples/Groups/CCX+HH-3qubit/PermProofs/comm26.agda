{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.comm26 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0152 as B152
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0153 as B153

p0 : X0 • CCX01 • X0 • CCX01 ≈ CX12 • CCX01 • CCX01
p0 = by-assoc-and (under (ε) (CCX01) B153.proved) Eq.refl Eq.refl

p1 : CX12 • CCX01 • CCX01 ≈ CX12
p1 = by-assoc-and (under (CX12) (ε) B11.proved) Eq.refl Eq.refl

p2 : X0 • CCX01 • X0 • CCX01 ≈ CX12
p2 = trans p0 (trans p1 (refl))

p3 : CCX01 • X0 • CCX01 • X0 ≈ X0 • CX12 • X0
p3 = by-assoc-and (under (ε) (X0) B152.proved) Eq.refl Eq.refl

p4 : X0 • CX12 • X0 ≈ X0 • X0 • CX12
p4 = by-assoc-and (under (X0) (ε) B45.proved) Eq.refl Eq.refl

p5 : X0 • X0 • CX12 ≈ CX12
p5 = by-assoc-and (under (ε) (CX12) B12.proved) Eq.refl Eq.refl

p6 : CCX01 • X0 • CCX01 • X0 ≈ CX12
p6 = trans p3 (trans p4 (trans p5 (refl)))

proved : X0 • CCX01 • X0 • CCX01 ≈ CCX01 • X0 • CCX01 • X0
proved = trans p2 (sym p6)
