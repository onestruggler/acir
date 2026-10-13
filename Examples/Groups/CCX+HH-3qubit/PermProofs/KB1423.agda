{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1423 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0046 as B46
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0152 as B152
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0211 as B211
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1184 as B1184

p0 : CCX01 • CCX12 • CCX01 • X0 • CCX01 ≈ CX02 • CCX12 • CX02 • X0 • CCX01
p0 = by-assoc-and (under (ε) (X0 • CCX01) B211.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX12 • CCX01 • X0 • CCX01 ≈ CCX01 • CCX12 • X0 • CX12
p1 = by-assoc-and (under (CCX01 • CCX12) (ε) B152.proved) Eq.refl Eq.refl

p2 : CX02 • CCX12 • CX02 • X0 • CCX01 ≈ CCX01 • CCX12 • X0 • CX12
p2 = trans (sym p0) p1

p3 : CX02 • CCX12 • CX02 • X0 • CCX01 ≈ CX02 • CCX12 • CX02 • X0 • CCX01
p3 = refl

p4 : CCX01 • CCX12 • X0 • CX12 ≈ CCX01 • X0 • CCX12 • CX12
p4 = by-assoc-and (under (CCX01) (CX12) B46.proved) Eq.refl Eq.refl

p5 : CCX01 • X0 • CCX12 • CX12 ≈ X0 • CCX01 • CX10 • CCX12
p5 = by-assoc-and (under (ε) (ε) B1184.proved) Eq.refl Eq.refl

p6 : CCX01 • CCX12 • X0 • CX12 ≈ X0 • CCX01 • CX10 • CCX12
p6 = trans p4 (trans p5 (refl))

p7 : CX02 • CCX12 • CX02 • X0 • CCX01 ≈ X0 • CCX01 • CX10 • CCX12
p7 = trans (sym p3) (trans p2 p6)

proved : CX02 • CCX12 • CX02 • X0 • CCX01 ≈ X0 • CCX01 • CX10 • CCX12
proved = p7
