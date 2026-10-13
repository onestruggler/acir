{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0786 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0046 as B46
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0047 as B47
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0140 as B140
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0141 as B141

p0 : CX10 • CCX12 • CX12 • CCX01 • X0 ≈ CX12 • CCX12 • CCX01 • X0
p0 = by-assoc-and (under (ε) (CCX01 • X0) B141.proved) Eq.refl Eq.refl

p1 : CX10 • CCX12 • CX12 • CCX01 • X0 ≈ CX10 • CCX12 • X0 • CCX01
p1 = by-assoc-and (under (CX10 • CCX12) (ε) B140.proved) Eq.refl Eq.refl

p2 : CX12 • CCX12 • CCX01 • X0 ≈ CX10 • CCX12 • X0 • CCX01
p2 = trans (sym p0) p1

p3 : CX12 • CCX12 • CCX01 • X0 ≈ CX12 • CCX12 • CCX01 • X0
p3 = refl

p4 : CX10 • CCX12 • X0 • CCX01 ≈ CX10 • X0 • CCX12 • CCX01
p4 = by-assoc-and (under (CX10) (CCX01) B46.proved) Eq.refl Eq.refl

p5 : CX10 • X0 • CCX12 • CCX01 ≈ X0 • CX10 • CCX12 • CCX01
p5 = by-assoc-and (under (ε) (CCX12 • CCX01) B47.proved) Eq.refl Eq.refl

p6 : CX10 • CCX12 • X0 • CCX01 ≈ X0 • CX10 • CCX12 • CCX01
p6 = trans p4 (trans p5 (refl))

p7 : CX12 • CCX12 • CCX01 • X0 ≈ X0 • CX10 • CCX12 • CCX01
p7 = trans (sym p3) (trans p2 p6)

proved : CX12 • CCX12 • CCX01 • X0 ≈ X0 • CX10 • CCX12 • CCX01
proved = p7
