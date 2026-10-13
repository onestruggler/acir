{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB2682 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0315 as B315
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0709 as B709

p0 : CX10 • CX02 • CCX12 • CX01 • CCX01 ≈ CX10 • CCX01 • CCX12 • CX01
p0 = by-assoc-and (under (CX10) (ε) B709.proved) Eq.refl Eq.refl

p1 : CX10 • CX02 • CCX12 • CX01 • CCX01 ≈ CX02 • CCX12 • CX12 • CX01 • CCX01
p1 = by-assoc-and (under (ε) (CX01 • CCX01) B315.proved) Eq.refl Eq.refl

p2 : CX10 • CCX01 • CCX12 • CX01 ≈ CX02 • CCX12 • CX12 • CX01 • CCX01
p2 = trans (sym p0) p1

p3 : CX10 • CCX01 • CCX12 • CX01 ≈ CX10 • CCX01 • CCX12 • CX01
p3 = refl

p4 : CX02 • CCX12 • CX12 • CX01 • CCX01 ≈ CX02 • CCX12 • CX12 • CX01 • CCX01
p4 = refl

p5 : CX10 • CCX01 • CCX12 • CX01 ≈ CX02 • CCX12 • CX12 • CX01 • CCX01
p5 = trans (sym p3) (trans p2 p4)

p6 : CX02 • CCX12 • CX12 • CX01 • CCX01 ≈ CX10 • CCX01 • CCX12 • CX01
p6 = sym p5

proved : CX02 • CCX12 • CX12 • CX01 • CCX01 ≈ CX10 • CCX01 • CCX12 • CX01
proved = p6
