{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0972 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0026 as B26
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0219 as B219

p0 : CX12 • CX10 • CCX02 • CX10 ≈ CX12 • CX01 • CCX12 • CX01
p0 = by-assoc-and (under (CX12) (ε) B219.proved) Eq.refl Eq.refl

p1 : CX12 • CX10 • CCX02 • CX10 ≈ CX10 • CX12 • CCX02 • CX10
p1 = by-assoc-and (under (ε) (CCX02 • CX10) B26.proved) Eq.refl Eq.refl

p2 : CX12 • CX01 • CCX12 • CX01 ≈ CX10 • CX12 • CCX02 • CX10
p2 = trans (sym p0) p1

p3 : CX12 • CX01 • CCX12 • CX01 ≈ CX12 • CX01 • CCX12 • CX01
p3 = refl

p4 : CX10 • CX12 • CCX02 • CX10 ≈ CX10 • CX12 • CCX02 • CX10
p4 = refl

p5 : CX12 • CX01 • CCX12 • CX01 ≈ CX10 • CX12 • CCX02 • CX10
p5 = trans (sym p3) (trans p2 p4)

proved : CX12 • CX01 • CCX12 • CX01 ≈ CX10 • CX12 • CCX02 • CX10
proved = p5
