{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1658 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0164 as B164
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0219 as B219
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0311 as B311

p0 : CX10 • CCX02 • CX10 • CX02 • CX12 ≈ CX10 • CCX02 • CX02 • CX10
p0 = by-assoc-and (under (CX10 • CCX02) (ε) B311.proved) Eq.refl Eq.refl

p1 : CX10 • CCX02 • CX10 • CX02 • CX12 ≈ CX01 • CCX12 • CX01 • CX02 • CX12
p1 = by-assoc-and (under (ε) (CX02 • CX12) B219.proved) Eq.refl Eq.refl

p2 : CX10 • CCX02 • CX02 • CX10 ≈ CX01 • CCX12 • CX01 • CX02 • CX12
p2 = trans (sym p0) p1

p3 : CX10 • CCX02 • CX02 • CX10 ≈ CX10 • CCX02 • CX02 • CX10
p3 = refl

p4 : CX01 • CCX12 • CX01 • CX02 • CX12 ≈ CX01 • CCX12 • CX12 • CX01
p4 = by-assoc-and (under (CX01 • CCX12) (ε) B164.proved) Eq.refl Eq.refl

p5 : CX01 • CCX12 • CX01 • CX02 • CX12 ≈ CX01 • CCX12 • CX12 • CX01
p5 = trans p4 (refl)

p6 : CX10 • CCX02 • CX02 • CX10 ≈ CX01 • CCX12 • CX12 • CX01
p6 = trans (sym p3) (trans p2 p5)

proved : CX10 • CCX02 • CX02 • CX10 ≈ CX01 • CCX12 • CX12 • CX01
proved = p6
