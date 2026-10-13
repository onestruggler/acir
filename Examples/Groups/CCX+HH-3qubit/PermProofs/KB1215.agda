{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1215 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0119 as B119
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0310 as B310

p0 : CX01 • CCX02 • CX02 • CX10 • CX12 ≈ CX01 • CCX02 • CX10 • CX02
p0 = by-assoc-and (under (CX01 • CCX02) (ε) B310.proved) Eq.refl Eq.refl

p1 : CX01 • CCX02 • CX02 • CX10 • CX12 ≈ CX02 • CCX02 • CX10 • CX12
p1 = by-assoc-and (under (ε) (CX10 • CX12) B119.proved) Eq.refl Eq.refl

p2 : CX01 • CCX02 • CX10 • CX02 ≈ CX02 • CCX02 • CX10 • CX12
p2 = trans (sym p0) p1

p3 : CX01 • CCX02 • CX10 • CX02 ≈ CX01 • CCX02 • CX10 • CX02
p3 = refl

p4 : CX02 • CCX02 • CX10 • CX12 ≈ CX02 • CCX02 • CX10 • CX12
p4 = refl

p5 : CX01 • CCX02 • CX10 • CX02 ≈ CX02 • CCX02 • CX10 • CX12
p5 = trans (sym p3) (trans p2 p4)

p6 : CX02 • CCX02 • CX10 • CX12 ≈ CX01 • CCX02 • CX10 • CX02
p6 = sym p5

proved : CX02 • CCX02 • CX10 • CX12 ≈ CX01 • CCX02 • CX10 • CX02
proved = p6
