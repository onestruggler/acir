{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0283 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0123 as B123
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0127 as B127

p0 : CX12 • CX01 • CX02 • CCX01 ≈ CX01 • CX12 • CCX01
p0 = by-assoc-and (under (ε) (CCX01) B127.proved) Eq.refl Eq.refl

p1 : CX12 • CX01 • CX02 • CCX01 ≈ CX12 • CCX01 • CX01
p1 = by-assoc-and (under (CX12) (ε) B123.proved) Eq.refl Eq.refl

p2 : CX01 • CX12 • CCX01 ≈ CX12 • CCX01 • CX01
p2 = trans (sym p0) p1

p3 : CX01 • CX12 • CCX01 ≈ CX01 • CX12 • CCX01
p3 = refl

p4 : CX12 • CCX01 • CX01 ≈ CX12 • CCX01 • CX01
p4 = refl

p5 : CX01 • CX12 • CCX01 ≈ CX12 • CCX01 • CX01
p5 = trans (sym p3) (trans p2 p4)

p6 : CX12 • CCX01 • CX01 ≈ CX01 • CX12 • CCX01
p6 = sym p5

proved : CX12 • CCX01 • CX01 ≈ CX01 • CX12 • CCX01
proved = p6
