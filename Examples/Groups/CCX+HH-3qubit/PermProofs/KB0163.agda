{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0163 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0006 as B6
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0127 as B127

p0 : CX12 • CX12 • CX01 • CX02 ≈ CX12 • CX01 • CX12
p0 = by-assoc-and (under (CX12) (ε) B127.proved) Eq.refl Eq.refl

p1 : CX12 • CX12 • CX01 • CX02 ≈ CX01 • CX02
p1 = by-assoc-and (under (ε) (CX01 • CX02) B6.proved) Eq.refl Eq.refl

p2 : CX12 • CX01 • CX12 ≈ CX01 • CX02
p2 = trans (sym p0) p1

p3 : CX12 • CX01 • CX12 ≈ CX12 • CX01 • CX12
p3 = refl

p4 : CX01 • CX02 ≈ CX01 • CX02
p4 = refl

p5 : CX12 • CX01 • CX12 ≈ CX01 • CX02
p5 = trans (sym p3) (trans p2 p4)

proved : CX12 • CX01 • CX12 ≈ CX01 • CX02
proved = p5
