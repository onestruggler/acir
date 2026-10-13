{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB2681 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0022 as B22
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0029 as B29
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0709 as B709

p0 : CX02 • CCX12 • CX01 • CCX01 • X2 ≈ CCX01 • CCX12 • CX01 • X2
p0 = by-assoc-and (under (ε) (X2) B709.proved) Eq.refl Eq.refl

p1 : CX02 • CCX12 • CX01 • CCX01 • X2 ≈ CX02 • CCX12 • CX01 • X2 • CCX01
p1 = by-assoc-and (under (CX02 • CCX12 • CX01) (ε) B29.proved) Eq.refl Eq.refl

p2 : CCX01 • CCX12 • CX01 • X2 ≈ CX02 • CCX12 • CX01 • X2 • CCX01
p2 = trans (sym p0) p1

p3 : CCX01 • CCX12 • CX01 • X2 ≈ CCX01 • CCX12 • X2 • CX01
p3 = by-assoc-and (under (CCX01 • CCX12) (ε) B22.proved) Eq.refl Eq.refl

p4 : CCX01 • CCX12 • CX01 • X2 ≈ CCX01 • CCX12 • X2 • CX01
p4 = trans p3 (refl)

p5 : CX02 • CCX12 • CX01 • X2 • CCX01 ≈ CX02 • CCX12 • X2 • CX01 • CCX01
p5 = by-assoc-and (under (CX02 • CCX12) (CCX01) B22.proved) Eq.refl Eq.refl

p6 : CX02 • CCX12 • CX01 • X2 • CCX01 ≈ CX02 • CCX12 • X2 • CX01 • CCX01
p6 = trans p5 (refl)

p7 : CCX01 • CCX12 • X2 • CX01 ≈ CX02 • CCX12 • X2 • CX01 • CCX01
p7 = trans (sym p4) (trans p2 p6)

p8 : CX02 • CCX12 • X2 • CX01 • CCX01 ≈ CCX01 • CCX12 • X2 • CX01
p8 = sym p7

proved : CX02 • CCX12 • X2 • CX01 • CCX01 ≈ CCX01 • CCX12 • X2 • CX01
proved = p8
