{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1448 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0126 as B126
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0164 as B164
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0217 as B217

p0 : CX01 • CX02 • CX21 • CCX01 • CX21 ≈ CX01 • CX02 • CX12 • CCX02 • CX12
p0 = by-assoc-and (under (CX01 • CX02) (ε) B217.proved) Eq.refl Eq.refl

p1 : CX01 • CX02 • CX21 • CCX01 • CX21 ≈ CX21 • CX02 • CCX01 • CX21
p1 = by-assoc-and (under (ε) (CCX01 • CX21) B126.proved) Eq.refl Eq.refl

p2 : CX01 • CX02 • CX12 • CCX02 • CX12 ≈ CX21 • CX02 • CCX01 • CX21
p2 = trans (sym p0) p1

p3 : CX01 • CX02 • CX12 • CCX02 • CX12 ≈ CX12 • CX01 • CCX02 • CX12
p3 = by-assoc-and (under (ε) (CCX02 • CX12) B164.proved) Eq.refl Eq.refl

p4 : CX01 • CX02 • CX12 • CCX02 • CX12 ≈ CX12 • CX01 • CCX02 • CX12
p4 = trans p3 (refl)

p5 : CX21 • CX02 • CCX01 • CX21 ≈ CX21 • CX02 • CCX01 • CX21
p5 = refl

p6 : CX12 • CX01 • CCX02 • CX12 ≈ CX21 • CX02 • CCX01 • CX21
p6 = trans (sym p4) (trans p2 p5)

p7 : CX21 • CX02 • CCX01 • CX21 ≈ CX12 • CX01 • CCX02 • CX12
p7 = sym p6

proved : CX21 • CX02 • CCX01 • CX21 ≈ CX12 • CX01 • CCX02 • CX12
proved = p7
