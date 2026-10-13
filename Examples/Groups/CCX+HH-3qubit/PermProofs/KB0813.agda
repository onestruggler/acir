{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0813 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0123 as B123
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0152 as B152
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0505 as B505

p0 : CX01 • CX02 • CCX01 • X0 • CCX01 ≈ CX01 • CX02 • X0 • CX12
p0 = by-assoc-and (under (CX01 • CX02) (ε) B152.proved) Eq.refl Eq.refl

p1 : CX01 • CX02 • CCX01 • X0 • CCX01 ≈ CCX01 • CX01 • X0 • CCX01
p1 = by-assoc-and (under (ε) (X0 • CCX01) B123.proved) Eq.refl Eq.refl

p2 : CX01 • CX02 • X0 • CX12 ≈ CCX01 • CX01 • X0 • CCX01
p2 = trans (sym p0) p1

p3 : CX01 • CX02 • X0 • CX12 ≈ CX12 • CX01 • X0
p3 = by-assoc-and (under (ε) (ε) B505.proved) Eq.refl Eq.refl

p4 : CX01 • CX02 • X0 • CX12 ≈ CX12 • CX01 • X0
p4 = trans p3 (refl)

p5 : CCX01 • CX01 • X0 • CCX01 ≈ CCX01 • CX01 • X0 • CCX01
p5 = refl

p6 : CX12 • CX01 • X0 ≈ CCX01 • CX01 • X0 • CCX01
p6 = trans (sym p4) (trans p2 p5)

p7 : CCX01 • CX01 • X0 • CCX01 ≈ CX12 • CX01 • X0
p7 = sym p6

proved : CCX01 • CX01 • X0 • CCX01 ≈ CX12 • CX01 • X0
proved = p7
