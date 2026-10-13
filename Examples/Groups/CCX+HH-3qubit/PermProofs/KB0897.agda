{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0897 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0044 as B44
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0152 as B152
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0186 as B186
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0832 as B832

p0 : CCX01 • X1 • CCX01 • X0 • CCX01 ≈ X1 • CX02 • X0 • CCX01
p0 = by-assoc-and (under (ε) (X0 • CCX01) B186.proved) Eq.refl Eq.refl

p1 : CCX01 • X1 • CCX01 • X0 • CCX01 ≈ CCX01 • X1 • X0 • CX12
p1 = by-assoc-and (under (CCX01 • X1) (ε) B152.proved) Eq.refl Eq.refl

p2 : X1 • CX02 • X0 • CCX01 ≈ CCX01 • X1 • X0 • CX12
p2 = trans (sym p0) p1

p3 : X1 • CX02 • X0 • CCX01 ≈ X0 • X2 • CCX01 • X1
p3 = by-assoc-and (under (ε) (ε) B832.proved) Eq.refl Eq.refl

p4 : X1 • CX02 • X0 • CCX01 ≈ X0 • X2 • CCX01 • X1
p4 = trans p3 (refl)

p5 : CCX01 • X1 • X0 • CX12 ≈ CCX01 • X0 • X1 • CX12
p5 = by-assoc-and (under (CCX01) (CX12) B44.proved) Eq.refl Eq.refl

p6 : CCX01 • X1 • X0 • CX12 ≈ CCX01 • X0 • X1 • CX12
p6 = trans p5 (refl)

p7 : X0 • X2 • CCX01 • X1 ≈ CCX01 • X0 • X1 • CX12
p7 = trans (sym p4) (trans p2 p6)

p8 : CCX01 • X0 • X1 • CX12 ≈ X0 • X2 • CCX01 • X1
p8 = sym p7

proved : CCX01 • X0 • X1 • CX12 ≈ X0 • X2 • CCX01 • X1
proved = p8
