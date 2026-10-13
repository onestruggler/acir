{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0783 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0018 as B18
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0044 as B44
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0117 as B117
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0140 as B140

p0 : X1 • X2 • CX12 • CCX01 • X0 ≈ X1 • X2 • X0 • CCX01
p0 = by-assoc-and (under (X1 • X2) (ε) B140.proved) Eq.refl Eq.refl

p1 : X1 • X2 • CX12 • CCX01 • X0 ≈ CX12 • X1 • CCX01 • X0
p1 = by-assoc-and (under (ε) (CCX01 • X0) B117.proved) Eq.refl Eq.refl

p2 : X1 • X2 • X0 • CCX01 ≈ CX12 • X1 • CCX01 • X0
p2 = trans (sym p0) p1

p3 : X1 • X2 • X0 • CCX01 ≈ X1 • X0 • X2 • CCX01
p3 = by-assoc-and (under (X1) (CCX01) B18.proved) Eq.refl Eq.refl

p4 : X1 • X0 • X2 • CCX01 ≈ X0 • X1 • X2 • CCX01
p4 = by-assoc-and (under (ε) (X2 • CCX01) B44.proved) Eq.refl Eq.refl

p5 : X1 • X2 • X0 • CCX01 ≈ X0 • X1 • X2 • CCX01
p5 = trans p3 (trans p4 (refl))

p6 : CX12 • X1 • CCX01 • X0 ≈ CX12 • X1 • CCX01 • X0
p6 = refl

p7 : X0 • X1 • X2 • CCX01 ≈ CX12 • X1 • CCX01 • X0
p7 = trans (sym p5) (trans p2 p6)

p8 : CX12 • X1 • CCX01 • X0 ≈ X0 • X1 • X2 • CCX01
p8 = sym p7

proved : CX12 • X1 • CCX01 • X0 ≈ X0 • X1 • X2 • CCX01
proved = p8
