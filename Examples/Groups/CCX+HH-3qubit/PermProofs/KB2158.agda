{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB2158 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0029 as B29
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0031 as B31
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0282 as B282
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0394 as B394
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0460 as B460
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0819 as B819
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0831 as B831

p0 : CCX01 • X1 • CX01 • CX12 • X1 ≈ CCX01 • X2 • CX01 • CX12
p0 = by-assoc-and (under (CCX01) (ε) B460.proved) Eq.refl Eq.refl

p1 : CCX01 • X1 • CX01 • CX12 • X1 ≈ X1 • CX01 • CCX01 • CX12 • X1
p1 = by-assoc-and (under (ε) (CX12 • X1) B282.proved) Eq.refl Eq.refl

p2 : CCX01 • X2 • CX01 • CX12 ≈ X1 • CX01 • CCX01 • CX12 • X1
p2 = trans (sym p0) p1

p3 : CCX01 • X2 • CX01 • CX12 ≈ X2 • CCX01 • CX01 • CX12
p3 = by-assoc-and (under (ε) (CX01 • CX12) B29.proved) Eq.refl Eq.refl

p4 : X2 • CCX01 • CX01 • CX12 ≈ X2 • CX12 • CX01 • CCX01
p4 = by-assoc-and (under (X2) (ε) B394.proved) Eq.refl Eq.refl

p5 : CCX01 • X2 • CX01 • CX12 ≈ X2 • CX12 • CX01 • CCX01
p5 = trans p3 (trans p4 (refl))

p6 : X1 • CX01 • CCX01 • CX12 • X1 ≈ X1 • CX01 • CX12 • CCX01 • X1
p6 = by-assoc-and (under (X1 • CX01) (X1) B31.proved) Eq.refl Eq.refl

p7 : X1 • CX01 • CX12 • CCX01 • X1 ≈ X0 • CX01 • CCX01 • X0 • X1
p7 = by-assoc-and (under (ε) (X1) B819.proved) Eq.refl Eq.refl

p8 : X0 • CX01 • CCX01 • X0 • X1 ≈ X0 • X1 • CCX01 • CX01 • X0
p8 = by-assoc-and (under (X0) (ε) B831.proved) Eq.refl Eq.refl

p9 : X1 • CX01 • CCX01 • CX12 • X1 ≈ X0 • X1 • CCX01 • CX01 • X0
p9 = trans p6 (trans p7 (trans p8 (refl)))

p10 : X2 • CX12 • CX01 • CCX01 ≈ X0 • X1 • CCX01 • CX01 • X0
p10 = trans (sym p5) (trans p2 p9)

p11 : X0 • X1 • CCX01 • CX01 • X0 ≈ X2 • CX12 • CX01 • CCX01
p11 = sym p10

proved : X0 • X1 • CCX01 • CX01 • X0 ≈ X2 • CX12 • CX01 • CCX01
proved = p11
