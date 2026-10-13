{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB3403 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0129 as B129
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0399 as B399
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0504 as B504
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0759 as B759
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1322 as B1322

p0 : CX21 • CCX02 • X0 • CX12 • X1 • CX01 ≈ CX21 • CCX02 • CX12 • CX01 • X0
p0 = by-assoc-and (under (CX21 • CCX02) (ε) B399.proved) Eq.refl Eq.refl

p1 : CX21 • CCX02 • X0 • CX12 • X1 • CX01 ≈ X0 • CCX02 • CX12 • X1 • CX01
p1 = by-assoc-and (under (ε) (CX12 • X1 • CX01) B129.proved) Eq.refl Eq.refl

p2 : CX21 • CCX02 • CX12 • CX01 • X0 ≈ X0 • CCX02 • CX12 • X1 • CX01
p2 = trans (sym p0) p1

p3 : CX21 • CCX02 • CX12 • CX01 • X0 ≈ CX21 • CX02 • CCX02 • CX12 • X0
p3 = by-assoc-and (under (CX21) (X0) B504.proved) Eq.refl Eq.refl

p4 : CX21 • CX02 • CCX02 • CX12 • X0 ≈ CX21 • CX02 • CCX02 • X0 • CX12
p4 = by-assoc-and (under (CX21 • CX02 • CCX02) (ε) B45.proved) Eq.refl Eq.refl

p5 : CX21 • CX02 • CCX02 • X0 • CX12 ≈ CX01 • CX02 • X0 • CCX02 • CX12
p5 = by-assoc-and (under (ε) (CX12) B759.proved) Eq.refl Eq.refl

p6 : CX21 • CCX02 • CX12 • CX01 • X0 ≈ CX01 • CX02 • X0 • CCX02 • CX12
p6 = trans p3 (trans p4 (trans p5 (refl)))

p7 : X0 • CCX02 • CX12 • X1 • CX01 ≈ X0 • CX02 • CCX02 • CX12 • X1
p7 = by-assoc-and (under (X0) (ε) B1322.proved) Eq.refl Eq.refl

p8 : X0 • CCX02 • CX12 • X1 • CX01 ≈ X0 • CX02 • CCX02 • CX12 • X1
p8 = trans p7 (refl)

p9 : CX01 • CX02 • X0 • CCX02 • CX12 ≈ X0 • CX02 • CCX02 • CX12 • X1
p9 = trans (sym p6) (trans p2 p8)

proved : CX01 • CX02 • X0 • CCX02 • CX12 ≈ X0 • CX02 • CCX02 • CX12 • X1
proved = p9
