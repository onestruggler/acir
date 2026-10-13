{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB5019 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0018 as B18
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1272 as B1272

p0 : CCX01 • CCX02 • X2 • CX12 • X0 ≈ CX12 • CCX02 • X2 • CCX01 • X0
p0 = by-assoc-and (under (ε) (X0) B1272.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX02 • X2 • CX12 • X0 ≈ CCX01 • CCX02 • X2 • X0 • CX12
p1 = by-assoc-and (under (CCX01 • CCX02 • X2) (ε) B45.proved) Eq.refl Eq.refl

p2 : CX12 • CCX02 • X2 • CCX01 • X0 ≈ CCX01 • CCX02 • X2 • X0 • CX12
p2 = trans (sym p0) p1

p3 : CX12 • CCX02 • X2 • CCX01 • X0 ≈ CX12 • CCX02 • X2 • CCX01 • X0
p3 = refl

p4 : CCX01 • CCX02 • X2 • X0 • CX12 ≈ CCX01 • CCX02 • X0 • X2 • CX12
p4 = by-assoc-and (under (CCX01 • CCX02) (CX12) B18.proved) Eq.refl Eq.refl

p5 : CCX01 • CCX02 • X2 • X0 • CX12 ≈ CCX01 • CCX02 • X0 • X2 • CX12
p5 = trans p4 (refl)

p6 : CX12 • CCX02 • X2 • CCX01 • X0 ≈ CCX01 • CCX02 • X0 • X2 • CX12
p6 = trans (sym p3) (trans p2 p5)

p7 : CCX01 • CCX02 • X0 • X2 • CX12 ≈ CX12 • CCX02 • X2 • CCX01 • X0
p7 = sym p6

proved : CCX01 • CCX02 • X0 • X2 • CX12 ≈ CX12 • CCX02 • X2 • CCX01 • X0
proved = p7
