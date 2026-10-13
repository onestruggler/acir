{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB2217 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0309 as B309
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0318 as B318
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0481 as B481

p0 : CX20 • X0 • X2 • CCX01 • X0 ≈ CX20 • X2 • CX12 • CCX01
p0 = by-assoc-and (under (CX20) (ε) B481.proved) Eq.refl Eq.refl

p1 : CX20 • X0 • X2 • CCX01 • X0 ≈ X0 • CX20 • X2 • CCX01 • X0
p1 = by-assoc-and (under (ε) (X2 • CCX01 • X0) B309.proved) Eq.refl Eq.refl

p2 : CX20 • X2 • CX12 • CCX01 ≈ X0 • CX20 • X2 • CCX01 • X0
p2 = trans (sym p0) p1

p3 : CX20 • X2 • CX12 • CCX01 ≈ CX20 • X2 • CX12 • CCX01
p3 = refl

p4 : X0 • CX20 • X2 • CCX01 • X0 ≈ X2 • CX20 • CCX01 • X0
p4 = by-assoc-and (under (ε) (CCX01 • X0) B318.proved) Eq.refl Eq.refl

p5 : X0 • CX20 • X2 • CCX01 • X0 ≈ X2 • CX20 • CCX01 • X0
p5 = trans p4 (refl)

p6 : CX20 • X2 • CX12 • CCX01 ≈ X2 • CX20 • CCX01 • X0
p6 = trans (sym p3) (trans p2 p5)

proved : CX20 • X2 • CX12 • CCX01 ≈ X2 • CX20 • CCX01 • X0
proved = p6
