{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0921 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0190 as B190
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0192 as B192
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0846 as B846

p0 : CX01 • CX12 • CX01 • X0 • X1 ≈ CX02 • CX12 • X0 • X1
p0 = by-assoc-and (under (ε) (X0 • X1) B192.proved) Eq.refl Eq.refl

p1 : CX01 • CX12 • CX01 • X0 • X1 ≈ CX01 • CX12 • X0 • CX01
p1 = by-assoc-and (under (CX01 • CX12) (ε) B190.proved) Eq.refl Eq.refl

p2 : CX02 • CX12 • X0 • X1 ≈ CX01 • CX12 • X0 • CX01
p2 = trans (sym p0) p1

p3 : CX02 • CX12 • X0 • X1 ≈ CX02 • X0 • CX12 • X1
p3 = by-assoc-and (under (CX02) (X1) B45.proved) Eq.refl Eq.refl

p4 : CX02 • CX12 • X0 • X1 ≈ CX02 • X0 • CX12 • X1
p4 = trans p3 (refl)

p5 : CX01 • CX12 • X0 • CX01 ≈ CX01 • X0 • CX12 • CX01
p5 = by-assoc-and (under (CX01) (CX01) B45.proved) Eq.refl Eq.refl

p6 : CX01 • X0 • CX12 • CX01 ≈ X0 • X1 • CX02 • CX12
p6 = by-assoc-and (under (ε) (ε) B846.proved) Eq.refl Eq.refl

p7 : CX01 • CX12 • X0 • CX01 ≈ X0 • X1 • CX02 • CX12
p7 = trans p5 (trans p6 (refl))

p8 : CX02 • X0 • CX12 • X1 ≈ X0 • X1 • CX02 • CX12
p8 = trans (sym p4) (trans p2 p7)

proved : CX02 • X0 • CX12 • X1 ≈ X0 • X1 • CX02 • CX12
proved = p8
