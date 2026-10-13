{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB4158 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0152 as B152
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0709 as B709

p0 : CX02 • CCX12 • CX01 • CCX01 • X0 • CCX01 ≈ CCX01 • CCX12 • CX01 • X0 • CCX01
p0 = by-assoc-and (under (ε) (X0 • CCX01) B709.proved) Eq.refl Eq.refl

p1 : CX02 • CCX12 • CX01 • CCX01 • X0 • CCX01 ≈ CX02 • CCX12 • CX01 • X0 • CX12
p1 = by-assoc-and (under (CX02 • CCX12 • CX01) (ε) B152.proved) Eq.refl Eq.refl

p2 : CCX01 • CCX12 • CX01 • X0 • CCX01 ≈ CX02 • CCX12 • CX01 • X0 • CX12
p2 = trans (sym p0) p1

p3 : CCX01 • CCX12 • CX01 • X0 • CCX01 ≈ CCX01 • CCX12 • CX01 • X0 • CCX01
p3 = refl

p4 : CX02 • CCX12 • CX01 • X0 • CX12 ≈ CX02 • CCX12 • CX01 • X0 • CX12
p4 = refl

p5 : CCX01 • CCX12 • CX01 • X0 • CCX01 ≈ CX02 • CCX12 • CX01 • X0 • CX12
p5 = trans (sym p3) (trans p2 p4)

proved : CCX01 • CCX12 • CX01 • X0 • CCX01 ≈ CX02 • CCX12 • CX01 • X0 • CX12
proved = p5
