{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB4082 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0159 as B159
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0672 as B672

p0 : CX01 • X0 • CX01 • CCX02 • CCX12 • CX02 ≈ CX01 • X0 • CCX12 • CX02 • CCX02
p0 = by-assoc-and (under (CX01 • X0) (ε) B672.proved) Eq.refl Eq.refl

p1 : CX01 • X0 • CX01 • CCX02 • CCX12 • CX02 ≈ X0 • X1 • CCX02 • CCX12 • CX02
p1 = by-assoc-and (under (ε) (CCX02 • CCX12 • CX02) B159.proved) Eq.refl Eq.refl

p2 : CX01 • X0 • CCX12 • CX02 • CCX02 ≈ X0 • X1 • CCX02 • CCX12 • CX02
p2 = trans (sym p0) p1

p3 : CX01 • X0 • CCX12 • CX02 • CCX02 ≈ CX01 • X0 • CCX12 • CX02 • CCX02
p3 = refl

p4 : X0 • X1 • CCX02 • CCX12 • CX02 ≈ X0 • X1 • CCX02 • CCX12 • CX02
p4 = refl

p5 : CX01 • X0 • CCX12 • CX02 • CCX02 ≈ X0 • X1 • CCX02 • CCX12 • CX02
p5 = trans (sym p3) (trans p2 p4)

proved : CX01 • X0 • CCX12 • CX02 • CCX02 ≈ X0 • X1 • CCX02 • CCX12 • CX02
proved = p5
