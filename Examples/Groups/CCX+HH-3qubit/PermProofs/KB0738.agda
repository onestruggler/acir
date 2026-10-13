{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0738 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0708 as B708

p0 : CX02 • CCX12 • X1 • CCX01 • CCX01 ≈ CCX01 • CCX12 • X1 • CCX01
p0 = by-assoc-and (under (ε) (CCX01) B708.proved) Eq.refl Eq.refl

p1 : CX02 • CCX12 • X1 • CCX01 • CCX01 ≈ CX02 • CCX12 • X1
p1 = by-assoc-and (under (CX02 • CCX12 • X1) (ε) B11.proved) Eq.refl Eq.refl

p2 : CCX01 • CCX12 • X1 • CCX01 ≈ CX02 • CCX12 • X1
p2 = trans (sym p0) p1

p3 : CCX01 • CCX12 • X1 • CCX01 ≈ CCX01 • CCX12 • X1 • CCX01
p3 = refl

p4 : CX02 • CCX12 • X1 ≈ CX02 • CCX12 • X1
p4 = refl

p5 : CCX01 • CCX12 • X1 • CCX01 ≈ CX02 • CCX12 • X1
p5 = trans (sym p3) (trans p2 p4)

proved : CCX01 • CCX12 • X1 • CCX01 ≈ CX02 • CCX12 • X1
proved = p5
