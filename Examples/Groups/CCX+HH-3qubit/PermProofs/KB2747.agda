{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB2747 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0029 as B29
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0738 as B738

p0 : CCX01 • CCX12 • X1 • CCX01 • X2 ≈ CX02 • CCX12 • X1 • X2
p0 = by-assoc-and (under (ε) (X2) B738.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX12 • X1 • CCX01 • X2 ≈ CCX01 • CCX12 • X1 • X2 • CCX01
p1 = by-assoc-and (under (CCX01 • CCX12 • X1) (ε) B29.proved) Eq.refl Eq.refl

p2 : CX02 • CCX12 • X1 • X2 ≈ CCX01 • CCX12 • X1 • X2 • CCX01
p2 = trans (sym p0) p1

p3 : CX02 • CCX12 • X1 • X2 ≈ CX02 • CCX12 • X1 • X2
p3 = refl

p4 : CCX01 • CCX12 • X1 • X2 • CCX01 ≈ CCX01 • CCX12 • X1 • X2 • CCX01
p4 = refl

p5 : CX02 • CCX12 • X1 • X2 ≈ CCX01 • CCX12 • X1 • X2 • CCX01
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX01 • CCX12 • X1 • X2 • CCX01 ≈ CX02 • CCX12 • X1 • X2
p6 = sym p5

proved : CCX01 • CCX12 • X1 • X2 • CCX01 ≈ CX02 • CCX12 • X1 • X2
proved = p6
