{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1209 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0029 as B29
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0036 as B36
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0308 as B308

p0 : CCX02 • CX12 • CCX01 • X2 ≈ CX12 • CCX01 • CCX02 • X2
p0 = by-assoc-and (under (ε) (X2) B308.proved) Eq.refl Eq.refl

p1 : CCX02 • CX12 • CCX01 • X2 ≈ CCX02 • CX12 • X2 • CCX01
p1 = by-assoc-and (under (CCX02 • CX12) (ε) B29.proved) Eq.refl Eq.refl

p2 : CX12 • CCX01 • CCX02 • X2 ≈ CCX02 • CX12 • X2 • CCX01
p2 = trans (sym p0) p1

p3 : CX12 • CCX01 • CCX02 • X2 ≈ CX12 • CCX01 • CCX02 • X2
p3 = refl

p4 : CCX02 • CX12 • X2 • CCX01 ≈ CCX02 • X2 • CX12 • CCX01
p4 = by-assoc-and (under (CCX02) (CCX01) B36.proved) Eq.refl Eq.refl

p5 : CCX02 • CX12 • X2 • CCX01 ≈ CCX02 • X2 • CX12 • CCX01
p5 = trans p4 (refl)

p6 : CX12 • CCX01 • CCX02 • X2 ≈ CCX02 • X2 • CX12 • CCX01
p6 = trans (sym p3) (trans p2 p5)

p7 : CCX02 • X2 • CX12 • CCX01 ≈ CX12 • CCX01 • CCX02 • X2
p7 = sym p6

proved : CCX02 • X2 • CX12 • CCX01 ≈ CX12 • CCX01 • CCX02 • X2
proved = p7
