{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0320 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0037 as B37
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0211 as B211

p0 : CCX01 • CCX01 • CCX12 • CCX01 ≈ CCX01 • CX02 • CCX12 • CX02
p0 = by-assoc-and (under (CCX01) (ε) B211.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX01 • CCX12 • CCX01 ≈ CCX12 • CCX01
p1 = by-assoc-and (under (ε) (CCX12 • CCX01) B11.proved) Eq.refl Eq.refl

p2 : CCX01 • CX02 • CCX12 • CX02 ≈ CCX12 • CCX01
p2 = trans (sym p0) p1

p3 : CCX01 • CX02 • CCX12 • CX02 ≈ CX02 • CCX01 • CCX12 • CX02
p3 = by-assoc-and (under (ε) (CCX12 • CX02) B37.proved) Eq.refl Eq.refl

p4 : CCX01 • CX02 • CCX12 • CX02 ≈ CX02 • CCX01 • CCX12 • CX02
p4 = trans p3 (refl)

p5 : CCX12 • CCX01 ≈ CCX12 • CCX01
p5 = refl

p6 : CX02 • CCX01 • CCX12 • CX02 ≈ CCX12 • CCX01
p6 = trans (sym p4) (trans p2 p5)

proved : CX02 • CCX01 • CCX12 • CX02 ≈ CCX12 • CCX01
proved = p6
