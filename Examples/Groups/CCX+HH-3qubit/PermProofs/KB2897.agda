{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB2897 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0149 as B149
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1250 as B1250

p0 : CCX01 • CCX12 • CX01 • CX02 • CCX02 ≈ CX02 • CCX12 • CCX01 • CX01 • CCX02
p0 = by-assoc-and (under (ε) (CCX02) B1250.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX12 • CX01 • CX02 • CCX02 ≈ CCX01 • CCX12 • CCX02 • CX02
p1 = by-assoc-and (under (CCX01 • CCX12) (ε) B149.proved) Eq.refl Eq.refl

p2 : CX02 • CCX12 • CCX01 • CX01 • CCX02 ≈ CCX01 • CCX12 • CCX02 • CX02
p2 = trans (sym p0) p1

p3 : CX02 • CCX12 • CCX01 • CX01 • CCX02 ≈ CX02 • CCX12 • CCX01 • CX01 • CCX02
p3 = refl

p4 : CCX01 • CCX12 • CCX02 • CX02 ≈ CCX01 • CCX12 • CCX02 • CX02
p4 = refl

p5 : CX02 • CCX12 • CCX01 • CX01 • CCX02 ≈ CCX01 • CCX12 • CCX02 • CX02
p5 = trans (sym p3) (trans p2 p4)

proved : CX02 • CCX12 • CCX01 • CX01 • CCX02 ≈ CCX01 • CCX12 • CCX02 • CX02
proved = p5
