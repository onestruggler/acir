{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0672 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0119 as B119
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0342 as B342

p0 : CCX12 • CX01 • CCX02 • CX02 ≈ CX01 • CCX02 • CCX12 • CX02
p0 = by-assoc-and (under (ε) (CX02) B342.proved) Eq.refl Eq.refl

p1 : CCX12 • CX01 • CCX02 • CX02 ≈ CCX12 • CX02 • CCX02
p1 = by-assoc-and (under (CCX12) (ε) B119.proved) Eq.refl Eq.refl

p2 : CX01 • CCX02 • CCX12 • CX02 ≈ CCX12 • CX02 • CCX02
p2 = trans (sym p0) p1

p3 : CX01 • CCX02 • CCX12 • CX02 ≈ CX01 • CCX02 • CCX12 • CX02
p3 = refl

p4 : CCX12 • CX02 • CCX02 ≈ CCX12 • CX02 • CCX02
p4 = refl

p5 : CX01 • CCX02 • CCX12 • CX02 ≈ CCX12 • CX02 • CCX02
p5 = trans (sym p3) (trans p2 p4)

proved : CX01 • CCX02 • CCX12 • CX02 ≈ CCX12 • CX02 • CCX02
proved = p5
