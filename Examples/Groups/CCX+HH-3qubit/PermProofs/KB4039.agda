{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB4039 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0156 as B156
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0666 as B666
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3403 as B3403

p0 : CCX01 • CX01 • CCX01 • X0 • CCX02 • CX12 ≈ CCX01 • CX01 • X0 • CCX02 • CCX01
p0 = by-assoc-and (under (CCX01 • CX01) (ε) B666.proved) Eq.refl Eq.refl

p1 : CCX01 • CX01 • CCX01 • X0 • CCX02 • CX12 ≈ CX01 • CX02 • X0 • CCX02 • CX12
p1 = by-assoc-and (under (ε) (X0 • CCX02 • CX12) B156.proved) Eq.refl Eq.refl

p2 : CCX01 • CX01 • X0 • CCX02 • CCX01 ≈ CX01 • CX02 • X0 • CCX02 • CX12
p2 = trans (sym p0) p1

p3 : CCX01 • CX01 • X0 • CCX02 • CCX01 ≈ CCX01 • CX01 • X0 • CCX02 • CCX01
p3 = refl

p4 : CX01 • CX02 • X0 • CCX02 • CX12 ≈ X0 • CX02 • CCX02 • CX12 • X1
p4 = by-assoc-and (under (ε) (ε) B3403.proved) Eq.refl Eq.refl

p5 : CX01 • CX02 • X0 • CCX02 • CX12 ≈ X0 • CX02 • CCX02 • CX12 • X1
p5 = trans p4 (refl)

p6 : CCX01 • CX01 • X0 • CCX02 • CCX01 ≈ X0 • CX02 • CCX02 • CX12 • X1
p6 = trans (sym p3) (trans p2 p5)

proved : CCX01 • CX01 • X0 • CCX02 • CCX01 ≈ X0 • CX02 • CCX02 • CX12 • X1
proved = p6
