{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0965 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0028 as B28
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0035 as B35
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0216 as B216

p0 : CCX02 • CCX12 • CCX02 • X1 ≈ CX01 • CCX12 • CX01 • X1
p0 = by-assoc-and (under (ε) (X1) B216.proved) Eq.refl Eq.refl

p1 : CCX02 • CCX12 • CCX02 • X1 ≈ CCX02 • CCX12 • X1 • CCX02
p1 = by-assoc-and (under (CCX02 • CCX12) (ε) B28.proved) Eq.refl Eq.refl

p2 : CX01 • CCX12 • CX01 • X1 ≈ CCX02 • CCX12 • X1 • CCX02
p2 = trans (sym p0) p1

p3 : CX01 • CCX12 • CX01 • X1 ≈ CX01 • CCX12 • X1 • CX01
p3 = by-assoc-and (under (CX01 • CCX12) (ε) B35.proved) Eq.refl Eq.refl

p4 : CX01 • CCX12 • CX01 • X1 ≈ CX01 • CCX12 • X1 • CX01
p4 = trans p3 (refl)

p5 : CCX02 • CCX12 • X1 • CCX02 ≈ CCX02 • CCX12 • X1 • CCX02
p5 = refl

p6 : CX01 • CCX12 • X1 • CX01 ≈ CCX02 • CCX12 • X1 • CCX02
p6 = trans (sym p4) (trans p2 p5)

p7 : CCX02 • CCX12 • X1 • CCX02 ≈ CX01 • CCX12 • X1 • CX01
p7 = sym p6

proved : CCX02 • CCX12 • X1 • CCX02 ≈ CX01 • CCX12 • X1 • CX01
proved = p7
