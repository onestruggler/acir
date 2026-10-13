{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1438 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0028 as B28
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0186 as B186
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0214 as B214
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1182 as B1182

p0 : CCX01 • CCX02 • CCX01 • X1 • CCX01 ≈ CX12 • CCX02 • CX12 • X1 • CCX01
p0 = by-assoc-and (under (ε) (X1 • CCX01) B214.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX02 • CCX01 • X1 • CCX01 ≈ CCX01 • CCX02 • X1 • CX02
p1 = by-assoc-and (under (CCX01 • CCX02) (ε) B186.proved) Eq.refl Eq.refl

p2 : CX12 • CCX02 • CX12 • X1 • CCX01 ≈ CCX01 • CCX02 • X1 • CX02
p2 = trans (sym p0) p1

p3 : CX12 • CCX02 • CX12 • X1 • CCX01 ≈ CX12 • CCX02 • CX12 • X1 • CCX01
p3 = refl

p4 : CCX01 • CCX02 • X1 • CX02 ≈ CCX01 • X1 • CCX02 • CX02
p4 = by-assoc-and (under (CCX01) (CX02) B28.proved) Eq.refl Eq.refl

p5 : CCX01 • X1 • CCX02 • CX02 ≈ X1 • CCX01 • CX01 • CCX02
p5 = by-assoc-and (under (ε) (ε) B1182.proved) Eq.refl Eq.refl

p6 : CCX01 • CCX02 • X1 • CX02 ≈ X1 • CCX01 • CX01 • CCX02
p6 = trans p4 (trans p5 (refl))

p7 : CX12 • CCX02 • CX12 • X1 • CCX01 ≈ X1 • CCX01 • CX01 • CCX02
p7 = trans (sym p3) (trans p2 p6)

proved : CX12 • CCX02 • CX12 • X1 • CCX01 ≈ X1 • CCX01 • CX01 • CCX02
proved = p7
