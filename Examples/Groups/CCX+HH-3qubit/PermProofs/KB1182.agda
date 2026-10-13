{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1182 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0023 as B23
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0028 as B28
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0292 as B292
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0435 as B435

p0 : CCX01 • CCX02 • CX02 • X1 ≈ CX01 • CCX01 • CCX02 • X1
p0 = by-assoc-and (under (ε) (X1) B292.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX02 • CX02 • X1 ≈ CCX01 • CCX02 • X1 • CX02
p1 = by-assoc-and (under (CCX01 • CCX02) (ε) B23.proved) Eq.refl Eq.refl

p2 : CX01 • CCX01 • CCX02 • X1 ≈ CCX01 • CCX02 • X1 • CX02
p2 = trans (sym p0) p1

p3 : CX01 • CCX01 • CCX02 • X1 ≈ CX01 • CCX01 • X1 • CCX02
p3 = by-assoc-and (under (CX01 • CCX01) (ε) B28.proved) Eq.refl Eq.refl

p4 : CX01 • CCX01 • X1 • CCX02 ≈ X1 • CCX01 • CX01 • CCX02
p4 = by-assoc-and (under (ε) (CCX02) B435.proved) Eq.refl Eq.refl

p5 : CX01 • CCX01 • CCX02 • X1 ≈ X1 • CCX01 • CX01 • CCX02
p5 = trans p3 (trans p4 (refl))

p6 : CCX01 • CCX02 • X1 • CX02 ≈ CCX01 • X1 • CCX02 • CX02
p6 = by-assoc-and (under (CCX01) (CX02) B28.proved) Eq.refl Eq.refl

p7 : CCX01 • CCX02 • X1 • CX02 ≈ CCX01 • X1 • CCX02 • CX02
p7 = trans p6 (refl)

p8 : X1 • CCX01 • CX01 • CCX02 ≈ CCX01 • X1 • CCX02 • CX02
p8 = trans (sym p5) (trans p2 p7)

p9 : CCX01 • X1 • CCX02 • CX02 ≈ X1 • CCX01 • CX01 • CCX02
p9 = sym p8

proved : CCX01 • X1 • CCX02 • CX02 ≈ X1 • CCX01 • CX01 • CCX02
proved = p9
