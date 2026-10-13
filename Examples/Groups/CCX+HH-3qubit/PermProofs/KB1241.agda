{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1241 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0221 as B221
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0302 as B302
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0317 as B317

p0 : CX20 • CX01 • CX20 • X2 • CX20 ≈ CX20 • CX01 • X0 • X2
p0 = by-assoc-and (under (CX20 • CX01) (ε) B317.proved) Eq.refl Eq.refl

p1 : CX20 • CX01 • CX20 • X2 • CX20 ≈ CX01 • CX21 • X2 • CX20
p1 = by-assoc-and (under (ε) (X2 • CX20) B302.proved) Eq.refl Eq.refl

p2 : CX20 • CX01 • X0 • X2 ≈ CX01 • CX21 • X2 • CX20
p2 = trans (sym p0) p1

p3 : CX20 • CX01 • X0 • X2 ≈ CX20 • X2 • CX01 • X0
p3 = by-assoc-and (under (CX20) (ε) B221.proved) Eq.refl Eq.refl

p4 : CX20 • CX01 • X0 • X2 ≈ CX20 • X2 • CX01 • X0
p4 = trans p3 (refl)

p5 : CX01 • CX21 • X2 • CX20 ≈ CX01 • CX21 • X2 • CX20
p5 = refl

p6 : CX20 • X2 • CX01 • X0 ≈ CX01 • CX21 • X2 • CX20
p6 = trans (sym p4) (trans p2 p5)

proved : CX20 • X2 • CX01 • X0 ≈ CX01 • CX21 • X2 • CX20
proved = p6
