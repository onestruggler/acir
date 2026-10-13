{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1605 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0020 as B20
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0191 as B191
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0291 as B291

p0 : CCX01 • CX21 • CX02 • X0 • X2 ≈ CX01 • CCX01 • CX21 • X0 • X2
p0 = by-assoc-and (under (ε) (X0 • X2) B291.proved) Eq.refl Eq.refl

p1 : CCX01 • CX21 • CX02 • X0 • X2 ≈ CCX01 • CX21 • X0 • CX02
p1 = by-assoc-and (under (CCX01 • CX21) (ε) B191.proved) Eq.refl Eq.refl

p2 : CX01 • CCX01 • CX21 • X0 • X2 ≈ CCX01 • CX21 • X0 • CX02
p2 = trans (sym p0) p1

p3 : CX01 • CCX01 • CX21 • X0 • X2 ≈ CX01 • CCX01 • X0 • CX21 • X2
p3 = by-assoc-and (under (CX01 • CCX01) (X2) B20.proved) Eq.refl Eq.refl

p4 : CX01 • CCX01 • CX21 • X0 • X2 ≈ CX01 • CCX01 • X0 • CX21 • X2
p4 = trans p3 (refl)

p5 : CCX01 • CX21 • X0 • CX02 ≈ CCX01 • X0 • CX21 • CX02
p5 = by-assoc-and (under (CCX01) (CX02) B20.proved) Eq.refl Eq.refl

p6 : CCX01 • CX21 • X0 • CX02 ≈ CCX01 • X0 • CX21 • CX02
p6 = trans p5 (refl)

p7 : CX01 • CCX01 • X0 • CX21 • X2 ≈ CCX01 • X0 • CX21 • CX02
p7 = trans (sym p4) (trans p2 p6)

proved : CX01 • CCX01 • X0 • CX21 • X2 ≈ CCX01 • X0 • CX21 • CX02
proved = p7
