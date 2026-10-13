{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB3121 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0020 as B20
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0043 as B43
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0259 as B259
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0260 as B260
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0291 as B291
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1097 as B1097

p0 : CCX01 • CX21 • CX02 • CX20 • X2 ≈ CX01 • CCX01 • CX21 • CX20 • X2
p0 = by-assoc-and (under (ε) (CX20 • X2) B291.proved) Eq.refl Eq.refl

p1 : CCX01 • CX21 • CX02 • CX20 • X2 ≈ CCX01 • CX21 • X0 • CX02 • CX20
p1 = by-assoc-and (under (CCX01 • CX21) (ε) B260.proved) Eq.refl Eq.refl

p2 : CX01 • CCX01 • CX21 • CX20 • X2 ≈ CCX01 • CX21 • X0 • CX02 • CX20
p2 = trans (sym p0) p1

p3 : CX01 • CCX01 • CX21 • CX20 • X2 ≈ CX01 • CCX01 • CX20 • CX21 • X2
p3 = by-assoc-and (under (CX01 • CCX01) (X2) B43.proved) Eq.refl Eq.refl

p4 : CX01 • CCX01 • CX21 • CX20 • X2 ≈ CX01 • CCX01 • CX20 • CX21 • X2
p4 = trans p3 (refl)

p5 : CCX01 • CX21 • X0 • CX02 • CX20 ≈ CCX01 • X0 • CX21 • CX02 • CX20
p5 = by-assoc-and (under (CCX01) (CX02 • CX20) B20.proved) Eq.refl Eq.refl

p6 : CCX01 • X0 • CX21 • CX02 • CX20 ≈ CCX01 • X0 • CX02 • CX20 • CX01
p6 = by-assoc-and (under (CCX01 • X0) (ε) B259.proved) Eq.refl Eq.refl

p7 : CCX01 • X0 • CX02 • CX20 • CX01 ≈ CX02 • CCX01 • CX20 • X2 • CX01
p7 = by-assoc-and (under (ε) (CX01) B1097.proved) Eq.refl Eq.refl

p8 : CCX01 • CX21 • X0 • CX02 • CX20 ≈ CX02 • CCX01 • CX20 • X2 • CX01
p8 = trans p5 (trans p6 (trans p7 (refl)))

p9 : CX01 • CCX01 • CX20 • CX21 • X2 ≈ CX02 • CCX01 • CX20 • X2 • CX01
p9 = trans (sym p4) (trans p2 p8)

p10 : CX02 • CCX01 • CX20 • X2 • CX01 ≈ CX01 • CCX01 • CX20 • CX21 • X2
p10 = sym p9

proved : CX02 • CCX01 • CX20 • X2 • CX01 ≈ CX01 • CCX01 • CX20 • CX21 • X2
proved = p10
