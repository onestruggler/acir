{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1431 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0126 as B126
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0149 as B149
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0213 as B213

p0 : CX01 • CX02 • CCX02 • CCX01 • CCX02 ≈ CX01 • CX02 • CX21 • CCX01 • CX21
p0 = by-assoc-and (under (CX01 • CX02) (ε) B213.proved) Eq.refl Eq.refl

p1 : CX01 • CX02 • CCX02 • CCX01 • CCX02 ≈ CCX02 • CX02 • CCX01 • CCX02
p1 = by-assoc-and (under (ε) (CCX01 • CCX02) B149.proved) Eq.refl Eq.refl

p2 : CX01 • CX02 • CX21 • CCX01 • CX21 ≈ CCX02 • CX02 • CCX01 • CCX02
p2 = trans (sym p0) p1

p3 : CX01 • CX02 • CX21 • CCX01 • CX21 ≈ CX21 • CX02 • CCX01 • CX21
p3 = by-assoc-and (under (ε) (CCX01 • CX21) B126.proved) Eq.refl Eq.refl

p4 : CX01 • CX02 • CX21 • CCX01 • CX21 ≈ CX21 • CX02 • CCX01 • CX21
p4 = trans p3 (refl)

p5 : CCX02 • CX02 • CCX01 • CCX02 ≈ CCX02 • CX02 • CCX01 • CCX02
p5 = refl

p6 : CX21 • CX02 • CCX01 • CX21 ≈ CCX02 • CX02 • CCX01 • CCX02
p6 = trans (sym p4) (trans p2 p5)

p7 : CCX02 • CX02 • CCX01 • CCX02 ≈ CX21 • CX02 • CCX01 • CX21
p7 = sym p6

proved : CCX02 • CX02 • CCX01 • CCX02 ≈ CX21 • CX02 • CCX01 • CX21
proved = p7
