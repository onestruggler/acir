{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0429 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0038 as B38
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0039 as B39
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0134 as B134
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0371 as B371

p0 : CCX02 • CX01 • CX21 • CX02 ≈ CCX02 • CX02 • CX21
p0 = by-assoc-and (under (CCX02) (ε) B134.proved) Eq.refl Eq.refl

p1 : CCX02 • CX01 • CX21 • CX02 ≈ CX01 • CCX02 • CX21 • CX02
p1 = by-assoc-and (under (ε) (CX21 • CX02) B38.proved) Eq.refl Eq.refl

p2 : CCX02 • CX02 • CX21 ≈ CX01 • CCX02 • CX21 • CX02
p2 = trans (sym p0) p1

p3 : CCX02 • CX02 • CX21 ≈ CCX02 • CX02 • CX21
p3 = refl

p4 : CX01 • CCX02 • CX21 • CX02 ≈ CX01 • CX21 • CCX02 • CX02
p4 = by-assoc-and (under (CX01) (CX02) B39.proved) Eq.refl Eq.refl

p5 : CX01 • CX21 • CCX02 • CX02 ≈ CX21 • CX02 • CCX02
p5 = by-assoc-and (under (ε) (ε) B371.proved) Eq.refl Eq.refl

p6 : CX01 • CCX02 • CX21 • CX02 ≈ CX21 • CX02 • CCX02
p6 = trans p4 (trans p5 (refl))

p7 : CCX02 • CX02 • CX21 ≈ CX21 • CX02 • CCX02
p7 = trans (sym p3) (trans p2 p6)

proved : CCX02 • CX02 • CX21 ≈ CX21 • CX02 • CCX02
proved = p7
