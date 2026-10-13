{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0330 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0007 as B7
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0039 as B39
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0328 as B328

p0 : CX21 • CCX02 • CCX01 • CX21 • CX21 ≈ CCX01 • CCX02 • CX21
p0 = by-assoc-and (under (ε) (CX21) B328.proved) Eq.refl Eq.refl

p1 : CX21 • CCX02 • CCX01 • CX21 • CX21 ≈ CX21 • CCX02 • CCX01
p1 = by-assoc-and (under (CX21 • CCX02 • CCX01) (ε) B7.proved) Eq.refl Eq.refl

p2 : CCX01 • CCX02 • CX21 ≈ CX21 • CCX02 • CCX01
p2 = trans (sym p0) p1

p3 : CCX01 • CCX02 • CX21 ≈ CCX01 • CX21 • CCX02
p3 = by-assoc-and (under (CCX01) (ε) B39.proved) Eq.refl Eq.refl

p4 : CCX01 • CCX02 • CX21 ≈ CCX01 • CX21 • CCX02
p4 = trans p3 (refl)

p5 : CX21 • CCX02 • CCX01 ≈ CX21 • CCX02 • CCX01
p5 = refl

p6 : CCX01 • CX21 • CCX02 ≈ CX21 • CCX02 • CCX01
p6 = trans (sym p4) (trans p2 p5)

proved : CCX01 • CX21 • CCX02 ≈ CX21 • CCX02 • CCX01
proved = p6
