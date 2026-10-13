{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0297 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0043 as B43
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0210 as B210

p0 : CX21 • CX20 • CX10 ≈ CX21 • CX10 • CX20
p0 = by-assoc-and (under (CX21) (ε) B210.proved) Eq.refl Eq.refl

p1 : CX21 • CX20 • CX10 ≈ CX20 • CX21 • CX10
p1 = by-assoc-and (under (ε) (CX10) B43.proved) Eq.refl Eq.refl

p2 : CX21 • CX10 • CX20 ≈ CX20 • CX21 • CX10
p2 = trans (sym p0) p1

p3 : CX21 • CX10 • CX20 ≈ CX21 • CX10 • CX20
p3 = refl

p4 : CX20 • CX21 • CX10 ≈ CX20 • CX21 • CX10
p4 = refl

p5 : CX21 • CX10 • CX20 ≈ CX20 • CX21 • CX10
p5 = trans (sym p3) (trans p2 p4)

proved : CX21 • CX10 • CX20 ≈ CX20 • CX21 • CX10
proved = p5
