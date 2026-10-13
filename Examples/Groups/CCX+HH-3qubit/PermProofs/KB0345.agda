{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0345 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0007 as B7
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0297 as B297
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0344 as B344

p0 : CX21 • CX21 • CX10 • CX21 ≈ CX21 • CX10 • CX20
p0 = by-assoc-and (under (CX21) (ε) B344.proved) Eq.refl Eq.refl

p1 : CX21 • CX21 • CX10 • CX21 ≈ CX10 • CX21
p1 = by-assoc-and (under (ε) (CX10 • CX21) B7.proved) Eq.refl Eq.refl

p2 : CX21 • CX10 • CX20 ≈ CX10 • CX21
p2 = trans (sym p0) p1

p3 : CX21 • CX10 • CX20 ≈ CX20 • CX21 • CX10
p3 = by-assoc-and (under (ε) (ε) B297.proved) Eq.refl Eq.refl

p4 : CX21 • CX10 • CX20 ≈ CX20 • CX21 • CX10
p4 = trans p3 (refl)

p5 : CX10 • CX21 ≈ CX10 • CX21
p5 = refl

p6 : CX20 • CX21 • CX10 ≈ CX10 • CX21
p6 = trans (sym p4) (trans p2 p5)

proved : CX20 • CX21 • CX10 ≈ CX10 • CX21
proved = p6
