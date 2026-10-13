{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0177 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0009 as B9
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0136 as B136

p0 : CX21 • CCX02 • CX20 • CX20 ≈ CX20 • CCX02 • CX20
p0 = by-assoc-and (under (ε) (CX20) B136.proved) Eq.refl Eq.refl

p1 : CX21 • CCX02 • CX20 • CX20 ≈ CX21 • CCX02
p1 = by-assoc-and (under (CX21 • CCX02) (ε) B9.proved) Eq.refl Eq.refl

p2 : CX20 • CCX02 • CX20 ≈ CX21 • CCX02
p2 = trans (sym p0) p1

p3 : CX20 • CCX02 • CX20 ≈ CX20 • CCX02 • CX20
p3 = refl

p4 : CX21 • CCX02 ≈ CX21 • CCX02
p4 = refl

p5 : CX20 • CCX02 • CX20 ≈ CX21 • CCX02
p5 = trans (sym p3) (trans p2 p4)

proved : CX20 • CCX02 • CX20 ≈ CX21 • CCX02
proved = p5
