{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0136 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0039 as B39

import Examples.Groups.CCX+HH-3qubit.Tietze.drel140 as Tdrel140
p0 : CX20 • CCX02 ≈ CCX02 • CX21 • CX20
p0 = Tdrel140.proved

p1 : CX20 • CCX02 ≈ CX20 • CCX02
p1 = refl

p2 : CCX02 • CX21 • CX20 ≈ CX21 • CCX02 • CX20
p2 = by-assoc-and (under (ε) (CX20) B39.proved) Eq.refl Eq.refl

p3 : CCX02 • CX21 • CX20 ≈ CX21 • CCX02 • CX20
p3 = trans p2 (refl)

p4 : CX20 • CCX02 ≈ CX21 • CCX02 • CX20
p4 = trans (sym p1) (trans p0 p3)

p5 : CX21 • CCX02 • CX20 ≈ CX20 • CCX02
p5 = sym p4

proved : CX21 • CCX02 • CX20 ≈ CX20 • CCX02
proved = p5
