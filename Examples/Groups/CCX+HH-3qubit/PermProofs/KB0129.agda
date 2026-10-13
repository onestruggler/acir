{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0129 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0039 as B39

import Examples.Groups.CCX+HH-3qubit.Tietze.drel127 as Tdrel127
p0 : X0 • CCX02 ≈ CCX02 • CX21 • X0
p0 = Tdrel127.proved

p1 : X0 • CCX02 ≈ X0 • CCX02
p1 = refl

p2 : CCX02 • CX21 • X0 ≈ CX21 • CCX02 • X0
p2 = by-assoc-and (under (ε) (X0) B39.proved) Eq.refl Eq.refl

p3 : CCX02 • CX21 • X0 ≈ CX21 • CCX02 • X0
p3 = trans p2 (refl)

p4 : X0 • CCX02 ≈ CX21 • CCX02 • X0
p4 = trans (sym p1) (trans p0 p3)

p5 : CX21 • CCX02 • X0 ≈ X0 • CCX02
p5 = sym p4

proved : CX21 • CCX02 • X0 ≈ X0 • CCX02
proved = p5
