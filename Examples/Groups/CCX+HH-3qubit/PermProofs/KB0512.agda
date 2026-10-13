{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0512 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0047 as B47
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0165 as B165

p0 : CX10 • X0 • CX21 • CCX02 ≈ CX10 • CCX02 • X0
p0 = by-assoc-and (under (CX10) (ε) B165.proved) Eq.refl Eq.refl

p1 : CX10 • X0 • CX21 • CCX02 ≈ X0 • CX10 • CX21 • CCX02
p1 = by-assoc-and (under (ε) (CX21 • CCX02) B47.proved) Eq.refl Eq.refl

p2 : CX10 • CCX02 • X0 ≈ X0 • CX10 • CX21 • CCX02
p2 = trans (sym p0) p1

p3 : CX10 • CCX02 • X0 ≈ CX10 • CCX02 • X0
p3 = refl

p4 : X0 • CX10 • CX21 • CCX02 ≈ X0 • CX10 • CX21 • CCX02
p4 = refl

p5 : CX10 • CCX02 • X0 ≈ X0 • CX10 • CX21 • CCX02
p5 = trans (sym p3) (trans p2 p4)

p6 : X0 • CX10 • CX21 • CCX02 ≈ CX10 • CCX02 • X0
p6 = sym p5

proved : X0 • CX10 • CX21 • CCX02 ≈ CX10 • CCX02 • X0
proved = p6
