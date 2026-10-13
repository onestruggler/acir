{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0193 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0010 as B10
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0165 as B165

p0 : X0 • CX21 • CCX02 • CCX02 ≈ CCX02 • X0 • CCX02
p0 = by-assoc-and (under (ε) (CCX02) B165.proved) Eq.refl Eq.refl

p1 : X0 • CX21 • CCX02 • CCX02 ≈ X0 • CX21
p1 = by-assoc-and (under (X0 • CX21) (ε) B10.proved) Eq.refl Eq.refl

p2 : CCX02 • X0 • CCX02 ≈ X0 • CX21
p2 = trans (sym p0) p1

p3 : CCX02 • X0 • CCX02 ≈ CCX02 • X0 • CCX02
p3 = refl

p4 : X0 • CX21 ≈ X0 • CX21
p4 = refl

p5 : CCX02 • X0 • CCX02 ≈ X0 • CX21
p5 = trans (sym p3) (trans p2 p4)

proved : CCX02 • X0 • CCX02 ≈ X0 • CX21
proved = p5
