{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0191 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0008 as B8
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0160 as B160

p0 : CX02 • CX02 • X0 • CX02 ≈ CX02 • X0 • X2
p0 = by-assoc-and (under (CX02) (ε) B160.proved) Eq.refl Eq.refl

p1 : CX02 • CX02 • X0 • CX02 ≈ X0 • CX02
p1 = by-assoc-and (under (ε) (X0 • CX02) B8.proved) Eq.refl Eq.refl

p2 : CX02 • X0 • X2 ≈ X0 • CX02
p2 = trans (sym p0) p1

p3 : CX02 • X0 • X2 ≈ CX02 • X0 • X2
p3 = refl

p4 : X0 • CX02 ≈ X0 • CX02
p4 = refl

p5 : CX02 • X0 • X2 ≈ X0 • CX02
p5 = trans (sym p3) (trans p2 p4)

proved : CX02 • X0 • X2 ≈ X0 • CX02
proved = p5
