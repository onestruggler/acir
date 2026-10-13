{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0161 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0125 as B125

p0 : X0 • X0 • X2 • CX02 ≈ X0 • CX02 • X0
p0 = by-assoc-and (under (X0) (ε) B125.proved) Eq.refl Eq.refl

p1 : X0 • X0 • X2 • CX02 ≈ X2 • CX02
p1 = by-assoc-and (under (ε) (X2 • CX02) B12.proved) Eq.refl Eq.refl

p2 : X0 • CX02 • X0 ≈ X2 • CX02
p2 = trans (sym p0) p1

p3 : X0 • CX02 • X0 ≈ X0 • CX02 • X0
p3 = refl

p4 : X2 • CX02 ≈ X2 • CX02
p4 = refl

p5 : X0 • CX02 • X0 ≈ X2 • CX02
p5 = trans (sym p3) (trans p2 p4)

proved : X0 • CX02 • X0 ≈ X2 • CX02
proved = p5
