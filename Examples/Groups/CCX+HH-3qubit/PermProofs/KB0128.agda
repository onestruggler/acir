{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0128 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0033 as B33

import Examples.Groups.CCX+HH-3qubit.Tietze.drel126 as Tdrel126
p0 : X0 • CX02 ≈ CX02 • X2 • X0
p0 = Tdrel126.proved

p1 : X0 • CX02 ≈ X0 • CX02
p1 = refl

p2 : CX02 • X2 • X0 ≈ X2 • CX02 • X0
p2 = by-assoc-and (under (ε) (X0) B33.proved) Eq.refl Eq.refl

p3 : CX02 • X2 • X0 ≈ X2 • CX02 • X0
p3 = trans p2 (refl)

p4 : X0 • CX02 ≈ X2 • CX02 • X0
p4 = trans (sym p1) (trans p0 p3)

p5 : X2 • CX02 • X0 ≈ X0 • CX02
p5 = sym p4

proved : X2 • CX02 • X0 ≈ X0 • CX02
proved = p5
