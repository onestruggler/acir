{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0133 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0034 as B34

import Examples.Groups.CCX+HH-3qubit.Tietze.drel133 as Tdrel133
p0 : X2 • CX21 ≈ CX21 • X1 • X2
p0 = Tdrel133.proved

p1 : X2 • CX21 ≈ X2 • CX21
p1 = refl

p2 : CX21 • X1 • X2 ≈ X1 • CX21 • X2
p2 = by-assoc-and (under (ε) (X2) B34.proved) Eq.refl Eq.refl

p3 : CX21 • X1 • X2 ≈ X1 • CX21 • X2
p3 = trans p2 (refl)

p4 : X2 • CX21 ≈ X1 • CX21 • X2
p4 = trans (sym p1) (trans p0 p3)

p5 : X1 • CX21 • X2 ≈ X2 • CX21
p5 = sym p4

proved : X1 • CX21 • X2 ≈ X2 • CX21
proved = p5
