{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0139 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0035 as B35

import Examples.Groups.CCX+HH-3qubit.Tietze.drel162 as Tdrel162
p0 : X0 • CX01 ≈ CX01 • X1 • X0
p0 = Tdrel162.proved

p1 : X0 • CX01 ≈ X0 • CX01
p1 = refl

p2 : CX01 • X1 • X0 ≈ X1 • CX01 • X0
p2 = by-assoc-and (under (ε) (X0) B35.proved) Eq.refl Eq.refl

p3 : CX01 • X1 • X0 ≈ X1 • CX01 • X0
p3 = trans p2 (refl)

p4 : X0 • CX01 ≈ X1 • CX01 • X0
p4 = trans (sym p1) (trans p0 p3)

p5 : X1 • CX01 • X0 ≈ X0 • CX01
p5 = sym p4

proved : X1 • CX01 • X0 ≈ X0 • CX01
proved = p5
