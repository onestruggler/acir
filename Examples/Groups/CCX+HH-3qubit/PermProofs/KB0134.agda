{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0134 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0025 as B25
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0030 as B30

import Examples.Groups.CCX+HH-3qubit.Tietze.drel134 as Tdrel134
p0 : CX02 • CX21 ≈ CX21 • CX02 • CX01
p0 = Tdrel134.proved

p1 : CX02 • CX21 ≈ CX02 • CX21
p1 = refl

p2 : CX21 • CX02 • CX01 ≈ CX21 • CX01 • CX02
p2 = by-assoc-and (under (CX21) (ε) B25.proved) Eq.refl Eq.refl

p3 : CX21 • CX01 • CX02 ≈ CX01 • CX21 • CX02
p3 = by-assoc-and (under (ε) (CX02) B30.proved) Eq.refl Eq.refl

p4 : CX21 • CX02 • CX01 ≈ CX01 • CX21 • CX02
p4 = trans p2 (trans p3 (refl))

p5 : CX02 • CX21 ≈ CX01 • CX21 • CX02
p5 = trans (sym p1) (trans p0 p4)

p6 : CX01 • CX21 • CX02 ≈ CX02 • CX21
p6 = sym p5

proved : CX01 • CX21 • CX02 ≈ CX02 • CX21
proved = p6
