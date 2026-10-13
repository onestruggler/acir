{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0173 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0008 as B8
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0134 as B134

p0 : CX01 • CX21 • CX02 • CX02 ≈ CX02 • CX21 • CX02
p0 = by-assoc-and (under (ε) (CX02) B134.proved) Eq.refl Eq.refl

p1 : CX01 • CX21 • CX02 • CX02 ≈ CX01 • CX21
p1 = by-assoc-and (under (CX01 • CX21) (ε) B8.proved) Eq.refl Eq.refl

p2 : CX02 • CX21 • CX02 ≈ CX01 • CX21
p2 = trans (sym p0) p1

p3 : CX02 • CX21 • CX02 ≈ CX02 • CX21 • CX02
p3 = refl

p4 : CX01 • CX21 ≈ CX01 • CX21
p4 = refl

p5 : CX02 • CX21 • CX02 ≈ CX01 • CX21
p5 = trans (sym p3) (trans p2 p4)

proved : CX02 • CX21 • CX02 ≈ CX01 • CX21
proved = p5
