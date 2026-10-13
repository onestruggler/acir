{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0119 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0038 as B38

import Examples.Groups.CCX+HH-3qubit.Tietze.drel95 as Tdrel95
p0 : CX02 • CCX02 ≈ CCX02 • CX01 • CX02
p0 = Tdrel95.proved

p1 : CX02 • CCX02 ≈ CX02 • CCX02
p1 = refl

p2 : CCX02 • CX01 • CX02 ≈ CX01 • CCX02 • CX02
p2 = by-assoc-and (under (ε) (CX02) B38.proved) Eq.refl Eq.refl

p3 : CCX02 • CX01 • CX02 ≈ CX01 • CCX02 • CX02
p3 = trans p2 (refl)

p4 : CX02 • CCX02 ≈ CX01 • CCX02 • CX02
p4 = trans (sym p1) (trans p0 p3)

p5 : CX01 • CCX02 • CX02 ≈ CX02 • CCX02
p5 = sym p4

proved : CX01 • CCX02 • CX02 ≈ CX02 • CCX02
proved = p5
