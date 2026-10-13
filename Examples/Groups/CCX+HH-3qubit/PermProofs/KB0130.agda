{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0130 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0038 as B38

import Examples.Groups.CCX+HH-3qubit.Tietze.drel129 as Tdrel129
p0 : X2 • CCX02 ≈ CCX02 • CX01 • X2
p0 = Tdrel129.proved

p1 : X2 • CCX02 ≈ X2 • CCX02
p1 = refl

p2 : CCX02 • CX01 • X2 ≈ CX01 • CCX02 • X2
p2 = by-assoc-and (under (ε) (X2) B38.proved) Eq.refl Eq.refl

p3 : CCX02 • CX01 • X2 ≈ CX01 • CCX02 • X2
p3 = trans p2 (refl)

p4 : X2 • CCX02 ≈ CX01 • CCX02 • X2
p4 = trans (sym p1) (trans p0 p3)

p5 : CX01 • CCX02 • X2 ≈ X2 • CCX02
p5 = sym p4

proved : CX01 • CCX02 • X2 ≈ X2 • CCX02
proved = p5
