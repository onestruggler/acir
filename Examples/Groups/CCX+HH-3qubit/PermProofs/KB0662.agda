{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0662 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0165 as B165
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0328 as B328

p0 : X0 • CX21 • CCX02 • CCX01 • CX21 ≈ X0 • CCX01 • CCX02
p0 = by-assoc-and (under (X0) (ε) B328.proved) Eq.refl Eq.refl

p1 : X0 • CX21 • CCX02 • CCX01 • CX21 ≈ CCX02 • X0 • CCX01 • CX21
p1 = by-assoc-and (under (ε) (CCX01 • CX21) B165.proved) Eq.refl Eq.refl

p2 : X0 • CCX01 • CCX02 ≈ CCX02 • X0 • CCX01 • CX21
p2 = trans (sym p0) p1

p3 : X0 • CCX01 • CCX02 ≈ X0 • CCX01 • CCX02
p3 = refl

p4 : CCX02 • X0 • CCX01 • CX21 ≈ CCX02 • X0 • CCX01 • CX21
p4 = refl

p5 : X0 • CCX01 • CCX02 ≈ CCX02 • X0 • CCX01 • CX21
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX02 • X0 • CCX01 • CX21 ≈ X0 • CCX01 • CCX02
p6 = sym p5

proved : CCX02 • X0 • CCX01 • CX21 ≈ X0 • CCX01 • CCX02
proved = p6
