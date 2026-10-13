{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0154 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0004 as B4
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0122 as B122

p0 : X2 • X2 • CX01 • CCX02 ≈ X2 • CCX02 • X2
p0 = by-assoc-and (under (X2) (ε) B122.proved) Eq.refl Eq.refl

p1 : X2 • X2 • CX01 • CCX02 ≈ CX01 • CCX02
p1 = by-assoc-and (under (ε) (CX01 • CCX02) B4.proved) Eq.refl Eq.refl

p2 : X2 • CCX02 • X2 ≈ CX01 • CCX02
p2 = trans (sym p0) p1

p3 : X2 • CCX02 • X2 ≈ X2 • CCX02 • X2
p3 = refl

p4 : CX01 • CCX02 ≈ CX01 • CCX02
p4 = refl

p5 : X2 • CCX02 • X2 ≈ CX01 • CCX02
p5 = trans (sym p3) (trans p2 p4)

proved : X2 • CCX02 • X2 ≈ CX01 • CCX02
proved = p5
