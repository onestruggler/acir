{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0836 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0148 as B148
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0160 as B160
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0762 as B762

p0 : CX02 • CCX02 • CX02 • X0 • CX02 ≈ CX02 • CCX02 • X0 • X2
p0 = by-assoc-and (under (CX02 • CCX02) (ε) B160.proved) Eq.refl Eq.refl

p1 : CX02 • CCX02 • CX02 • X0 • CX02 ≈ CX01 • CCX02 • X0 • CX02
p1 = by-assoc-and (under (ε) (X0 • CX02) B148.proved) Eq.refl Eq.refl

p2 : CX02 • CCX02 • X0 • X2 ≈ CX01 • CCX02 • X0 • CX02
p2 = trans (sym p0) p1

p3 : CX02 • CCX02 • X0 • X2 ≈ CX02 • CCX02 • X0 • X2
p3 = refl

p4 : CX01 • CCX02 • X0 • CX02 ≈ X2 • CCX02 • CX02 • X0
p4 = by-assoc-and (under (ε) (ε) B762.proved) Eq.refl Eq.refl

p5 : CX01 • CCX02 • X0 • CX02 ≈ X2 • CCX02 • CX02 • X0
p5 = trans p4 (refl)

p6 : CX02 • CCX02 • X0 • X2 ≈ X2 • CCX02 • CX02 • X0
p6 = trans (sym p3) (trans p2 p5)

proved : CX02 • CCX02 • X0 • X2 ≈ X2 • CCX02 • CX02 • X0
proved = p6
