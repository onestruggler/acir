{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0150 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0003 as B3
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0120 as B120

p0 : CX02 • CCX01 • X1 • X1 ≈ X1 • CCX01 • X1
p0 = by-assoc-and (under (ε) (X1) B120.proved) Eq.refl Eq.refl

p1 : CX02 • CCX01 • X1 • X1 ≈ CX02 • CCX01
p1 = by-assoc-and (under (CX02 • CCX01) (ε) B3.proved) Eq.refl Eq.refl

p2 : X1 • CCX01 • X1 ≈ CX02 • CCX01
p2 = trans (sym p0) p1

p3 : X1 • CCX01 • X1 ≈ X1 • CCX01 • X1
p3 = refl

p4 : CX02 • CCX01 ≈ CX02 • CCX01
p4 = refl

p5 : X1 • CCX01 • X1 ≈ CX02 • CCX01
p5 = trans (sym p3) (trans p2 p4)

proved : X1 • CCX01 • X1 ≈ CX02 • CCX01
proved = p5
