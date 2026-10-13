{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.invol4 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0003 as B3
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0120 as B120
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0150 as B150

p0 : X1 • CCX01 • X1 • X1 • CCX01 • X1 ≈ CX02 • CCX01 • X1 • CCX01 • X1
p0 = by-assoc-and (under (ε) (X1 • CCX01 • X1) B150.proved) Eq.refl Eq.refl

p1 : CX02 • CCX01 • X1 • CCX01 • X1 ≈ X1 • CCX01 • CCX01 • X1
p1 = by-assoc-and (under (ε) (CCX01 • X1) B120.proved) Eq.refl Eq.refl

p2 : X1 • CCX01 • CCX01 • X1 ≈ X1 • X1
p2 = by-assoc-and (under (X1) (X1) B11.proved) Eq.refl Eq.refl

p3 : X1 • X1 ≈ ε
p3 = by-assoc-and (under (ε) (ε) B3.proved) Eq.refl Eq.refl

p4 : X1 • CCX01 • X1 • X1 • CCX01 • X1 ≈ ε
p4 = trans p0 (trans p1 (trans p2 (trans p3 (refl))))

p5 : ε ≈ ε
p5 = refl

proved : X1 • CCX01 • X1 • X1 • CCX01 • X1 ≈ ε
proved = trans p4 (sym p5)
