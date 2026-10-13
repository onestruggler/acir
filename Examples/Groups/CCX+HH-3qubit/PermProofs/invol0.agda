{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.invol0 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0003 as B3
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0120 as B120
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0150 as B150

p0 : X0 • X1 • CCX01 • X1 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X0 • CX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0
p0 = by-assoc-and (under (X0) (X0 • X0 • X1 • CCX01 • X1 • X0) B150.proved) Eq.refl Eq.refl

p1 : X0 • CX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X0 • CX02 • CCX01 • X1 • CCX01 • X1 • X0
p1 = by-assoc-and (under (X0 • CX02 • CCX01) (X1 • CCX01 • X1 • X0) B12.proved) Eq.refl Eq.refl

p2 : X0 • CX02 • CCX01 • X1 • CCX01 • X1 • X0 ≈ X0 • X1 • CCX01 • CCX01 • X1 • X0
p2 = by-assoc-and (under (X0) (CCX01 • X1 • X0) B120.proved) Eq.refl Eq.refl

p3 : X0 • X1 • CCX01 • CCX01 • X1 • X0 ≈ X0 • X1 • X1 • X0
p3 = by-assoc-and (under (X0 • X1) (X1 • X0) B11.proved) Eq.refl Eq.refl

p4 : X0 • X1 • X1 • X0 ≈ X0 • X0
p4 = by-assoc-and (under (X0) (X0) B3.proved) Eq.refl Eq.refl

p5 : X0 • X0 ≈ ε
p5 = by-assoc-and (under (ε) (ε) B12.proved) Eq.refl Eq.refl

p6 : X0 • X1 • CCX01 • X1 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ ε
p6 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (refl))))))

p7 : ε ≈ ε
p7 = refl

proved : X0 • X1 • CCX01 • X1 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ ε
proved = trans p6 (sym p7)
