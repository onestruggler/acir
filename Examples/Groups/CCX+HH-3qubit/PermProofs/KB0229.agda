{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0229 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0023 as B23
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0044 as B44

p0 : CX02 • X1 • X0 ≈ CX02 • X0 • X1
p0 = by-assoc-and (under (CX02) (ε) B44.proved) Eq.refl Eq.refl

p1 : CX02 • X1 • X0 ≈ X1 • CX02 • X0
p1 = by-assoc-and (under (ε) (X0) B23.proved) Eq.refl Eq.refl

p2 : CX02 • X0 • X1 ≈ X1 • CX02 • X0
p2 = trans (sym p0) p1

p3 : CX02 • X0 • X1 ≈ CX02 • X0 • X1
p3 = refl

p4 : X1 • CX02 • X0 ≈ X1 • CX02 • X0
p4 = refl

p5 : CX02 • X0 • X1 ≈ X1 • CX02 • X0
p5 = trans (sym p3) (trans p2 p4)

proved : CX02 • X0 • X1 ≈ X1 • CX02 • X0
proved = p5
