{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB5463 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB2091 as B2091
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB2793 as B2793

p0 : X0 • X1 • X2 • CCX02 • CX02 • CCX01 ≈ CX01 • CX02 • X0 • CCX02 • CCX01
p0 = by-assoc-and (under (ε) (CCX01) B2793.proved) Eq.refl Eq.refl

p1 : X0 • X1 • X2 • CCX02 • CX02 • CCX01 ≈ X0 • X2 • CCX02 • CCX01 • X1
p1 = by-assoc-and (under (X0) (ε) B2091.proved) Eq.refl Eq.refl

p2 : CX01 • CX02 • X0 • CCX02 • CCX01 ≈ X0 • X2 • CCX02 • CCX01 • X1
p2 = trans (sym p0) p1

p3 : CX01 • CX02 • X0 • CCX02 • CCX01 ≈ CX01 • CX02 • X0 • CCX02 • CCX01
p3 = refl

p4 : X0 • X2 • CCX02 • CCX01 • X1 ≈ X0 • X2 • CCX02 • CCX01 • X1
p4 = refl

p5 : CX01 • CX02 • X0 • CCX02 • CCX01 ≈ X0 • X2 • CCX02 • CCX01 • X1
p5 = trans (sym p3) (trans p2 p4)

proved : CX01 • CX02 • X0 • CCX02 • CCX01 ≈ X0 • X2 • CCX02 • CCX01 • X1
proved = p5
