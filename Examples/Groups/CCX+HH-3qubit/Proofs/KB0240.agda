{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Proofs.KB0240 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0074 as B74
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0238 as B238

p0 : X0 • CX01 • X1 • X1 ≈ CX01 • X0 • X1
p0 = by-assoc-and (under (ε) (X1) B238.proved) Eq.refl Eq.refl

p1 : X0 • CX01 • X1 • X1 ≈ X0 • CX01
p1 = by-assoc-and (under (X0 • CX01) (ε) B74.proved) Eq.refl Eq.refl

p2 : CX01 • X0 • X1 ≈ X0 • CX01
p2 = trans (sym p0) p1

p3 : CX01 • X0 • X1 ≈ CX01 • X0 • X1
p3 = refl

p4 : X0 • CX01 ≈ X0 • CX01
p4 = refl

p5 : CX01 • X0 • X1 ≈ X0 • CX01
p5 = trans (sym p3) (trans p2 p4)

proved : CX01 • X0 • X1 ≈ X0 • CX01
proved = p5
