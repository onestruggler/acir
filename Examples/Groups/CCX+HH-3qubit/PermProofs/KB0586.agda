{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0586 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0125 as B125
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0221 as B221

p0 : CX01 • X0 • X2 • CX02 ≈ X2 • CX01 • X0 • CX02
p0 = by-assoc-and (under (ε) (CX02) B221.proved) Eq.refl Eq.refl

p1 : CX01 • X0 • X2 • CX02 ≈ CX01 • CX02 • X0
p1 = by-assoc-and (under (CX01) (ε) B125.proved) Eq.refl Eq.refl

p2 : X2 • CX01 • X0 • CX02 ≈ CX01 • CX02 • X0
p2 = trans (sym p0) p1

p3 : X2 • CX01 • X0 • CX02 ≈ X2 • CX01 • X0 • CX02
p3 = refl

p4 : CX01 • CX02 • X0 ≈ CX01 • CX02 • X0
p4 = refl

p5 : X2 • CX01 • X0 • CX02 ≈ CX01 • CX02 • X0
p5 = trans (sym p3) (trans p2 p4)

proved : X2 • CX01 • X0 • CX02 ≈ CX01 • CX02 • X0
proved = p5
