{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0416 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0029 as B29
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0037 as B37
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0128 as B128

p0 : CCX01 • X2 • CX02 • X0 ≈ CCX01 • X0 • CX02
p0 = by-assoc-and (under (CCX01) (ε) B128.proved) Eq.refl Eq.refl

p1 : CCX01 • X2 • CX02 • X0 ≈ X2 • CCX01 • CX02 • X0
p1 = by-assoc-and (under (ε) (CX02 • X0) B29.proved) Eq.refl Eq.refl

p2 : CCX01 • X0 • CX02 ≈ X2 • CCX01 • CX02 • X0
p2 = trans (sym p0) p1

p3 : CCX01 • X0 • CX02 ≈ CCX01 • X0 • CX02
p3 = refl

p4 : X2 • CCX01 • CX02 • X0 ≈ X2 • CX02 • CCX01 • X0
p4 = by-assoc-and (under (X2) (X0) B37.proved) Eq.refl Eq.refl

p5 : X2 • CCX01 • CX02 • X0 ≈ X2 • CX02 • CCX01 • X0
p5 = trans p4 (refl)

p6 : CCX01 • X0 • CX02 ≈ X2 • CX02 • CCX01 • X0
p6 = trans (sym p3) (trans p2 p5)

p7 : X2 • CX02 • CCX01 • X0 ≈ CCX01 • X0 • CX02
p7 = sym p6

proved : X2 • CX02 • CCX01 • X0 ≈ CCX01 • X0 • CX02
proved = p7
