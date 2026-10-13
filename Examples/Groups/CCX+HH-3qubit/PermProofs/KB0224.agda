{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0224 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0019 as B19
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0029 as B29

p0 : CCX01 • X2 • X1 ≈ X2 • CCX01 • X1
p0 = by-assoc-and (under (ε) (X1) B29.proved) Eq.refl Eq.refl

p1 : CCX01 • X2 • X1 ≈ CCX01 • X1 • X2
p1 = by-assoc-and (under (CCX01) (ε) B19.proved) Eq.refl Eq.refl

p2 : X2 • CCX01 • X1 ≈ CCX01 • X1 • X2
p2 = trans (sym p0) p1

p3 : X2 • CCX01 • X1 ≈ X2 • CCX01 • X1
p3 = refl

p4 : CCX01 • X1 • X2 ≈ CCX01 • X1 • X2
p4 = refl

p5 : X2 • CCX01 • X1 ≈ CCX01 • X1 • X2
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX01 • X1 • X2 ≈ X2 • CCX01 • X1
p6 = sym p5

proved : CCX01 • X1 • X2 ≈ X2 • CCX01 • X1
proved = p6
