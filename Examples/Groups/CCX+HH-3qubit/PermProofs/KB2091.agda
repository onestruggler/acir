{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB2091 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0019 as B19
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0028 as B28
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0188 as B188
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0435 as B435
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0901 as B901

p0 : CCX02 • X2 • CX01 • CCX01 • X1 ≈ CCX02 • X2 • X1 • CCX01 • CX01
p0 = by-assoc-and (under (CCX02 • X2) (ε) B435.proved) Eq.refl Eq.refl

p1 : CCX02 • X2 • CX01 • CCX01 • X1 ≈ X2 • CCX02 • CCX01 • X1
p1 = by-assoc-and (under (ε) (CCX01 • X1) B188.proved) Eq.refl Eq.refl

p2 : CCX02 • X2 • X1 • CCX01 • CX01 ≈ X2 • CCX02 • CCX01 • X1
p2 = trans (sym p0) p1

p3 : CCX02 • X2 • X1 • CCX01 • CX01 ≈ CCX02 • X1 • X2 • CCX01 • CX01
p3 = by-assoc-and (under (CCX02) (CCX01 • CX01) B19.proved) Eq.refl Eq.refl

p4 : CCX02 • X1 • X2 • CCX01 • CX01 ≈ X1 • CCX02 • X2 • CCX01 • CX01
p4 = by-assoc-and (under (ε) (X2 • CCX01 • CX01) B28.proved) Eq.refl Eq.refl

p5 : X1 • CCX02 • X2 • CCX01 • CX01 ≈ X1 • X2 • CCX02 • CX02 • CCX01
p5 = by-assoc-and (under (X1) (ε) B901.proved) Eq.refl Eq.refl

p6 : CCX02 • X2 • X1 • CCX01 • CX01 ≈ X1 • X2 • CCX02 • CX02 • CCX01
p6 = trans p3 (trans p4 (trans p5 (refl)))

p7 : X2 • CCX02 • CCX01 • X1 ≈ X2 • CCX02 • CCX01 • X1
p7 = refl

p8 : X1 • X2 • CCX02 • CX02 • CCX01 ≈ X2 • CCX02 • CCX01 • X1
p8 = trans (sym p6) (trans p2 p7)

proved : X1 • X2 • CCX02 • CX02 • CCX01 ≈ X2 • CCX02 • CCX01 • X1
proved = p8
