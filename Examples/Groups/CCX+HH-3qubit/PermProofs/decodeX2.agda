{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.decodeX2 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0003 as B3
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0019 as B19
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0023 as B23
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0150 as B150
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0161 as B161
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0475 as B475

p0 : X2 ≈ X2
p0 = refl

p1 : X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • CCX01 ≈ X0 • CX02 • CCX01 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • CCX01
p1 = by-assoc-and (under (X0) (X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • CCX01) B150.proved) Eq.refl Eq.refl

p2 : X0 • CX02 • CCX01 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • CCX01 ≈ X0 • CX02 • CCX01 • CCX01 • X0 • X1 • CCX01 • X1 • CCX01
p2 = by-assoc-and (under (X0 • CX02 • CCX01) (CCX01 • X0 • X1 • CCX01 • X1 • CCX01) B12.proved) Eq.refl Eq.refl

p3 : X0 • CX02 • CCX01 • CCX01 • X0 • X1 • CCX01 • X1 • CCX01 ≈ X0 • CX02 • X0 • X1 • CCX01 • X1 • CCX01
p3 = by-assoc-and (under (X0 • CX02) (X0 • X1 • CCX01 • X1 • CCX01) B11.proved) Eq.refl Eq.refl

p4 : X0 • CX02 • X0 • X1 • CCX01 • X1 • CCX01 ≈ X2 • CX02 • X1 • CCX01 • X1 • CCX01
p4 = by-assoc-and (under (ε) (X1 • CCX01 • X1 • CCX01) B161.proved) Eq.refl Eq.refl

p5 : X2 • CX02 • X1 • CCX01 • X1 • CCX01 ≈ X2 • X1 • CX02 • CCX01 • X1 • CCX01
p5 = by-assoc-and (under (X2) (CCX01 • X1 • CCX01) B23.proved) Eq.refl Eq.refl

p6 : X2 • X1 • CX02 • CCX01 • X1 • CCX01 ≈ X1 • X2 • CX02 • CCX01 • X1 • CCX01
p6 = by-assoc-and (under (ε) (CX02 • CCX01 • X1 • CCX01) B19.proved) Eq.refl Eq.refl

p7 : X1 • X2 • CX02 • CCX01 • X1 • CCX01 ≈ X2 • CCX01 • X1 • X1 • CCX01
p7 = by-assoc-and (under (ε) (X1 • CCX01) B475.proved) Eq.refl Eq.refl

p8 : X2 • CCX01 • X1 • X1 • CCX01 ≈ X2 • CCX01 • CCX01
p8 = by-assoc-and (under (X2 • CCX01) (CCX01) B3.proved) Eq.refl Eq.refl

p9 : X2 • CCX01 • CCX01 ≈ X2
p9 = by-assoc-and (under (X2) (ε) B11.proved) Eq.refl Eq.refl

p10 : X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • CCX01 ≈ X2
p10 = trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (refl)))))))))

proved : X2 ≈ X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 • X1 • CCX01 • X1 • CCX01
proved = trans p0 (sym p10)
