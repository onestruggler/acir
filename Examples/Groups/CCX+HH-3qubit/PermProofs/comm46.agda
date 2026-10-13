{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.comm46 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0003 as B3
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0023 as B23
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0150 as B150
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0186 as B186

p0 : X1 • CCX01 • X1 • CCX01 ≈ CX02 • CCX01 • CCX01
p0 = by-assoc-and (under (ε) (CCX01) B150.proved) Eq.refl Eq.refl

p1 : CX02 • CCX01 • CCX01 ≈ CX02
p1 = by-assoc-and (under (CX02) (ε) B11.proved) Eq.refl Eq.refl

p2 : X1 • CCX01 • X1 • CCX01 ≈ CX02
p2 = trans p0 (trans p1 (refl))

p3 : CCX01 • X1 • CCX01 • X1 ≈ X1 • CX02 • X1
p3 = by-assoc-and (under (ε) (X1) B186.proved) Eq.refl Eq.refl

p4 : X1 • CX02 • X1 ≈ X1 • X1 • CX02
p4 = by-assoc-and (under (X1) (ε) B23.proved) Eq.refl Eq.refl

p5 : X1 • X1 • CX02 ≈ CX02
p5 = by-assoc-and (under (ε) (CX02) B3.proved) Eq.refl Eq.refl

p6 : CCX01 • X1 • CCX01 • X1 ≈ CX02
p6 = trans p3 (trans p4 (trans p5 (refl)))

proved : X1 • CCX01 • X1 • CCX01 ≈ CCX01 • X1 • CCX01 • X1
proved = trans p2 (sym p6)
