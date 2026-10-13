{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0171 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0003 as B3
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0133 as B133

p0 : X1 • X1 • CX21 • X2 ≈ X1 • X2 • CX21
p0 = by-assoc-and (under (X1) (ε) B133.proved) Eq.refl Eq.refl

p1 : X1 • X1 • CX21 • X2 ≈ CX21 • X2
p1 = by-assoc-and (under (ε) (CX21 • X2) B3.proved) Eq.refl Eq.refl

p2 : X1 • X2 • CX21 ≈ CX21 • X2
p2 = trans (sym p0) p1

p3 : X1 • X2 • CX21 ≈ X1 • X2 • CX21
p3 = refl

p4 : CX21 • X2 ≈ CX21 • X2
p4 = refl

p5 : X1 • X2 • CX21 ≈ CX21 • X2
p5 = trans (sym p3) (trans p2 p4)

proved : X1 • X2 • CX21 ≈ CX21 • X2
proved = p5
