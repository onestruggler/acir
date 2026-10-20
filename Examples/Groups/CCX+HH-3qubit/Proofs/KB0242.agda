{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Proofs.KB0242 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; X0 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0001 as B1
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0234 as B234
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0240 as B240

p0 : CX01 • CX01 • X0 • X1 ≈ CX01 • X0 • CX01
p0 = by-assoc-and (under (CX01) (ε) B240.proved) Eq.refl Eq.refl

p1 : CX01 • CX01 • X0 • X1 ≈ X0 • X1
p1 = by-assoc-and (under (ε) (X0 • X1) B1.proved) Eq.refl Eq.refl

p2 : CX01 • X0 • CX01 ≈ X0 • X1
p2 = trans (sym p0) p1

p3 : CX01 • X0 • CX01 ≈ X1 • X0
p3 = by-assoc-and (under (ε) (ε) B234.proved) Eq.refl Eq.refl

p4 : CX01 • X0 • CX01 ≈ X1 • X0
p4 = trans p3 (refl)

p5 : X0 • X1 ≈ X0 • X1
p5 = refl

p6 : X1 • X0 ≈ X0 • X1
p6 = trans (sym p4) (trans p2 p5)

proved : X1 • X0 ≈ X0 • X1
proved = p6
