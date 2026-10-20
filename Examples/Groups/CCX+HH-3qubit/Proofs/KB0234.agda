{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Proofs.KB0234 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; X0 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0000 as B0
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0233 as B233

p0 : CX01 • X0 • CX01 • X0 • X0 ≈ X1 • X0
p0 = by-assoc-and (under (ε) (X0) B233.proved) Eq.refl Eq.refl

p1 : CX01 • X0 • CX01 • X0 • X0 ≈ CX01 • X0 • CX01
p1 = by-assoc-and (under (CX01 • X0 • CX01) (ε) B0.proved) Eq.refl Eq.refl

p2 : X1 • X0 ≈ CX01 • X0 • CX01
p2 = trans (sym p0) p1

p3 : X1 • X0 ≈ X1 • X0
p3 = refl

p4 : CX01 • X0 • CX01 ≈ CX01 • X0 • CX01
p4 = refl

p5 : X1 • X0 ≈ CX01 • X0 • CX01
p5 = trans (sym p3) (trans p2 p4)

p6 : CX01 • X0 • CX01 ≈ X1 • X0
p6 = sym p5

proved : CX01 • X0 • CX01 ≈ X1 • X0
proved = p6
