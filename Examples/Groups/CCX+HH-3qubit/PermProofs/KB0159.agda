{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0159 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; X0 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0013 as B13
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0124 as B124

p0 : X0 • X1 • CX01 • CX01 ≈ CX01 • X0 • CX01
p0 = by-assoc-and (under (ε) (CX01) B124.proved) Eq.refl Eq.refl

p1 : X0 • X1 • CX01 • CX01 ≈ X0 • X1
p1 = by-assoc-and (under (X0 • X1) (ε) B13.proved) Eq.refl Eq.refl

p2 : CX01 • X0 • CX01 ≈ X0 • X1
p2 = trans (sym p0) p1

p3 : CX01 • X0 • CX01 ≈ CX01 • X0 • CX01
p3 = refl

p4 : X0 • X1 ≈ X0 • X1
p4 = refl

p5 : CX01 • X0 • CX01 ≈ X0 • X1
p5 = trans (sym p3) (trans p2 p4)

proved : CX01 • X0 • CX01 ≈ X0 • X1
proved = p5
