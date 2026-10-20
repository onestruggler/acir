{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0190 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; X0 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0013 as B13
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0159 as B159

p0 : CX01 • CX01 • X0 • CX01 ≈ CX01 • X0 • X1
p0 = by-assoc-and (under (CX01) (ε) B159.proved) Eq.refl Eq.refl

p1 : CX01 • CX01 • X0 • CX01 ≈ X0 • CX01
p1 = by-assoc-and (under (ε) (X0 • CX01) B13.proved) Eq.refl Eq.refl

p2 : CX01 • X0 • X1 ≈ X0 • CX01
p2 = trans (sym p0) p1

p3 : CX01 • X0 • X1 ≈ CX01 • X0 • X1
p3 = refl

p4 : X0 • CX01 ≈ X0 • CX01
p4 = refl

p5 : CX01 • X0 • X1 ≈ X0 • CX01
p5 = trans (sym p3) (trans p2 p4)

proved : CX01 • X0 • X1 ≈ X0 • CX01
proved = p5
