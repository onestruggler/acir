{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0832 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX02 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0120 as B120
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0160 as B160
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0229 as B229

p0 : CX02 • X0 • CX02 • CCX01 • X1 ≈ X0 • X2 • CCX01 • X1
p0 = by-assoc-and (under (ε) (CCX01 • X1) B160.proved) Eq.refl Eq.refl

p1 : CX02 • X0 • CX02 • CCX01 • X1 ≈ CX02 • X0 • X1 • CCX01
p1 = by-assoc-and (under (CX02 • X0) (ε) B120.proved) Eq.refl Eq.refl

p2 : X0 • X2 • CCX01 • X1 ≈ CX02 • X0 • X1 • CCX01
p2 = trans (sym p0) p1

p3 : X0 • X2 • CCX01 • X1 ≈ X0 • X2 • CCX01 • X1
p3 = refl

p4 : CX02 • X0 • X1 • CCX01 ≈ X1 • CX02 • X0 • CCX01
p4 = by-assoc-and (under (ε) (CCX01) B229.proved) Eq.refl Eq.refl

p5 : CX02 • X0 • X1 • CCX01 ≈ X1 • CX02 • X0 • CCX01
p5 = trans p4 (refl)

p6 : X0 • X2 • CCX01 • X1 ≈ X1 • CX02 • X0 • CCX01
p6 = trans (sym p3) (trans p2 p5)

p7 : X1 • CX02 • X0 • CCX01 ≈ X0 • X2 • CCX01 • X1
p7 = sym p6

proved : X1 • CX02 • X0 • CCX01 ≈ X0 • X2 • CCX01 • X1
proved = p7
