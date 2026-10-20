{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0835 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX01 ; CX02 ; X0 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0137 as B137
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0160 as B160

p0 : CX02 • X0 • CX02 • CCX01 • CX01 ≈ X0 • X2 • CCX01 • CX01
p0 = by-assoc-and (under (ε) (CCX01 • CX01) B160.proved) Eq.refl Eq.refl

p1 : CX02 • X0 • CX02 • CCX01 • CX01 ≈ CX02 • X0 • CX01 • CCX01
p1 = by-assoc-and (under (CX02 • X0) (ε) B137.proved) Eq.refl Eq.refl

p2 : X0 • X2 • CCX01 • CX01 ≈ CX02 • X0 • CX01 • CCX01
p2 = trans (sym p0) p1

p3 : X0 • X2 • CCX01 • CX01 ≈ X0 • X2 • CCX01 • CX01
p3 = refl

p4 : CX02 • X0 • CX01 • CCX01 ≈ CX02 • X0 • CX01 • CCX01
p4 = refl

p5 : X0 • X2 • CCX01 • CX01 ≈ CX02 • X0 • CX01 • CCX01
p5 = trans (sym p3) (trans p2 p4)

p6 : CX02 • X0 • CX01 • CCX01 ≈ X0 • X2 • CCX01 • CX01
p6 = sym p5

proved : CX02 • X0 • CX01 • CCX01 ≈ X0 • X2 • CCX01 • CX01
proved = p6
