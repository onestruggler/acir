{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0762 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CX01 ; CX02 ; X0 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0128 as B128
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0130 as B130

p0 : CX01 • CCX02 • X2 • CX02 • X0 ≈ X2 • CCX02 • CX02 • X0
p0 = by-assoc-and (under (ε) (CX02 • X0) B130.proved) Eq.refl Eq.refl

p1 : CX01 • CCX02 • X2 • CX02 • X0 ≈ CX01 • CCX02 • X0 • CX02
p1 = by-assoc-and (under (CX01 • CCX02) (ε) B128.proved) Eq.refl Eq.refl

p2 : X2 • CCX02 • CX02 • X0 ≈ CX01 • CCX02 • X0 • CX02
p2 = trans (sym p0) p1

p3 : X2 • CCX02 • CX02 • X0 ≈ X2 • CCX02 • CX02 • X0
p3 = refl

p4 : CX01 • CCX02 • X0 • CX02 ≈ CX01 • CCX02 • X0 • CX02
p4 = refl

p5 : X2 • CCX02 • CX02 • X0 ≈ CX01 • CCX02 • X0 • CX02
p5 = trans (sym p3) (trans p2 p4)

p6 : CX01 • CCX02 • X0 • CX02 ≈ X2 • CCX02 • CX02 • X0
p6 = sym p5

proved : CX01 • CCX02 • X0 • CX02 ≈ X2 • CCX02 • CX02 • X0
proved = p6
