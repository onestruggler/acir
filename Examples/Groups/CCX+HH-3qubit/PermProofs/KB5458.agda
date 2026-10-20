{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB5458 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX01 ; CX02 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0390 as B390
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB2769 as B2769

p0 : X0 • X1 • X2 • CCX01 • CX01 • CCX02 ≈ CX01 • CX02 • X0 • CCX01 • CCX02
p0 = by-assoc-and (under (ε) (CCX02) B2769.proved) Eq.refl Eq.refl

p1 : X0 • X1 • X2 • CCX01 • CX01 • CCX02 ≈ X0 • X1 • CCX01 • CCX02 • X2
p1 = by-assoc-and (under (X0 • X1) (ε) B390.proved) Eq.refl Eq.refl

p2 : CX01 • CX02 • X0 • CCX01 • CCX02 ≈ X0 • X1 • CCX01 • CCX02 • X2
p2 = trans (sym p0) p1

p3 : CX01 • CX02 • X0 • CCX01 • CCX02 ≈ CX01 • CX02 • X0 • CCX01 • CCX02
p3 = refl

p4 : X0 • X1 • CCX01 • CCX02 • X2 ≈ X0 • X1 • CCX01 • CCX02 • X2
p4 = refl

p5 : CX01 • CX02 • X0 • CCX01 • CCX02 ≈ X0 • X1 • CCX01 • CCX02 • X2
p5 = trans (sym p3) (trans p2 p4)

proved : CX01 • CX02 • X0 • CCX01 • CCX02 ≈ X0 • X1 • CCX01 • CCX02 • X2
proved = p5
