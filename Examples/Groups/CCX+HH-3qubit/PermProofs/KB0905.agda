{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0905 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CX01 ; CX21 ; X0 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0165 as B165
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0188 as B188

p0 : X0 • CX21 • CCX02 • X2 • CX01 ≈ X0 • CX21 • X2 • CCX02
p0 = by-assoc-and (under (X0 • CX21) (ε) B188.proved) Eq.refl Eq.refl

p1 : X0 • CX21 • CCX02 • X2 • CX01 ≈ CCX02 • X0 • X2 • CX01
p1 = by-assoc-and (under (ε) (X2 • CX01) B165.proved) Eq.refl Eq.refl

p2 : X0 • CX21 • X2 • CCX02 ≈ CCX02 • X0 • X2 • CX01
p2 = trans (sym p0) p1

p3 : X0 • CX21 • X2 • CCX02 ≈ X0 • CX21 • X2 • CCX02
p3 = refl

p4 : CCX02 • X0 • X2 • CX01 ≈ CCX02 • X0 • X2 • CX01
p4 = refl

p5 : X0 • CX21 • X2 • CCX02 ≈ CCX02 • X0 • X2 • CX01
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX02 • X0 • X2 • CX01 ≈ X0 • CX21 • X2 • CCX02
p6 = sym p5

proved : CCX02 • X0 • X2 • CX01 ≈ X0 • CX21 • X2 • CCX02
proved = p6
