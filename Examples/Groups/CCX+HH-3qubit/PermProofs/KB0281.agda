{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0281 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CX01 ; CX02 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0119 as B119
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0122 as B122

p0 : X2 • CX01 • CCX02 • CX02 ≈ CCX02 • X2 • CX02
p0 = by-assoc-and (under (ε) (CX02) B122.proved) Eq.refl Eq.refl

p1 : X2 • CX01 • CCX02 • CX02 ≈ X2 • CX02 • CCX02
p1 = by-assoc-and (under (X2) (ε) B119.proved) Eq.refl Eq.refl

p2 : CCX02 • X2 • CX02 ≈ X2 • CX02 • CCX02
p2 = trans (sym p0) p1

p3 : CCX02 • X2 • CX02 ≈ CCX02 • X2 • CX02
p3 = refl

p4 : X2 • CX02 • CCX02 ≈ X2 • CX02 • CCX02
p4 = refl

p5 : CCX02 • X2 • CX02 ≈ X2 • CX02 • CCX02
p5 = trans (sym p3) (trans p2 p4)

proved : CCX02 • X2 • CX02 ≈ X2 • CX02 • CCX02
proved = p5
