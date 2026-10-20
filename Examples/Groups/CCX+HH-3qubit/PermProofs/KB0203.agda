{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0203 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX02 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0186 as B186

p0 : CCX01 • CCX01 • X1 • CCX01 ≈ CCX01 • X1 • CX02
p0 = by-assoc-and (under (CCX01) (ε) B186.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX01 • X1 • CCX01 ≈ X1 • CCX01
p1 = by-assoc-and (under (ε) (X1 • CCX01) B11.proved) Eq.refl Eq.refl

p2 : CCX01 • X1 • CX02 ≈ X1 • CCX01
p2 = trans (sym p0) p1

p3 : CCX01 • X1 • CX02 ≈ CCX01 • X1 • CX02
p3 = refl

p4 : X1 • CCX01 ≈ X1 • CCX01
p4 = refl

p5 : CCX01 • X1 • CX02 ≈ X1 • CCX01
p5 = trans (sym p3) (trans p2 p4)

proved : CCX01 • X1 • CX02 ≈ X1 • CCX01
proved = p5
