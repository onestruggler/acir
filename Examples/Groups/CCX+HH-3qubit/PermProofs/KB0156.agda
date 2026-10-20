{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0156 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX01 ; CX02 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0123 as B123

p0 : CX01 • CX02 • CCX01 • CCX01 ≈ CCX01 • CX01 • CCX01
p0 = by-assoc-and (under (ε) (CCX01) B123.proved) Eq.refl Eq.refl

p1 : CX01 • CX02 • CCX01 • CCX01 ≈ CX01 • CX02
p1 = by-assoc-and (under (CX01 • CX02) (ε) B11.proved) Eq.refl Eq.refl

p2 : CCX01 • CX01 • CCX01 ≈ CX01 • CX02
p2 = trans (sym p0) p1

p3 : CCX01 • CX01 • CCX01 ≈ CCX01 • CX01 • CCX01
p3 = refl

p4 : CX01 • CX02 ≈ CX01 • CX02
p4 = refl

p5 : CCX01 • CX01 • CCX01 ≈ CX01 • CX02
p5 = trans (sym p3) (trans p2 p4)

proved : CCX01 • CX01 • CCX01 ≈ CX01 • CX02
proved = p5
