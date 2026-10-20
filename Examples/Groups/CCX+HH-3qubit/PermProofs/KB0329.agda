{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0329 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX21 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0007 as B7
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0328 as B328

p0 : CX21 • CX21 • CCX02 • CCX01 • CX21 ≈ CX21 • CCX01 • CCX02
p0 = by-assoc-and (under (CX21) (ε) B328.proved) Eq.refl Eq.refl

p1 : CX21 • CX21 • CCX02 • CCX01 • CX21 ≈ CCX02 • CCX01 • CX21
p1 = by-assoc-and (under (ε) (CCX02 • CCX01 • CX21) B7.proved) Eq.refl Eq.refl

p2 : CX21 • CCX01 • CCX02 ≈ CCX02 • CCX01 • CX21
p2 = trans (sym p0) p1

p3 : CX21 • CCX01 • CCX02 ≈ CX21 • CCX01 • CCX02
p3 = refl

p4 : CCX02 • CCX01 • CX21 ≈ CCX02 • CCX01 • CX21
p4 = refl

p5 : CX21 • CCX01 • CCX02 ≈ CCX02 • CCX01 • CX21
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX02 • CCX01 • CX21 ≈ CX21 • CCX01 • CCX02
p6 = sym p5

proved : CCX02 • CCX01 • CX21 ≈ CX21 • CCX01 • CCX02
proved = p6
