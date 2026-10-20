{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.decodeCX02 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX02 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0150 as B150

p0 : CX02 ≈ CX02
p0 = refl

p1 : X1 • CCX01 • X1 • CCX01 ≈ CX02 • CCX01 • CCX01
p1 = by-assoc-and (under (ε) (CCX01) B150.proved) Eq.refl Eq.refl

p2 : CX02 • CCX01 • CCX01 ≈ CX02
p2 = by-assoc-and (under (CX02) (ε) B11.proved) Eq.refl Eq.refl

p3 : X1 • CCX01 • X1 • CCX01 ≈ CX02
p3 = trans p1 (trans p2 (refl))

proved : CX02 ≈ X1 • CCX01 • X1 • CCX01
proved = trans p0 (sym p3)
