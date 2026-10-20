{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0372 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CX01 ; CX02 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0033 as B33
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0119 as B119
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0130 as B130

p0 : CX01 • CCX02 • CX02 • X2 ≈ CX02 • CCX02 • X2
p0 = by-assoc-and (under (ε) (X2) B119.proved) Eq.refl Eq.refl

p1 : CX01 • CCX02 • CX02 • X2 ≈ CX01 • CCX02 • X2 • CX02
p1 = by-assoc-and (under (CX01 • CCX02) (ε) B33.proved) Eq.refl Eq.refl

p2 : CX02 • CCX02 • X2 ≈ CX01 • CCX02 • X2 • CX02
p2 = trans (sym p0) p1

p3 : CX02 • CCX02 • X2 ≈ CX02 • CCX02 • X2
p3 = refl

p4 : CX01 • CCX02 • X2 • CX02 ≈ X2 • CCX02 • CX02
p4 = by-assoc-and (under (ε) (CX02) B130.proved) Eq.refl Eq.refl

p5 : CX01 • CCX02 • X2 • CX02 ≈ X2 • CCX02 • CX02
p5 = trans p4 (refl)

p6 : CX02 • CCX02 • X2 ≈ X2 • CCX02 • CX02
p6 = trans (sym p3) (trans p2 p5)

proved : CX02 • CCX02 • X2 ≈ X2 • CCX02 • CX02
proved = p6
