{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0282 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX01 ; CX02 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0035 as B35
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0120 as B120
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0123 as B123

p0 : CX01 • CX02 • CCX01 • X1 ≈ CCX01 • CX01 • X1
p0 = by-assoc-and (under (ε) (X1) B123.proved) Eq.refl Eq.refl

p1 : CX01 • CX02 • CCX01 • X1 ≈ CX01 • X1 • CCX01
p1 = by-assoc-and (under (CX01) (ε) B120.proved) Eq.refl Eq.refl

p2 : CCX01 • CX01 • X1 ≈ CX01 • X1 • CCX01
p2 = trans (sym p0) p1

p3 : CCX01 • CX01 • X1 ≈ CCX01 • X1 • CX01
p3 = by-assoc-and (under (CCX01) (ε) B35.proved) Eq.refl Eq.refl

p4 : CCX01 • CX01 • X1 ≈ CCX01 • X1 • CX01
p4 = trans p3 (refl)

p5 : CX01 • X1 • CCX01 ≈ X1 • CX01 • CCX01
p5 = by-assoc-and (under (ε) (CCX01) B35.proved) Eq.refl Eq.refl

p6 : CX01 • X1 • CCX01 ≈ X1 • CX01 • CCX01
p6 = trans p5 (refl)

p7 : CCX01 • X1 • CX01 ≈ X1 • CX01 • CCX01
p7 = trans (sym p4) (trans p2 p6)

proved : CCX01 • X1 • CX01 ≈ X1 • CX01 • CCX01
proved = p7
