{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0605 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX01 ; X0 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0139 as B139
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0282 as B282

p0 : CCX01 • X1 • CX01 • X0 ≈ X1 • CX01 • CCX01 • X0
p0 = by-assoc-and (under (ε) (X0) B282.proved) Eq.refl Eq.refl

p1 : CCX01 • X1 • CX01 • X0 ≈ CCX01 • X0 • CX01
p1 = by-assoc-and (under (CCX01) (ε) B139.proved) Eq.refl Eq.refl

p2 : X1 • CX01 • CCX01 • X0 ≈ CCX01 • X0 • CX01
p2 = trans (sym p0) p1

p3 : X1 • CX01 • CCX01 • X0 ≈ X1 • CX01 • CCX01 • X0
p3 = refl

p4 : CCX01 • X0 • CX01 ≈ CCX01 • X0 • CX01
p4 = refl

p5 : X1 • CX01 • CCX01 • X0 ≈ CCX01 • X0 • CX01
p5 = trans (sym p3) (trans p2 p4)

proved : X1 • CX01 • CCX01 • X0 ≈ CCX01 • X0 • CX01
proved = p5
