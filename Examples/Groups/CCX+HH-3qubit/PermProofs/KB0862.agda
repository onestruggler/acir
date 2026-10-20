{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0862 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX02 ; CX21 ; X0 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0125 as B125
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0173 as B173
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0834 as B834

p0 : X0 • X2 • CX02 • CX21 • CX02 ≈ X0 • X2 • CX01 • CX21
p0 = by-assoc-and (under (X0 • X2) (ε) B173.proved) Eq.refl Eq.refl

p1 : X0 • X2 • CX02 • CX21 • CX02 ≈ CX02 • X0 • CX21 • CX02
p1 = by-assoc-and (under (ε) (CX21 • CX02) B125.proved) Eq.refl Eq.refl

p2 : X0 • X2 • CX01 • CX21 ≈ CX02 • X0 • CX21 • CX02
p2 = trans (sym p0) p1

p3 : X0 • X2 • CX01 • CX21 ≈ X0 • X2 • CX01 • CX21
p3 = refl

p4 : CX02 • X0 • CX21 • CX02 ≈ CX01 • X0 • CX21 • X2
p4 = by-assoc-and (under (ε) (ε) B834.proved) Eq.refl Eq.refl

p5 : CX02 • X0 • CX21 • CX02 ≈ CX01 • X0 • CX21 • X2
p5 = trans p4 (refl)

p6 : X0 • X2 • CX01 • CX21 ≈ CX01 • X0 • CX21 • X2
p6 = trans (sym p3) (trans p2 p5)

p7 : CX01 • X0 • CX21 • X2 ≈ X0 • X2 • CX01 • CX21
p7 = sym p6

proved : CX01 • X0 • CX21 • X2 ≈ X0 • X2 • CX01 • CX21
proved = p7
