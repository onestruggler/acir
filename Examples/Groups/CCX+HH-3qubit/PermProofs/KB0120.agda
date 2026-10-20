{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0120 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX02 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0037 as B37

import Examples.Groups.CCX+HH-3qubit.Tietze.drel96 as Tdrel96
p0 : X1 • CCX01 ≈ CCX01 • CX02 • X1
p0 = Tdrel96.proved

p1 : X1 • CCX01 ≈ X1 • CCX01
p1 = refl

p2 : CCX01 • CX02 • X1 ≈ CX02 • CCX01 • X1
p2 = by-assoc-and (under (ε) (X1) B37.proved) Eq.refl Eq.refl

p3 : CCX01 • CX02 • X1 ≈ CX02 • CCX01 • X1
p3 = trans p2 (refl)

p4 : X1 • CCX01 ≈ CX02 • CCX01 • X1
p4 = trans (sym p1) (trans p0 p3)

p5 : CX02 • CCX01 • X1 ≈ X1 • CCX01
p5 = sym p4

proved : CX02 • CCX01 • X1 ≈ X1 • CCX01
proved = p5
