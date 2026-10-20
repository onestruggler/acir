{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0160 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX02 ; X0 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0008 as B8
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0125 as B125

p0 : X0 • X2 • CX02 • CX02 ≈ CX02 • X0 • CX02
p0 = by-assoc-and (under (ε) (CX02) B125.proved) Eq.refl Eq.refl

p1 : X0 • X2 • CX02 • CX02 ≈ X0 • X2
p1 = by-assoc-and (under (X0 • X2) (ε) B8.proved) Eq.refl Eq.refl

p2 : CX02 • X0 • CX02 ≈ X0 • X2
p2 = trans (sym p0) p1

p3 : CX02 • X0 • CX02 ≈ CX02 • X0 • CX02
p3 = refl

p4 : X0 • X2 ≈ X0 • X2
p4 = refl

p5 : CX02 • X0 • CX02 ≈ X0 • X2
p5 = trans (sym p3) (trans p2 p4)

proved : CX02 • X0 • CX02 ≈ X0 • X2
proved = p5
