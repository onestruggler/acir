{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0115 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX10 ; X0 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0047 as B47

import Examples.Groups.CCX+HH-3qubit.Tietze.drel67 as Tdrel67
p0 : X1 • CX10 ≈ CX10 • X0 • X1
p0 = Tdrel67.proved

p1 : X1 • CX10 ≈ X1 • CX10
p1 = refl

p2 : CX10 • X0 • X1 ≈ X0 • CX10 • X1
p2 = by-assoc-and (under (ε) (X1) B47.proved) Eq.refl Eq.refl

p3 : CX10 • X0 • X1 ≈ X0 • CX10 • X1
p3 = trans p2 (refl)

p4 : X1 • CX10 ≈ X0 • CX10 • X1
p4 = trans (sym p1) (trans p0 p3)

p5 : X0 • CX10 • X1 ≈ X1 • CX10
p5 = sym p4

proved : X0 • CX10 • X1 ≈ X1 • CX10
proved = p5
