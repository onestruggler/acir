{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0143 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX10 ; X0 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0115 as B115

p0 : X0 • X0 • CX10 • X1 ≈ X0 • X1 • CX10
p0 = by-assoc-and (under (X0) (ε) B115.proved) Eq.refl Eq.refl

p1 : X0 • X0 • CX10 • X1 ≈ CX10 • X1
p1 = by-assoc-and (under (ε) (CX10 • X1) B12.proved) Eq.refl Eq.refl

p2 : X0 • X1 • CX10 ≈ CX10 • X1
p2 = trans (sym p0) p1

p3 : X0 • X1 • CX10 ≈ X0 • X1 • CX10
p3 = refl

p4 : CX10 • X1 ≈ CX10 • X1
p4 = refl

p5 : X0 • X1 • CX10 ≈ CX10 • X1
p5 = trans (sym p3) (trans p2 p4)

proved : X0 • X1 • CX10 ≈ CX10 • X1
proved = p5
