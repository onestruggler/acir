{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0047 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX10 ; X0 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r038 ; refl ; sym ; trans ; module Eq)
open K

p0 : X0 • CX10 ≈ CX10 • X0
p0 = by-assoc-and (axiom r038) Eq.refl Eq.refl

p1 : X0 • CX10 ≈ X0 • CX10
p1 = refl

p2 : CX10 • X0 ≈ CX10 • X0
p2 = refl

p3 : X0 • CX10 ≈ CX10 • X0
p3 = trans (sym p1) (trans p0 p2)

p4 : CX10 • X0 ≈ X0 • CX10
p4 = sym p3

proved : CX10 • X0 ≈ X0 • CX10
proved = p4
