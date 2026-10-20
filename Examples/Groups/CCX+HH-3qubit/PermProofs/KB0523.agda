{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0523 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX12 ; CX02 ; CX10 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0033 as B33
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0168 as B168

p0 : CX02 • X2 • CX10 • CCX12 ≈ CX02 • CCX12 • X2
p0 = by-assoc-and (under (CX02) (ε) B168.proved) Eq.refl Eq.refl

p1 : CX02 • X2 • CX10 • CCX12 ≈ X2 • CX02 • CX10 • CCX12
p1 = by-assoc-and (under (ε) (CX10 • CCX12) B33.proved) Eq.refl Eq.refl

p2 : CX02 • CCX12 • X2 ≈ X2 • CX02 • CX10 • CCX12
p2 = trans (sym p0) p1

p3 : CX02 • CCX12 • X2 ≈ CX02 • CCX12 • X2
p3 = refl

p4 : X2 • CX02 • CX10 • CCX12 ≈ X2 • CX02 • CX10 • CCX12
p4 = refl

p5 : CX02 • CCX12 • X2 ≈ X2 • CX02 • CX10 • CCX12
p5 = trans (sym p3) (trans p2 p4)

p6 : X2 • CX02 • CX10 • CCX12 ≈ CX02 • CCX12 • X2
p6 = sym p5

proved : X2 • CX02 • CX10 • CCX12 ≈ CX02 • CCX12 • X2
proved = p6
