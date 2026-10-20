{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1871 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; CX02 ; CX10 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0168 as B168
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0372 as B372

p0 : CX02 • CCX02 • X2 • CX10 • CCX12 ≈ X2 • CCX02 • CX02 • CX10 • CCX12
p0 = by-assoc-and (under (ε) (CX10 • CCX12) B372.proved) Eq.refl Eq.refl

p1 : CX02 • CCX02 • X2 • CX10 • CCX12 ≈ CX02 • CCX02 • CCX12 • X2
p1 = by-assoc-and (under (CX02 • CCX02) (ε) B168.proved) Eq.refl Eq.refl

p2 : X2 • CCX02 • CX02 • CX10 • CCX12 ≈ CX02 • CCX02 • CCX12 • X2
p2 = trans (sym p0) p1

p3 : X2 • CCX02 • CX02 • CX10 • CCX12 ≈ X2 • CCX02 • CX02 • CX10 • CCX12
p3 = refl

p4 : CX02 • CCX02 • CCX12 • X2 ≈ CX02 • CCX02 • CCX12 • X2
p4 = refl

p5 : X2 • CCX02 • CX02 • CX10 • CCX12 ≈ CX02 • CCX02 • CCX12 • X2
p5 = trans (sym p3) (trans p2 p4)

proved : X2 • CCX02 • CX02 • CX10 • CCX12 ≈ CX02 • CCX02 • CCX12 • X2
proved = p5
