{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0287 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX12 ; CX10 ; CX12 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0141 as B141
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0168 as B168

p0 : X2 • CX10 • CCX12 • CX12 ≈ CCX12 • X2 • CX12
p0 = by-assoc-and (under (ε) (CX12) B168.proved) Eq.refl Eq.refl

p1 : X2 • CX10 • CCX12 • CX12 ≈ X2 • CX12 • CCX12
p1 = by-assoc-and (under (X2) (ε) B141.proved) Eq.refl Eq.refl

p2 : CCX12 • X2 • CX12 ≈ X2 • CX12 • CCX12
p2 = trans (sym p0) p1

p3 : CCX12 • X2 • CX12 ≈ CCX12 • X2 • CX12
p3 = refl

p4 : X2 • CX12 • CCX12 ≈ X2 • CX12 • CCX12
p4 = refl

p5 : CCX12 • X2 • CX12 ≈ X2 • CX12 • CCX12
p5 = trans (sym p3) (trans p2 p4)

proved : CCX12 • X2 • CX12 ≈ X2 • CX12 • CCX12
proved = p5
