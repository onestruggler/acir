{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0131 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX12 ; CX10 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0032 as B32

import Examples.Groups.CCX+HH-3qubit.Tietze.drel130 as Tdrel130
p0 : X2 • CCX12 ≈ CCX12 • CX10 • X2
p0 = Tdrel130.proved

p1 : X2 • CCX12 ≈ X2 • CCX12
p1 = refl

p2 : CCX12 • CX10 • X2 ≈ CX10 • CCX12 • X2
p2 = by-assoc-and (under (ε) (X2) B32.proved) Eq.refl Eq.refl

p3 : CCX12 • CX10 • X2 ≈ CX10 • CCX12 • X2
p3 = trans p2 (refl)

p4 : X2 • CCX12 ≈ CX10 • CCX12 • X2
p4 = trans (sym p1) (trans p0 p3)

p5 : CX10 • CCX12 • X2 ≈ X2 • CCX12
p5 = sym p4

proved : CX10 • CCX12 • X2 ≈ X2 • CCX12
proved = p5
