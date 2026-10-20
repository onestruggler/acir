{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0181 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX12 ; CX10 ; CX12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0006 as B6
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0141 as B141

p0 : CX10 • CCX12 • CX12 • CX12 ≈ CX12 • CCX12 • CX12
p0 = by-assoc-and (under (ε) (CX12) B141.proved) Eq.refl Eq.refl

p1 : CX10 • CCX12 • CX12 • CX12 ≈ CX10 • CCX12
p1 = by-assoc-and (under (CX10 • CCX12) (ε) B6.proved) Eq.refl Eq.refl

p2 : CX12 • CCX12 • CX12 ≈ CX10 • CCX12
p2 = trans (sym p0) p1

p3 : CX12 • CCX12 • CX12 ≈ CX12 • CCX12 • CX12
p3 = refl

p4 : CX10 • CCX12 ≈ CX10 • CCX12
p4 = refl

p5 : CX12 • CCX12 • CX12 ≈ CX10 • CCX12
p5 = trans (sym p3) (trans p2 p4)

proved : CX12 • CCX12 • CX12 ≈ CX10 • CCX12
proved = p5
