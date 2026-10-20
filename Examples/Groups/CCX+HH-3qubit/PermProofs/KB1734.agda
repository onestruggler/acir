{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1734 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; CX10 ; X0 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0182 as B182
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0231 as B231
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0335 as B335

p0 : CX10 • CCX12 • CCX02 • CX10 • X1 • CX10 ≈ CCX02 • CCX12 • X1 • CX10
p0 = by-assoc-and (under (ε) (X1 • CX10) B335.proved) Eq.refl Eq.refl

p1 : CX10 • CCX12 • CCX02 • CX10 • X1 • CX10 ≈ CX10 • CCX12 • CCX02 • X0 • X1
p1 = by-assoc-and (under (CX10 • CCX12 • CCX02) (ε) B182.proved) Eq.refl Eq.refl

p2 : CCX02 • CCX12 • X1 • CX10 ≈ CX10 • CCX12 • CCX02 • X0 • X1
p2 = trans (sym p0) p1

p3 : CCX02 • CCX12 • X1 • CX10 ≈ CCX02 • CCX12 • X1 • CX10
p3 = refl

p4 : CX10 • CCX12 • CCX02 • X0 • X1 ≈ CX10 • CCX12 • X1 • CCX02 • X0
p4 = by-assoc-and (under (CX10 • CCX12) (ε) B231.proved) Eq.refl Eq.refl

p5 : CX10 • CCX12 • CCX02 • X0 • X1 ≈ CX10 • CCX12 • X1 • CCX02 • X0
p5 = trans p4 (refl)

p6 : CCX02 • CCX12 • X1 • CX10 ≈ CX10 • CCX12 • X1 • CCX02 • X0
p6 = trans (sym p3) (trans p2 p5)

p7 : CX10 • CCX12 • X1 • CCX02 • X0 ≈ CCX02 • CCX12 • X1 • CX10
p7 = sym p6

proved : CX10 • CCX12 • X1 • CCX02 • X0 ≈ CCX02 • CCX12 • X1 • CX10
proved = p7
