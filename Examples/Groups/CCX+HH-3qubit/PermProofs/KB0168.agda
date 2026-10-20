{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0168 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX12 ; CX10 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0005 as B5
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0021 as B21
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0131 as B131

p0 : CX10 • CX10 • CCX12 • X2 ≈ CX10 • X2 • CCX12
p0 = by-assoc-and (under (CX10) (ε) B131.proved) Eq.refl Eq.refl

p1 : CX10 • CX10 • CCX12 • X2 ≈ CCX12 • X2
p1 = by-assoc-and (under (ε) (CCX12 • X2) B5.proved) Eq.refl Eq.refl

p2 : CX10 • X2 • CCX12 ≈ CCX12 • X2
p2 = trans (sym p0) p1

p3 : CX10 • X2 • CCX12 ≈ X2 • CX10 • CCX12
p3 = by-assoc-and (under (ε) (CCX12) B21.proved) Eq.refl Eq.refl

p4 : CX10 • X2 • CCX12 ≈ X2 • CX10 • CCX12
p4 = trans p3 (refl)

p5 : CCX12 • X2 ≈ CCX12 • X2
p5 = refl

p6 : X2 • CX10 • CCX12 ≈ CCX12 • X2
p6 = trans (sym p4) (trans p2 p5)

proved : X2 • CX10 • CCX12 ≈ CCX12 • X2
proved = p6
