{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0356 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX12 ; CX10 ; X0 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0032 as B32
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0046 as B46
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0115 as B115

p0 : CCX12 • X0 • CX10 • X1 ≈ CCX12 • X1 • CX10
p0 = by-assoc-and (under (CCX12) (ε) B115.proved) Eq.refl Eq.refl

p1 : CCX12 • X0 • CX10 • X1 ≈ X0 • CCX12 • CX10 • X1
p1 = by-assoc-and (under (ε) (CX10 • X1) B46.proved) Eq.refl Eq.refl

p2 : CCX12 • X1 • CX10 ≈ X0 • CCX12 • CX10 • X1
p2 = trans (sym p0) p1

p3 : CCX12 • X1 • CX10 ≈ CCX12 • X1 • CX10
p3 = refl

p4 : X0 • CCX12 • CX10 • X1 ≈ X0 • CX10 • CCX12 • X1
p4 = by-assoc-and (under (X0) (X1) B32.proved) Eq.refl Eq.refl

p5 : X0 • CCX12 • CX10 • X1 ≈ X0 • CX10 • CCX12 • X1
p5 = trans p4 (refl)

p6 : CCX12 • X1 • CX10 ≈ X0 • CX10 • CCX12 • X1
p6 = trans (sym p3) (trans p2 p5)

p7 : X0 • CX10 • CCX12 • X1 ≈ CCX12 • X1 • CX10
p7 = sym p6

proved : X0 • CX10 • CCX12 • X1 ≈ CCX12 • X1 • CX10
proved = p7
