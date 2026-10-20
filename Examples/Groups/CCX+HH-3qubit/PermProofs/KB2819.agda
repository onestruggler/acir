{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB2819 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX12 ; CX02 ; CX10 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0019 as B19
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0356 as B356
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0915 as B915

p0 : CX02 • X0 • CX10 • CCX12 • X1 ≈ X0 • CX02 • CCX12 • X2 • X1
p0 = by-assoc-and (under (ε) (X1) B915.proved) Eq.refl Eq.refl

p1 : CX02 • X0 • CX10 • CCX12 • X1 ≈ CX02 • CCX12 • X1 • CX10
p1 = by-assoc-and (under (CX02) (ε) B356.proved) Eq.refl Eq.refl

p2 : X0 • CX02 • CCX12 • X2 • X1 ≈ CX02 • CCX12 • X1 • CX10
p2 = trans (sym p0) p1

p3 : X0 • CX02 • CCX12 • X2 • X1 ≈ X0 • CX02 • CCX12 • X1 • X2
p3 = by-assoc-and (under (X0 • CX02 • CCX12) (ε) B19.proved) Eq.refl Eq.refl

p4 : X0 • CX02 • CCX12 • X2 • X1 ≈ X0 • CX02 • CCX12 • X1 • X2
p4 = trans p3 (refl)

p5 : CX02 • CCX12 • X1 • CX10 ≈ CX02 • CCX12 • X1 • CX10
p5 = refl

p6 : X0 • CX02 • CCX12 • X1 • X2 ≈ CX02 • CCX12 • X1 • CX10
p6 = trans (sym p4) (trans p2 p5)

proved : X0 • CX02 • CCX12 • X1 • X2 ≈ CX02 • CCX12 • X1 • CX10
proved = p6
