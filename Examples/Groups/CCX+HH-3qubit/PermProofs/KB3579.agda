{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB3579 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CX10 ; CX12 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0021 as B21
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0117 as B117
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0451 as B451

p0 : X1 • CCX02 • CX10 • X1 • X2 • CX12 ≈ CCX02 • X0 • CX10 • X2 • CX12
p0 = by-assoc-and (under (ε) (X2 • CX12) B451.proved) Eq.refl Eq.refl

p1 : X1 • CCX02 • CX10 • X1 • X2 • CX12 ≈ X1 • CCX02 • CX10 • CX12 • X1
p1 = by-assoc-and (under (X1 • CCX02 • CX10) (ε) B117.proved) Eq.refl Eq.refl

p2 : CCX02 • X0 • CX10 • X2 • CX12 ≈ X1 • CCX02 • CX10 • CX12 • X1
p2 = trans (sym p0) p1

p3 : CCX02 • X0 • CX10 • X2 • CX12 ≈ CCX02 • X0 • X2 • CX10 • CX12
p3 = by-assoc-and (under (CCX02 • X0) (CX12) B21.proved) Eq.refl Eq.refl

p4 : CCX02 • X0 • CX10 • X2 • CX12 ≈ CCX02 • X0 • X2 • CX10 • CX12
p4 = trans p3 (refl)

p5 : X1 • CCX02 • CX10 • CX12 • X1 ≈ X1 • CCX02 • CX10 • CX12 • X1
p5 = refl

p6 : CCX02 • X0 • X2 • CX10 • CX12 ≈ X1 • CCX02 • CX10 • CX12 • X1
p6 = trans (sym p4) (trans p2 p5)

proved : CCX02 • X0 • X2 • CX10 • CX12 ≈ X1 • CCX02 • CX10 • CX12 • X1
proved = p6
