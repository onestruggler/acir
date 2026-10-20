{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1274 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; CX10 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0021 as B21
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0336 as B336

p0 : CCX12 • CCX02 • CX10 • X2 ≈ CX10 • CCX02 • CCX12 • X2
p0 = by-assoc-and (under (ε) (X2) B336.proved) Eq.refl Eq.refl

p1 : CCX12 • CCX02 • CX10 • X2 ≈ CCX12 • CCX02 • X2 • CX10
p1 = by-assoc-and (under (CCX12 • CCX02) (ε) B21.proved) Eq.refl Eq.refl

p2 : CX10 • CCX02 • CCX12 • X2 ≈ CCX12 • CCX02 • X2 • CX10
p2 = trans (sym p0) p1

p3 : CX10 • CCX02 • CCX12 • X2 ≈ CX10 • CCX02 • CCX12 • X2
p3 = refl

p4 : CCX12 • CCX02 • X2 • CX10 ≈ CCX12 • CCX02 • X2 • CX10
p4 = refl

p5 : CX10 • CCX02 • CCX12 • X2 ≈ CCX12 • CCX02 • X2 • CX10
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX12 • CCX02 • X2 • CX10 ≈ CX10 • CCX02 • CCX12 • X2
p6 = sym p5

proved : CCX12 • CCX02 • X2 • CX10 ≈ CX10 • CCX02 • CCX12 • X2
proved = p6
