{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0566 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX12 ; CX10 ; CX20 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0040 as B40
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0194 as B194

p0 : CCX12 • X2 • CCX12 • CX20 ≈ X2 • CX10 • CX20
p0 = by-assoc-and (under (ε) (CX20) B194.proved) Eq.refl Eq.refl

p1 : CCX12 • X2 • CCX12 • CX20 ≈ CCX12 • X2 • CX20 • CCX12
p1 = by-assoc-and (under (CCX12 • X2) (ε) B40.proved) Eq.refl Eq.refl

p2 : X2 • CX10 • CX20 ≈ CCX12 • X2 • CX20 • CCX12
p2 = trans (sym p0) p1

p3 : X2 • CX10 • CX20 ≈ X2 • CX10 • CX20
p3 = refl

p4 : CCX12 • X2 • CX20 • CCX12 ≈ CCX12 • X2 • CX20 • CCX12
p4 = refl

p5 : X2 • CX10 • CX20 ≈ CCX12 • X2 • CX20 • CCX12
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX12 • X2 • CX20 • CCX12 ≈ X2 • CX10 • CX20
p6 = sym p5

proved : CCX12 • X2 • CX20 • CCX12 ≈ X2 • CX10 • CX20
proved = p6
