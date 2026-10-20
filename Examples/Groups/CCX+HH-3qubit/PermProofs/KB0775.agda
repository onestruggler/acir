{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0775 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CX10 ; CX12 ; CX20 ; CX21 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0135 as B135
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0136 as B136

p0 : CX21 • CCX02 • CX20 • CX10 • CX12 ≈ CX20 • CCX02 • CX10 • CX12
p0 = by-assoc-and (under (ε) (CX10 • CX12) B136.proved) Eq.refl Eq.refl

p1 : CX21 • CCX02 • CX20 • CX10 • CX12 ≈ CX21 • CCX02 • CX12 • CX20
p1 = by-assoc-and (under (CX21 • CCX02) (ε) B135.proved) Eq.refl Eq.refl

p2 : CX20 • CCX02 • CX10 • CX12 ≈ CX21 • CCX02 • CX12 • CX20
p2 = trans (sym p0) p1

p3 : CX20 • CCX02 • CX10 • CX12 ≈ CX20 • CCX02 • CX10 • CX12
p3 = refl

p4 : CX21 • CCX02 • CX12 • CX20 ≈ CX21 • CCX02 • CX12 • CX20
p4 = refl

p5 : CX20 • CCX02 • CX10 • CX12 ≈ CX21 • CCX02 • CX12 • CX20
p5 = trans (sym p3) (trans p2 p4)

p6 : CX21 • CCX02 • CX12 • CX20 ≈ CX20 • CCX02 • CX10 • CX12
p6 = sym p5

proved : CX21 • CCX02 • CX12 • CX20 ≈ CX20 • CCX02 • CX10 • CX12
proved = p6
