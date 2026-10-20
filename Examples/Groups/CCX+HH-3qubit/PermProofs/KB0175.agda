{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0175 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX10 ; CX12 ; CX20 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0009 as B9
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0135 as B135

p0 : CX20 • CX20 • CX10 • CX12 ≈ CX20 • CX12 • CX20
p0 = by-assoc-and (under (CX20) (ε) B135.proved) Eq.refl Eq.refl

p1 : CX20 • CX20 • CX10 • CX12 ≈ CX10 • CX12
p1 = by-assoc-and (under (ε) (CX10 • CX12) B9.proved) Eq.refl Eq.refl

p2 : CX20 • CX12 • CX20 ≈ CX10 • CX12
p2 = trans (sym p0) p1

p3 : CX20 • CX12 • CX20 ≈ CX20 • CX12 • CX20
p3 = refl

p4 : CX10 • CX12 ≈ CX10 • CX12
p4 = refl

p5 : CX20 • CX12 • CX20 ≈ CX10 • CX12
p5 = trans (sym p3) (trans p2 p4)

proved : CX20 • CX12 • CX20 ≈ CX10 • CX12
proved = p5
