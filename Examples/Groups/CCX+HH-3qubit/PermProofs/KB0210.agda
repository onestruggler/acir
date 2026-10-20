{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0210 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX10 ; CX12 ; CX20 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0006 as B6
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0174 as B174
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0208 as B208

p0 : CX10 • CX20 • CX12 • CX12 ≈ CX12 • CX20 • CX12
p0 = by-assoc-and (under (ε) (CX12) B208.proved) Eq.refl Eq.refl

p1 : CX10 • CX20 • CX12 • CX12 ≈ CX10 • CX20
p1 = by-assoc-and (under (CX10 • CX20) (ε) B6.proved) Eq.refl Eq.refl

p2 : CX12 • CX20 • CX12 ≈ CX10 • CX20
p2 = trans (sym p0) p1

p3 : CX12 • CX20 • CX12 ≈ CX20 • CX10
p3 = by-assoc-and (under (ε) (ε) B174.proved) Eq.refl Eq.refl

p4 : CX12 • CX20 • CX12 ≈ CX20 • CX10
p4 = trans p3 (refl)

p5 : CX10 • CX20 ≈ CX10 • CX20
p5 = refl

p6 : CX20 • CX10 ≈ CX10 • CX20
p6 = trans (sym p4) (trans p2 p5)

proved : CX20 • CX10 ≈ CX10 • CX20
proved = p6
