{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0362 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX12 ; CX20 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0024 as B24
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0117 as B117

p0 : CX20 • X1 • X2 • CX12 ≈ CX20 • CX12 • X1
p0 = by-assoc-and (under (CX20) (ε) B117.proved) Eq.refl Eq.refl

p1 : CX20 • X1 • X2 • CX12 ≈ X1 • CX20 • X2 • CX12
p1 = by-assoc-and (under (ε) (X2 • CX12) B24.proved) Eq.refl Eq.refl

p2 : CX20 • CX12 • X1 ≈ X1 • CX20 • X2 • CX12
p2 = trans (sym p0) p1

p3 : CX20 • CX12 • X1 ≈ CX20 • CX12 • X1
p3 = refl

p4 : X1 • CX20 • X2 • CX12 ≈ X1 • CX20 • X2 • CX12
p4 = refl

p5 : CX20 • CX12 • X1 ≈ X1 • CX20 • X2 • CX12
p5 = trans (sym p3) (trans p2 p4)

p6 : X1 • CX20 • X2 • CX12 ≈ CX20 • CX12 • X1
p6 = sym p5

proved : X1 • CX20 • X2 • CX12 ≈ CX20 • CX12 • X1
proved = p6
