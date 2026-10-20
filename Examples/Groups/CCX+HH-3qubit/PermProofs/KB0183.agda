{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0183 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX12 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0006 as B6
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0145 as B145

p0 : CX12 • CX12 • X1 • CX12 ≈ CX12 • X1 • X2
p0 = by-assoc-and (under (CX12) (ε) B145.proved) Eq.refl Eq.refl

p1 : CX12 • CX12 • X1 • CX12 ≈ X1 • CX12
p1 = by-assoc-and (under (ε) (X1 • CX12) B6.proved) Eq.refl Eq.refl

p2 : CX12 • X1 • X2 ≈ X1 • CX12
p2 = trans (sym p0) p1

p3 : CX12 • X1 • X2 ≈ CX12 • X1 • X2
p3 = refl

p4 : X1 • CX12 ≈ X1 • CX12
p4 = refl

p5 : CX12 • X1 • X2 ≈ X1 • CX12
p5 = trans (sym p3) (trans p2 p4)

proved : CX12 • X1 • X2 ≈ X1 • CX12
proved = p5
