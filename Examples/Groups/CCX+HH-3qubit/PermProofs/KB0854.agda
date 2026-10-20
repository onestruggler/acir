{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0854 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX02 ; CX20 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0120 as B120
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0169 as B169
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0325 as B325

p0 : CX02 • CCX01 • X1 • CCX12 • X1 ≈ CX02 • CCX01 • CX20 • CCX12
p0 = by-assoc-and (under (CX02 • CCX01) (ε) B169.proved) Eq.refl Eq.refl

p1 : CX02 • CCX01 • X1 • CCX12 • X1 ≈ X1 • CCX01 • CCX12 • X1
p1 = by-assoc-and (under (ε) (CCX12 • X1) B120.proved) Eq.refl Eq.refl

p2 : CX02 • CCX01 • CX20 • CCX12 ≈ X1 • CCX01 • CCX12 • X1
p2 = trans (sym p0) p1

p3 : CX02 • CCX01 • CX20 • CCX12 ≈ CX02 • CX20 • CCX12 • CCX01
p3 = by-assoc-and (under (CX02) (ε) B325.proved) Eq.refl Eq.refl

p4 : CX02 • CCX01 • CX20 • CCX12 ≈ CX02 • CX20 • CCX12 • CCX01
p4 = trans p3 (refl)

p5 : X1 • CCX01 • CCX12 • X1 ≈ X1 • CCX01 • CCX12 • X1
p5 = refl

p6 : CX02 • CX20 • CCX12 • CCX01 ≈ X1 • CCX01 • CCX12 • X1
p6 = trans (sym p4) (trans p2 p5)

proved : CX02 • CX20 • CCX12 • CCX01 ≈ X1 • CCX01 • CCX12 • X1
proved = p6
