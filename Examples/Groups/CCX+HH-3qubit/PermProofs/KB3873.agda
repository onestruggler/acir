{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB3873 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX10 ; CX12 ; X0 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0141 as B141
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0623 as B623

p0 : CX10 • CCX12 • CX12 • CCX02 • X0 • CCX01 ≈ CX10 • CCX12 • CCX01 • CCX02 • X0
p0 = by-assoc-and (under (CX10 • CCX12) (ε) B623.proved) Eq.refl Eq.refl

p1 : CX10 • CCX12 • CX12 • CCX02 • X0 • CCX01 ≈ CX12 • CCX12 • CCX02 • X0 • CCX01
p1 = by-assoc-and (under (ε) (CCX02 • X0 • CCX01) B141.proved) Eq.refl Eq.refl

p2 : CX10 • CCX12 • CCX01 • CCX02 • X0 ≈ CX12 • CCX12 • CCX02 • X0 • CCX01
p2 = trans (sym p0) p1

p3 : CX10 • CCX12 • CCX01 • CCX02 • X0 ≈ CX10 • CCX12 • CCX01 • CCX02 • X0
p3 = refl

p4 : CX12 • CCX12 • CCX02 • X0 • CCX01 ≈ CX12 • CCX12 • CCX02 • X0 • CCX01
p4 = refl

p5 : CX10 • CCX12 • CCX01 • CCX02 • X0 ≈ CX12 • CCX12 • CCX02 • X0 • CCX01
p5 = trans (sym p3) (trans p2 p4)

p6 : CX12 • CCX12 • CCX02 • X0 • CCX01 ≈ CX10 • CCX12 • CCX01 • CCX02 • X0
p6 = sym p5

proved : CX12 • CCX12 • CCX02 • X0 • CCX01 ≈ CX10 • CCX12 • CCX01 • CCX02 • X0
proved = p6
