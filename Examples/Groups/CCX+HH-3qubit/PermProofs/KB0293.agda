{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0293 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX10 ; CX12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0180 as B180
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0202 as B202

p0 : CCX01 • CX10 • CX12 • CCX12 ≈ CX10 • CCX01 • CCX12
p0 = by-assoc-and (under (ε) (CCX12) B202.proved) Eq.refl Eq.refl

p1 : CCX01 • CX10 • CX12 • CCX12 ≈ CCX01 • CCX12 • CX12
p1 = by-assoc-and (under (CCX01) (ε) B180.proved) Eq.refl Eq.refl

p2 : CX10 • CCX01 • CCX12 ≈ CCX01 • CCX12 • CX12
p2 = trans (sym p0) p1

p3 : CX10 • CCX01 • CCX12 ≈ CX10 • CCX01 • CCX12
p3 = refl

p4 : CCX01 • CCX12 • CX12 ≈ CCX01 • CCX12 • CX12
p4 = refl

p5 : CX10 • CCX01 • CCX12 ≈ CCX01 • CCX12 • CX12
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX01 • CCX12 • CX12 ≈ CX10 • CCX01 • CCX12
p6 = sym p5

proved : CCX01 • CCX12 • CX12 ≈ CX10 • CCX01 • CCX12
proved = p6
