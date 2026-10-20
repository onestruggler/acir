{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0146 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX10 ; CX12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0005 as B5
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0118 as B118

p0 : CX12 • CCX01 • CX10 • CX10 ≈ CX10 • CCX01 • CX10
p0 = by-assoc-and (under (ε) (CX10) B118.proved) Eq.refl Eq.refl

p1 : CX12 • CCX01 • CX10 • CX10 ≈ CX12 • CCX01
p1 = by-assoc-and (under (CX12 • CCX01) (ε) B5.proved) Eq.refl Eq.refl

p2 : CX10 • CCX01 • CX10 ≈ CX12 • CCX01
p2 = trans (sym p0) p1

p3 : CX10 • CCX01 • CX10 ≈ CX10 • CCX01 • CX10
p3 = refl

p4 : CX12 • CCX01 ≈ CX12 • CCX01
p4 = refl

p5 : CX10 • CCX01 • CX10 ≈ CX12 • CCX01
p5 = trans (sym p3) (trans p2 p4)

proved : CX10 • CCX01 • CX10 ≈ CX12 • CCX01
proved = p5
