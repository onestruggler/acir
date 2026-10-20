{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0466 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX10 ; CX12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0032 as B32
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0141 as B141
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0147 as B147

p0 : CCX12 • CX10 • CX12 • CCX01 ≈ CCX12 • CCX01 • CX10
p0 = by-assoc-and (under (CCX12) (ε) B147.proved) Eq.refl Eq.refl

p1 : CCX12 • CX10 • CX12 • CCX01 ≈ CX10 • CCX12 • CX12 • CCX01
p1 = by-assoc-and (under (ε) (CX12 • CCX01) B32.proved) Eq.refl Eq.refl

p2 : CCX12 • CCX01 • CX10 ≈ CX10 • CCX12 • CX12 • CCX01
p2 = trans (sym p0) p1

p3 : CCX12 • CCX01 • CX10 ≈ CCX12 • CCX01 • CX10
p3 = refl

p4 : CX10 • CCX12 • CX12 • CCX01 ≈ CX12 • CCX12 • CCX01
p4 = by-assoc-and (under (ε) (CCX01) B141.proved) Eq.refl Eq.refl

p5 : CX10 • CCX12 • CX12 • CCX01 ≈ CX12 • CCX12 • CCX01
p5 = trans p4 (refl)

p6 : CCX12 • CCX01 • CX10 ≈ CX12 • CCX12 • CCX01
p6 = trans (sym p3) (trans p2 p5)

proved : CCX12 • CCX01 • CX10 ≈ CX12 • CCX12 • CCX01
proved = p6
