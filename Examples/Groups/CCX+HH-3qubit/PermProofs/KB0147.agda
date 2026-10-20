{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0147 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX10 ; CX12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0006 as B6
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0026 as B26
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0118 as B118

p0 : CX12 • CX12 • CCX01 • CX10 ≈ CX12 • CX10 • CCX01
p0 = by-assoc-and (under (CX12) (ε) B118.proved) Eq.refl Eq.refl

p1 : CX12 • CX12 • CCX01 • CX10 ≈ CCX01 • CX10
p1 = by-assoc-and (under (ε) (CCX01 • CX10) B6.proved) Eq.refl Eq.refl

p2 : CX12 • CX10 • CCX01 ≈ CCX01 • CX10
p2 = trans (sym p0) p1

p3 : CX12 • CX10 • CCX01 ≈ CX10 • CX12 • CCX01
p3 = by-assoc-and (under (ε) (CCX01) B26.proved) Eq.refl Eq.refl

p4 : CX12 • CX10 • CCX01 ≈ CX10 • CX12 • CCX01
p4 = trans p3 (refl)

p5 : CCX01 • CX10 ≈ CCX01 • CX10
p5 = refl

p6 : CX10 • CX12 • CCX01 ≈ CCX01 • CX10
p6 = trans (sym p4) (trans p2 p5)

proved : CX10 • CX12 • CCX01 ≈ CCX01 • CX10
proved = p6
