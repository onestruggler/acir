{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0284 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX10 ; CX12 ; CX20 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0135 as B135
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0147 as B147

p0 : CX20 • CX10 • CX12 • CCX01 ≈ CX20 • CCX01 • CX10
p0 = by-assoc-and (under (CX20) (ε) B147.proved) Eq.refl Eq.refl

p1 : CX20 • CX10 • CX12 • CCX01 ≈ CX12 • CX20 • CCX01
p1 = by-assoc-and (under (ε) (CCX01) B135.proved) Eq.refl Eq.refl

p2 : CX20 • CCX01 • CX10 ≈ CX12 • CX20 • CCX01
p2 = trans (sym p0) p1

p3 : CX20 • CCX01 • CX10 ≈ CX20 • CCX01 • CX10
p3 = refl

p4 : CX12 • CX20 • CCX01 ≈ CX12 • CX20 • CCX01
p4 = refl

p5 : CX20 • CCX01 • CX10 ≈ CX12 • CX20 • CCX01
p5 = trans (sym p3) (trans p2 p4)

proved : CX20 • CCX01 • CX10 ≈ CX12 • CX20 • CCX01
proved = p5
