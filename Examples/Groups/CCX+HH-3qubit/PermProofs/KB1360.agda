{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1360 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX02 ; CX10 ; CX12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0027 as B27
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0315 as B315
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0326 as B326

p0 : CX10 • CX02 • CCX12 • CX02 • CCX12 ≈ CX10 • CCX12 • CCX01
p0 = by-assoc-and (under (CX10) (ε) B326.proved) Eq.refl Eq.refl

p1 : CX10 • CX02 • CCX12 • CX02 • CCX12 ≈ CX02 • CCX12 • CX12 • CX02 • CCX12
p1 = by-assoc-and (under (ε) (CX02 • CCX12) B315.proved) Eq.refl Eq.refl

p2 : CX10 • CCX12 • CCX01 ≈ CX02 • CCX12 • CX12 • CX02 • CCX12
p2 = trans (sym p0) p1

p3 : CX10 • CCX12 • CCX01 ≈ CX10 • CCX12 • CCX01
p3 = refl

p4 : CX02 • CCX12 • CX12 • CX02 • CCX12 ≈ CX02 • CCX12 • CX02 • CX12 • CCX12
p4 = by-assoc-and (under (CX02 • CCX12) (CCX12) B27.proved) Eq.refl Eq.refl

p5 : CX02 • CCX12 • CX12 • CX02 • CCX12 ≈ CX02 • CCX12 • CX02 • CX12 • CCX12
p5 = trans p4 (refl)

p6 : CX10 • CCX12 • CCX01 ≈ CX02 • CCX12 • CX02 • CX12 • CCX12
p6 = trans (sym p3) (trans p2 p5)

p7 : CX02 • CCX12 • CX02 • CX12 • CCX12 ≈ CX10 • CCX12 • CCX01
p7 = sym p6

proved : CX02 • CCX12 • CX02 • CX12 • CCX12 ≈ CX10 • CCX12 • CCX01
proved = p7
