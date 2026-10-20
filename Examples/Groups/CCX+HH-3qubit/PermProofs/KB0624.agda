{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0624 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX10 ; CX12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0118 as B118
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0308 as B308

p0 : CCX02 • CX12 • CCX01 • CX10 ≈ CX12 • CCX01 • CCX02 • CX10
p0 = by-assoc-and (under (ε) (CX10) B308.proved) Eq.refl Eq.refl

p1 : CCX02 • CX12 • CCX01 • CX10 ≈ CCX02 • CX10 • CCX01
p1 = by-assoc-and (under (CCX02) (ε) B118.proved) Eq.refl Eq.refl

p2 : CX12 • CCX01 • CCX02 • CX10 ≈ CCX02 • CX10 • CCX01
p2 = trans (sym p0) p1

p3 : CX12 • CCX01 • CCX02 • CX10 ≈ CX12 • CCX01 • CCX02 • CX10
p3 = refl

p4 : CCX02 • CX10 • CCX01 ≈ CCX02 • CX10 • CCX01
p4 = refl

p5 : CX12 • CCX01 • CCX02 • CX10 ≈ CCX02 • CX10 • CCX01
p5 = trans (sym p3) (trans p2 p4)

proved : CX12 • CCX01 • CCX02 • CX10 ≈ CCX02 • CX10 • CCX01
proved = p5
