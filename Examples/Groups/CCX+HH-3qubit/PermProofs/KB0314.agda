{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0314 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX02 ; CX10 ; CX12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0147 as B147
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0310 as B310

p0 : CX02 • CX10 • CX12 • CCX01 ≈ CX10 • CX02 • CCX01
p0 = by-assoc-and (under (ε) (CCX01) B310.proved) Eq.refl Eq.refl

p1 : CX02 • CX10 • CX12 • CCX01 ≈ CX02 • CCX01 • CX10
p1 = by-assoc-and (under (CX02) (ε) B147.proved) Eq.refl Eq.refl

p2 : CX10 • CX02 • CCX01 ≈ CX02 • CCX01 • CX10
p2 = trans (sym p0) p1

p3 : CX10 • CX02 • CCX01 ≈ CX10 • CX02 • CCX01
p3 = refl

p4 : CX02 • CCX01 • CX10 ≈ CX02 • CCX01 • CX10
p4 = refl

p5 : CX10 • CX02 • CCX01 ≈ CX02 • CCX01 • CX10
p5 = trans (sym p3) (trans p2 p4)

proved : CX10 • CX02 • CCX01 ≈ CX02 • CCX01 • CX10
proved = p5
