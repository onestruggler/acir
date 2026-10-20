{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0973 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; CX01 ; CX10 ; X0 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0047 as B47
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0219 as B219

p0 : CX10 • CCX02 • CX10 • X0 ≈ CX01 • CCX12 • CX01 • X0
p0 = by-assoc-and (under (ε) (X0) B219.proved) Eq.refl Eq.refl

p1 : CX10 • CCX02 • CX10 • X0 ≈ CX10 • CCX02 • X0 • CX10
p1 = by-assoc-and (under (CX10 • CCX02) (ε) B47.proved) Eq.refl Eq.refl

p2 : CX01 • CCX12 • CX01 • X0 ≈ CX10 • CCX02 • X0 • CX10
p2 = trans (sym p0) p1

p3 : CX01 • CCX12 • CX01 • X0 ≈ CX01 • CCX12 • CX01 • X0
p3 = refl

p4 : CX10 • CCX02 • X0 • CX10 ≈ CX10 • CCX02 • X0 • CX10
p4 = refl

p5 : CX01 • CCX12 • CX01 • X0 ≈ CX10 • CCX02 • X0 • CX10
p5 = trans (sym p3) (trans p2 p4)

p6 : CX10 • CCX02 • X0 • CX10 ≈ CX01 • CCX12 • CX01 • X0
p6 = sym p5

proved : CX10 • CCX02 • X0 • CX10 ≈ CX01 • CCX12 • CX01 • X0
proved = p6
