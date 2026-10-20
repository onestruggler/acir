{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1364 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX10 ; CX12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0622 as B622
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1362 as B1362

p0 : CCX12 • CX12 • CCX02 • CX10 • CCX01 ≈ CX12 • CCX02 • CCX12 • CCX01
p0 = by-assoc-and (under (ε) (CCX01) B1362.proved) Eq.refl Eq.refl

p1 : CCX12 • CX12 • CCX02 • CX10 • CCX01 ≈ CCX12 • CCX01 • CCX02 • CX10
p1 = by-assoc-and (under (CCX12) (ε) B622.proved) Eq.refl Eq.refl

p2 : CX12 • CCX02 • CCX12 • CCX01 ≈ CCX12 • CCX01 • CCX02 • CX10
p2 = trans (sym p0) p1

p3 : CX12 • CCX02 • CCX12 • CCX01 ≈ CX12 • CCX02 • CCX12 • CCX01
p3 = refl

p4 : CCX12 • CCX01 • CCX02 • CX10 ≈ CCX12 • CCX01 • CCX02 • CX10
p4 = refl

p5 : CX12 • CCX02 • CCX12 • CCX01 ≈ CCX12 • CCX01 • CCX02 • CX10
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX12 • CCX01 • CCX02 • CX10 ≈ CX12 • CCX02 • CCX12 • CCX01
p6 = sym p5

proved : CCX12 • CCX01 • CCX02 • CX10 ≈ CX12 • CCX02 • CCX12 • CCX01
proved = p6
