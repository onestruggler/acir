{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1350 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX10 ; CX12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0667 as B667
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0721 as B721

p0 : CCX01 • CX10 • CCX02 • CX12 • CCX12 ≈ CCX01 • CCX12 • CCX02 • CX12
p0 = by-assoc-and (under (CCX01) (ε) B721.proved) Eq.refl Eq.refl

p1 : CCX01 • CX10 • CCX02 • CX12 • CCX12 ≈ CX10 • CCX02 • CCX01 • CCX12
p1 = by-assoc-and (under (ε) (CCX12) B667.proved) Eq.refl Eq.refl

p2 : CCX01 • CCX12 • CCX02 • CX12 ≈ CX10 • CCX02 • CCX01 • CCX12
p2 = trans (sym p0) p1

p3 : CCX01 • CCX12 • CCX02 • CX12 ≈ CCX01 • CCX12 • CCX02 • CX12
p3 = refl

p4 : CX10 • CCX02 • CCX01 • CCX12 ≈ CX10 • CCX02 • CCX01 • CCX12
p4 = refl

p5 : CCX01 • CCX12 • CCX02 • CX12 ≈ CX10 • CCX02 • CCX01 • CCX12
p5 = trans (sym p3) (trans p2 p4)

proved : CCX01 • CCX12 • CCX02 • CX12 ≈ CX10 • CCX02 • CCX01 • CCX12
proved = p5
