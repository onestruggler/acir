{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB5127 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX02 ; CX10 ; CX12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0027 as B27
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0321 as B321
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1350 as B1350

p0 : CCX01 • CCX12 • CCX02 • CX12 • CX02 ≈ CX10 • CCX02 • CCX01 • CCX12 • CX02
p0 = by-assoc-and (under (ε) (CX02) B1350.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX12 • CCX02 • CX12 • CX02 ≈ CCX01 • CCX12 • CCX02 • CX02 • CX12
p1 = by-assoc-and (under (CCX01 • CCX12 • CCX02) (ε) B27.proved) Eq.refl Eq.refl

p2 : CX10 • CCX02 • CCX01 • CCX12 • CX02 ≈ CCX01 • CCX12 • CCX02 • CX02 • CX12
p2 = trans (sym p0) p1

p3 : CX10 • CCX02 • CCX01 • CCX12 • CX02 ≈ CX10 • CCX02 • CX02 • CCX12 • CCX01
p3 = by-assoc-and (under (CX10 • CCX02) (ε) B321.proved) Eq.refl Eq.refl

p4 : CX10 • CCX02 • CCX01 • CCX12 • CX02 ≈ CX10 • CCX02 • CX02 • CCX12 • CCX01
p4 = trans p3 (refl)

p5 : CCX01 • CCX12 • CCX02 • CX02 • CX12 ≈ CCX01 • CCX12 • CCX02 • CX02 • CX12
p5 = refl

p6 : CX10 • CCX02 • CX02 • CCX12 • CCX01 ≈ CCX01 • CCX12 • CCX02 • CX02 • CX12
p6 = trans (sym p4) (trans p2 p5)

p7 : CCX01 • CCX12 • CCX02 • CX02 • CX12 ≈ CX10 • CCX02 • CX02 • CCX12 • CCX01
p7 = sym p6

proved : CCX01 • CCX12 • CCX02 • CX02 • CX12 ≈ CX10 • CCX02 • CX02 • CCX12 • CCX01
proved = p7
