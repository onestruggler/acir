{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1407 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX10 ; CX12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0005 as B5
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0466 as B466
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1364 as B1364

p0 : CCX12 • CCX01 • CCX02 • CX10 • CX10 ≈ CX12 • CCX02 • CCX12 • CCX01 • CX10
p0 = by-assoc-and (under (ε) (CX10) B1364.proved) Eq.refl Eq.refl

p1 : CCX12 • CCX01 • CCX02 • CX10 • CX10 ≈ CCX12 • CCX01 • CCX02
p1 = by-assoc-and (under (CCX12 • CCX01 • CCX02) (ε) B5.proved) Eq.refl Eq.refl

p2 : CX12 • CCX02 • CCX12 • CCX01 • CX10 ≈ CCX12 • CCX01 • CCX02
p2 = trans (sym p0) p1

p3 : CX12 • CCX02 • CCX12 • CCX01 • CX10 ≈ CX12 • CCX02 • CX12 • CCX12 • CCX01
p3 = by-assoc-and (under (CX12 • CCX02) (ε) B466.proved) Eq.refl Eq.refl

p4 : CX12 • CCX02 • CCX12 • CCX01 • CX10 ≈ CX12 • CCX02 • CX12 • CCX12 • CCX01
p4 = trans p3 (refl)

p5 : CCX12 • CCX01 • CCX02 ≈ CCX12 • CCX01 • CCX02
p5 = refl

p6 : CX12 • CCX02 • CX12 • CCX12 • CCX01 ≈ CCX12 • CCX01 • CCX02
p6 = trans (sym p4) (trans p2 p5)

proved : CX12 • CCX02 • CX12 • CCX12 • CCX01 ≈ CCX12 • CCX01 • CCX02
proved = p6
