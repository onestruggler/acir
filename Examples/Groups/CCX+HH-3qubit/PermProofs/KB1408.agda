{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1408 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0006 as B6
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1407 as B1407

p0 : CX12 • CX12 • CCX02 • CX12 • CCX12 • CCX01 ≈ CX12 • CCX12 • CCX01 • CCX02
p0 = by-assoc-and (under (CX12) (ε) B1407.proved) Eq.refl Eq.refl

p1 : CX12 • CX12 • CCX02 • CX12 • CCX12 • CCX01 ≈ CCX02 • CX12 • CCX12 • CCX01
p1 = by-assoc-and (under (ε) (CCX02 • CX12 • CCX12 • CCX01) B6.proved) Eq.refl Eq.refl

p2 : CX12 • CCX12 • CCX01 • CCX02 ≈ CCX02 • CX12 • CCX12 • CCX01
p2 = trans (sym p0) p1

p3 : CX12 • CCX12 • CCX01 • CCX02 ≈ CX12 • CCX12 • CCX01 • CCX02
p3 = refl

p4 : CCX02 • CX12 • CCX12 • CCX01 ≈ CCX02 • CX12 • CCX12 • CCX01
p4 = refl

p5 : CX12 • CCX12 • CCX01 • CCX02 ≈ CCX02 • CX12 • CCX12 • CCX01
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX02 • CX12 • CCX12 • CCX01 ≈ CX12 • CCX12 • CCX01 • CCX02
p6 = sym p5

proved : CCX02 • CX12 • CCX12 • CCX01 ≈ CX12 • CCX12 • CCX01 • CCX02
proved = p6
