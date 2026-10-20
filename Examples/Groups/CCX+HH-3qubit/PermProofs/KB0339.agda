{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0339 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; CX01 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0013 as B13
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0338 as B338

p0 : CX01 • CX01 • CCX12 • CX01 • CCX12 ≈ CX01 • CCX12 • CCX02
p0 = by-assoc-and (under (CX01) (ε) B338.proved) Eq.refl Eq.refl

p1 : CX01 • CX01 • CCX12 • CX01 • CCX12 ≈ CCX12 • CX01 • CCX12
p1 = by-assoc-and (under (ε) (CCX12 • CX01 • CCX12) B13.proved) Eq.refl Eq.refl

p2 : CX01 • CCX12 • CCX02 ≈ CCX12 • CX01 • CCX12
p2 = trans (sym p0) p1

p3 : CX01 • CCX12 • CCX02 ≈ CX01 • CCX12 • CCX02
p3 = refl

p4 : CCX12 • CX01 • CCX12 ≈ CCX12 • CX01 • CCX12
p4 = refl

p5 : CX01 • CCX12 • CCX02 ≈ CCX12 • CX01 • CCX12
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX12 • CX01 • CCX12 ≈ CX01 • CCX12 • CCX02
p6 = sym p5

proved : CCX12 • CX01 • CCX12 ≈ CX01 • CCX12 • CCX02
proved = p6
