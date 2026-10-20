{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB3181 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; CX20 ; CX21 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB3180 as B3180

p0 : CCX01 • CCX02 • CX20 • CCX12 • CCX01 • CCX01 ≈ CX21 • CCX01 • CCX12 • CX21 • CCX01
p0 = by-assoc-and (under (ε) (CCX01) B3180.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX02 • CX20 • CCX12 • CCX01 • CCX01 ≈ CCX01 • CCX02 • CX20 • CCX12
p1 = by-assoc-and (under (CCX01 • CCX02 • CX20 • CCX12) (ε) B11.proved) Eq.refl Eq.refl

p2 : CX21 • CCX01 • CCX12 • CX21 • CCX01 ≈ CCX01 • CCX02 • CX20 • CCX12
p2 = trans (sym p0) p1

p3 : CX21 • CCX01 • CCX12 • CX21 • CCX01 ≈ CX21 • CCX01 • CCX12 • CX21 • CCX01
p3 = refl

p4 : CCX01 • CCX02 • CX20 • CCX12 ≈ CCX01 • CCX02 • CX20 • CCX12
p4 = refl

p5 : CX21 • CCX01 • CCX12 • CX21 • CCX01 ≈ CCX01 • CCX02 • CX20 • CCX12
p5 = trans (sym p3) (trans p2 p4)

proved : CX21 • CCX01 • CCX12 • CX21 • CCX01 ≈ CCX01 • CCX02 • CX20 • CCX12
proved = p5
