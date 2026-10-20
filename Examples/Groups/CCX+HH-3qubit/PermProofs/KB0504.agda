{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0504 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CX01 ; CX02 ; CX12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0038 as B38
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0119 as B119
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0164 as B164

p0 : CCX02 • CX01 • CX02 • CX12 ≈ CCX02 • CX12 • CX01
p0 = by-assoc-and (under (CCX02) (ε) B164.proved) Eq.refl Eq.refl

p1 : CCX02 • CX01 • CX02 • CX12 ≈ CX01 • CCX02 • CX02 • CX12
p1 = by-assoc-and (under (ε) (CX02 • CX12) B38.proved) Eq.refl Eq.refl

p2 : CCX02 • CX12 • CX01 ≈ CX01 • CCX02 • CX02 • CX12
p2 = trans (sym p0) p1

p3 : CCX02 • CX12 • CX01 ≈ CCX02 • CX12 • CX01
p3 = refl

p4 : CX01 • CCX02 • CX02 • CX12 ≈ CX02 • CCX02 • CX12
p4 = by-assoc-and (under (ε) (CX12) B119.proved) Eq.refl Eq.refl

p5 : CX01 • CCX02 • CX02 • CX12 ≈ CX02 • CCX02 • CX12
p5 = trans p4 (refl)

p6 : CCX02 • CX12 • CX01 ≈ CX02 • CCX02 • CX12
p6 = trans (sym p3) (trans p2 p5)

proved : CCX02 • CX12 • CX01 ≈ CX02 • CCX02 • CX12
proved = p6
