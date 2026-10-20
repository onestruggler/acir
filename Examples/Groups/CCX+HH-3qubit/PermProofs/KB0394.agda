{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0394 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX01 ; CX02 ; CX12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0031 as B31
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0123 as B123
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0164 as B164

p0 : CX01 • CX02 • CCX01 • CX12 ≈ CCX01 • CX01 • CX12
p0 = by-assoc-and (under (ε) (CX12) B123.proved) Eq.refl Eq.refl

p1 : CX01 • CX02 • CCX01 • CX12 ≈ CX01 • CX02 • CX12 • CCX01
p1 = by-assoc-and (under (CX01 • CX02) (ε) B31.proved) Eq.refl Eq.refl

p2 : CCX01 • CX01 • CX12 ≈ CX01 • CX02 • CX12 • CCX01
p2 = trans (sym p0) p1

p3 : CCX01 • CX01 • CX12 ≈ CCX01 • CX01 • CX12
p3 = refl

p4 : CX01 • CX02 • CX12 • CCX01 ≈ CX12 • CX01 • CCX01
p4 = by-assoc-and (under (ε) (CCX01) B164.proved) Eq.refl Eq.refl

p5 : CX01 • CX02 • CX12 • CCX01 ≈ CX12 • CX01 • CCX01
p5 = trans p4 (refl)

p6 : CCX01 • CX01 • CX12 ≈ CX12 • CX01 • CCX01
p6 = trans (sym p3) (trans p2 p5)

proved : CCX01 • CX01 • CX12 ≈ CX12 • CX01 • CCX01
proved = p6
