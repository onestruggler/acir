{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0192 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX02 ; CX12 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0013 as B13
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0164 as B164

p0 : CX01 • CX01 • CX02 • CX12 ≈ CX01 • CX12 • CX01
p0 = by-assoc-and (under (CX01) (ε) B164.proved) Eq.refl Eq.refl

p1 : CX01 • CX01 • CX02 • CX12 ≈ CX02 • CX12
p1 = by-assoc-and (under (ε) (CX02 • CX12) B13.proved) Eq.refl Eq.refl

p2 : CX01 • CX12 • CX01 ≈ CX02 • CX12
p2 = trans (sym p0) p1

p3 : CX01 • CX12 • CX01 ≈ CX01 • CX12 • CX01
p3 = refl

p4 : CX02 • CX12 ≈ CX02 • CX12
p4 = refl

p5 : CX01 • CX12 • CX01 ≈ CX02 • CX12
p5 = trans (sym p3) (trans p2 p4)

proved : CX01 • CX12 • CX01 ≈ CX02 • CX12
proved = p5
