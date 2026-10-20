{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0505 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX02 ; CX12 ; X0 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0164 as B164

p0 : CX01 • CX02 • CX12 • X0 ≈ CX12 • CX01 • X0
p0 = by-assoc-and (under (ε) (X0) B164.proved) Eq.refl Eq.refl

p1 : CX01 • CX02 • CX12 • X0 ≈ CX01 • CX02 • X0 • CX12
p1 = by-assoc-and (under (CX01 • CX02) (ε) B45.proved) Eq.refl Eq.refl

p2 : CX12 • CX01 • X0 ≈ CX01 • CX02 • X0 • CX12
p2 = trans (sym p0) p1

p3 : CX12 • CX01 • X0 ≈ CX12 • CX01 • X0
p3 = refl

p4 : CX01 • CX02 • X0 • CX12 ≈ CX01 • CX02 • X0 • CX12
p4 = refl

p5 : CX12 • CX01 • X0 ≈ CX01 • CX02 • X0 • CX12
p5 = trans (sym p3) (trans p2 p4)

p6 : CX01 • CX02 • X0 • CX12 ≈ CX12 • CX01 • X0
p6 = sym p5

proved : CX01 • CX02 • X0 • CX12 ≈ CX12 • CX01 • X0
proved = p6
