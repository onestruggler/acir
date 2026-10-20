{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0399 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX12 ; X0 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0124 as B124

p0 : CX12 • X0 • X1 • CX01 ≈ CX12 • CX01 • X0
p0 = by-assoc-and (under (CX12) (ε) B124.proved) Eq.refl Eq.refl

p1 : CX12 • X0 • X1 • CX01 ≈ X0 • CX12 • X1 • CX01
p1 = by-assoc-and (under (ε) (X1 • CX01) B45.proved) Eq.refl Eq.refl

p2 : CX12 • CX01 • X0 ≈ X0 • CX12 • X1 • CX01
p2 = trans (sym p0) p1

p3 : CX12 • CX01 • X0 ≈ CX12 • CX01 • X0
p3 = refl

p4 : X0 • CX12 • X1 • CX01 ≈ X0 • CX12 • X1 • CX01
p4 = refl

p5 : CX12 • CX01 • X0 ≈ X0 • CX12 • X1 • CX01
p5 = trans (sym p3) (trans p2 p4)

p6 : X0 • CX12 • X1 • CX01 ≈ CX12 • CX01 • X0
p6 = sym p5

proved : X0 • CX12 • X1 • CX01 ≈ CX12 • CX01 • X0
proved = p6
