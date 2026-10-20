{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0483 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX12 ; X0 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0044 as B44
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0153 as B153

p0 : X1 • X0 • CCX01 • X0 ≈ X1 • CX12 • CCX01
p0 = by-assoc-and (under (X1) (ε) B153.proved) Eq.refl Eq.refl

p1 : X1 • X0 • CCX01 • X0 ≈ X0 • X1 • CCX01 • X0
p1 = by-assoc-and (under (ε) (CCX01 • X0) B44.proved) Eq.refl Eq.refl

p2 : X1 • CX12 • CCX01 ≈ X0 • X1 • CCX01 • X0
p2 = trans (sym p0) p1

p3 : X1 • CX12 • CCX01 ≈ X1 • CX12 • CCX01
p3 = refl

p4 : X0 • X1 • CCX01 • X0 ≈ X0 • X1 • CCX01 • X0
p4 = refl

p5 : X1 • CX12 • CCX01 ≈ X0 • X1 • CCX01 • X0
p5 = trans (sym p3) (trans p2 p4)

p6 : X0 • X1 • CCX01 • X0 ≈ X1 • CX12 • CCX01
p6 = sym p5

proved : X0 • X1 • CCX01 • X0 ≈ X1 • CX12 • CCX01
proved = p6
