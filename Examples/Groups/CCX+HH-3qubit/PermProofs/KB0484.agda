{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0484 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX12 ; X0 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0046 as B46
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0153 as B153

p0 : CCX12 • X0 • CCX01 • X0 ≈ CCX12 • CX12 • CCX01
p0 = by-assoc-and (under (CCX12) (ε) B153.proved) Eq.refl Eq.refl

p1 : CCX12 • X0 • CCX01 • X0 ≈ X0 • CCX12 • CCX01 • X0
p1 = by-assoc-and (under (ε) (CCX01 • X0) B46.proved) Eq.refl Eq.refl

p2 : CCX12 • CX12 • CCX01 ≈ X0 • CCX12 • CCX01 • X0
p2 = trans (sym p0) p1

p3 : CCX12 • CX12 • CCX01 ≈ CCX12 • CX12 • CCX01
p3 = refl

p4 : X0 • CCX12 • CCX01 • X0 ≈ X0 • CCX12 • CCX01 • X0
p4 = refl

p5 : CCX12 • CX12 • CCX01 ≈ X0 • CCX12 • CCX01 • X0
p5 = trans (sym p3) (trans p2 p4)

p6 : X0 • CCX12 • CCX01 • X0 ≈ CCX12 • CX12 • CCX01
p6 = sym p5

proved : X0 • CCX12 • CCX01 • X0 ≈ CCX12 • CX12 • CCX01
proved = p6
