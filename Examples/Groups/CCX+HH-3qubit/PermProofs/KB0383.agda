{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0383 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX12 ; X0 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0018 as B18
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0121 as B121

p0 : X2 • X0 • CX12 • CCX01 ≈ X2 • CCX01 • X0
p0 = by-assoc-and (under (X2) (ε) B121.proved) Eq.refl Eq.refl

p1 : X2 • X0 • CX12 • CCX01 ≈ X0 • X2 • CX12 • CCX01
p1 = by-assoc-and (under (ε) (CX12 • CCX01) B18.proved) Eq.refl Eq.refl

p2 : X2 • CCX01 • X0 ≈ X0 • X2 • CX12 • CCX01
p2 = trans (sym p0) p1

p3 : X2 • CCX01 • X0 ≈ X2 • CCX01 • X0
p3 = refl

p4 : X0 • X2 • CX12 • CCX01 ≈ X0 • X2 • CX12 • CCX01
p4 = refl

p5 : X2 • CCX01 • X0 ≈ X0 • X2 • CX12 • CCX01
p5 = trans (sym p3) (trans p2 p4)

p6 : X0 • X2 • CX12 • CCX01 ≈ X2 • CCX01 • X0
p6 = sym p5

proved : X0 • X2 • CX12 • CCX01 ≈ X2 • CCX01 • X0
proved = p6
