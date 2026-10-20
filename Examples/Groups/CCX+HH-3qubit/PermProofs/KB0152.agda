{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0152 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX12 ; X0 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0121 as B121

p0 : X0 • CX12 • CCX01 • CCX01 ≈ CCX01 • X0 • CCX01
p0 = by-assoc-and (under (ε) (CCX01) B121.proved) Eq.refl Eq.refl

p1 : X0 • CX12 • CCX01 • CCX01 ≈ X0 • CX12
p1 = by-assoc-and (under (X0 • CX12) (ε) B11.proved) Eq.refl Eq.refl

p2 : CCX01 • X0 • CCX01 ≈ X0 • CX12
p2 = trans (sym p0) p1

p3 : CCX01 • X0 • CCX01 ≈ CCX01 • X0 • CCX01
p3 = refl

p4 : X0 • CX12 ≈ X0 • CX12
p4 = refl

p5 : CCX01 • X0 • CCX01 ≈ X0 • CX12
p5 = trans (sym p3) (trans p2 p4)

proved : CCX01 • X0 • CCX01 ≈ X0 • CX12
proved = p5
