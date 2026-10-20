{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB2062 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX12 ; CX01 ; CX02 ; CX10 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0025 as B25
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0033 as B33
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0423 as B423

p0 : CX02 • X2 • CX01 • CX10 • CCX12 ≈ CX02 • CX01 • CCX12 • X2
p0 = by-assoc-and (under (CX02) (ε) B423.proved) Eq.refl Eq.refl

p1 : CX02 • X2 • CX01 • CX10 • CCX12 ≈ X2 • CX02 • CX01 • CX10 • CCX12
p1 = by-assoc-and (under (ε) (CX01 • CX10 • CCX12) B33.proved) Eq.refl Eq.refl

p2 : CX02 • CX01 • CCX12 • X2 ≈ X2 • CX02 • CX01 • CX10 • CCX12
p2 = trans (sym p0) p1

p3 : CX02 • CX01 • CCX12 • X2 ≈ CX01 • CX02 • CCX12 • X2
p3 = by-assoc-and (under (ε) (CCX12 • X2) B25.proved) Eq.refl Eq.refl

p4 : CX02 • CX01 • CCX12 • X2 ≈ CX01 • CX02 • CCX12 • X2
p4 = trans p3 (refl)

p5 : X2 • CX02 • CX01 • CX10 • CCX12 ≈ X2 • CX01 • CX02 • CX10 • CCX12
p5 = by-assoc-and (under (X2) (CX10 • CCX12) B25.proved) Eq.refl Eq.refl

p6 : X2 • CX02 • CX01 • CX10 • CCX12 ≈ X2 • CX01 • CX02 • CX10 • CCX12
p6 = trans p5 (refl)

p7 : CX01 • CX02 • CCX12 • X2 ≈ X2 • CX01 • CX02 • CX10 • CCX12
p7 = trans (sym p4) (trans p2 p6)

p8 : X2 • CX01 • CX02 • CX10 • CCX12 ≈ CX01 • CX02 • CCX12 • X2
p8 = sym p7

proved : X2 • CX01 • CX02 • CX10 • CCX12 ≈ CX01 • CX02 • CCX12 • X2
proved = p8
