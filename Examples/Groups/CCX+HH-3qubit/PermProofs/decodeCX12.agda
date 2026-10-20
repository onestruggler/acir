{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.decodeCX12 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX12 ; X0 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0153 as B153

p0 : CX12 ≈ CX12
p0 = refl

p1 : X0 • CCX01 • X0 • CCX01 ≈ CX12 • CCX01 • CCX01
p1 = by-assoc-and (under (ε) (CCX01) B153.proved) Eq.refl Eq.refl

p2 : CX12 • CCX01 • CCX01 ≈ CX12
p2 = by-assoc-and (under (CX12) (ε) B11.proved) Eq.refl Eq.refl

p3 : X0 • CCX01 • X0 • CCX01 ≈ CX12
p3 = trans p1 (trans p2 (refl))

proved : CX12 ≈ X0 • CCX01 • X0 • CCX01
proved = trans p0 (sym p3)
