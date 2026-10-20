{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0306 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX12 ; CX01 ; CX20 ; CX21 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0179 as B179
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0303 as B303

p0 : CX01 • CX20 • CX21 • CCX12 ≈ CX20 • CX01 • CCX12
p0 = by-assoc-and (under (ε) (CCX12) B303.proved) Eq.refl Eq.refl

p1 : CX01 • CX20 • CX21 • CCX12 ≈ CX01 • CCX12 • CX21
p1 = by-assoc-and (under (CX01) (ε) B179.proved) Eq.refl Eq.refl

p2 : CX20 • CX01 • CCX12 ≈ CX01 • CCX12 • CX21
p2 = trans (sym p0) p1

p3 : CX20 • CX01 • CCX12 ≈ CX20 • CX01 • CCX12
p3 = refl

p4 : CX01 • CCX12 • CX21 ≈ CX01 • CCX12 • CX21
p4 = refl

p5 : CX20 • CX01 • CCX12 ≈ CX01 • CCX12 • CX21
p5 = trans (sym p3) (trans p2 p4)

proved : CX20 • CX01 • CCX12 ≈ CX01 • CCX12 • CX21
proved = p5
