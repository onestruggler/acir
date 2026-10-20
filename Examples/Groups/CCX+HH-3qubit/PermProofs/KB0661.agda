{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0661 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX20 ; CX21 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0138 as B138
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0325 as B325

p0 : CCX01 • CX20 • CCX12 • CX21 ≈ CX20 • CCX12 • CCX01 • CX21
p0 = by-assoc-and (under (ε) (CX21) B325.proved) Eq.refl Eq.refl

p1 : CCX01 • CX20 • CCX12 • CX21 ≈ CCX01 • CX21 • CCX12
p1 = by-assoc-and (under (CCX01) (ε) B138.proved) Eq.refl Eq.refl

p2 : CX20 • CCX12 • CCX01 • CX21 ≈ CCX01 • CX21 • CCX12
p2 = trans (sym p0) p1

p3 : CX20 • CCX12 • CCX01 • CX21 ≈ CX20 • CCX12 • CCX01 • CX21
p3 = refl

p4 : CCX01 • CX21 • CCX12 ≈ CCX01 • CX21 • CCX12
p4 = refl

p5 : CX20 • CCX12 • CCX01 • CX21 ≈ CCX01 • CX21 • CCX12
p5 = trans (sym p3) (trans p2 p4)

proved : CX20 • CCX12 • CCX01 • CX21 ≈ CCX01 • CX21 • CCX12
proved = p5
