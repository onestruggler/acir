{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1365 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; CX01 ; CX20 ; CX21 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0030 as B30
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0306 as B306
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0338 as B338

p0 : CX20 • CX01 • CCX12 • CX01 • CCX12 ≈ CX20 • CCX12 • CCX02
p0 = by-assoc-and (under (CX20) (ε) B338.proved) Eq.refl Eq.refl

p1 : CX20 • CX01 • CCX12 • CX01 • CCX12 ≈ CX01 • CCX12 • CX21 • CX01 • CCX12
p1 = by-assoc-and (under (ε) (CX01 • CCX12) B306.proved) Eq.refl Eq.refl

p2 : CX20 • CCX12 • CCX02 ≈ CX01 • CCX12 • CX21 • CX01 • CCX12
p2 = trans (sym p0) p1

p3 : CX20 • CCX12 • CCX02 ≈ CX20 • CCX12 • CCX02
p3 = refl

p4 : CX01 • CCX12 • CX21 • CX01 • CCX12 ≈ CX01 • CCX12 • CX01 • CX21 • CCX12
p4 = by-assoc-and (under (CX01 • CCX12) (CCX12) B30.proved) Eq.refl Eq.refl

p5 : CX01 • CCX12 • CX21 • CX01 • CCX12 ≈ CX01 • CCX12 • CX01 • CX21 • CCX12
p5 = trans p4 (refl)

p6 : CX20 • CCX12 • CCX02 ≈ CX01 • CCX12 • CX01 • CX21 • CCX12
p6 = trans (sym p3) (trans p2 p5)

p7 : CX01 • CCX12 • CX01 • CX21 • CCX12 ≈ CX20 • CCX12 • CCX02
p7 = sym p6

proved : CX01 • CCX12 • CX01 • CX21 • CCX12 ≈ CX20 • CCX12 • CCX02
proved = p7
