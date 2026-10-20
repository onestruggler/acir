{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0323 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX20 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0014 as B14
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0040 as B40
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0212 as B212

p0 : CCX12 • CCX12 • CCX01 • CCX12 ≈ CCX12 • CX20 • CCX01 • CX20
p0 = by-assoc-and (under (CCX12) (ε) B212.proved) Eq.refl Eq.refl

p1 : CCX12 • CCX12 • CCX01 • CCX12 ≈ CCX01 • CCX12
p1 = by-assoc-and (under (ε) (CCX01 • CCX12) B14.proved) Eq.refl Eq.refl

p2 : CCX12 • CX20 • CCX01 • CX20 ≈ CCX01 • CCX12
p2 = trans (sym p0) p1

p3 : CCX12 • CX20 • CCX01 • CX20 ≈ CX20 • CCX12 • CCX01 • CX20
p3 = by-assoc-and (under (ε) (CCX01 • CX20) B40.proved) Eq.refl Eq.refl

p4 : CCX12 • CX20 • CCX01 • CX20 ≈ CX20 • CCX12 • CCX01 • CX20
p4 = trans p3 (refl)

p5 : CCX01 • CCX12 ≈ CCX01 • CCX12
p5 = refl

p6 : CX20 • CCX12 • CCX01 • CX20 ≈ CCX01 • CCX12
p6 = trans (sym p4) (trans p2 p5)

proved : CX20 • CCX12 • CCX01 • CX20 ≈ CCX01 • CCX12
proved = p6
