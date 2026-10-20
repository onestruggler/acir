{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0324 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX20 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0009 as B9
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0323 as B323

p0 : CX20 • CX20 • CCX12 • CCX01 • CX20 ≈ CX20 • CCX01 • CCX12
p0 = by-assoc-and (under (CX20) (ε) B323.proved) Eq.refl Eq.refl

p1 : CX20 • CX20 • CCX12 • CCX01 • CX20 ≈ CCX12 • CCX01 • CX20
p1 = by-assoc-and (under (ε) (CCX12 • CCX01 • CX20) B9.proved) Eq.refl Eq.refl

p2 : CX20 • CCX01 • CCX12 ≈ CCX12 • CCX01 • CX20
p2 = trans (sym p0) p1

p3 : CX20 • CCX01 • CCX12 ≈ CX20 • CCX01 • CCX12
p3 = refl

p4 : CCX12 • CCX01 • CX20 ≈ CCX12 • CCX01 • CX20
p4 = refl

p5 : CX20 • CCX01 • CCX12 ≈ CCX12 • CCX01 • CX20
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX12 • CCX01 • CX20 ≈ CX20 • CCX01 • CCX12
p6 = sym p5

proved : CCX12 • CCX01 • CX20 ≈ CX20 • CCX01 • CCX12
proved = p6
