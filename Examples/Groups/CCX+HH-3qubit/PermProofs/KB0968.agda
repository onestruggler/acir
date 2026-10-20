{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0968 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX12 ; CX20 ; CX21 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0043 as B43
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0217 as B217

p0 : CX21 • CCX01 • CX21 • CX20 ≈ CX12 • CCX02 • CX12 • CX20
p0 = by-assoc-and (under (ε) (CX20) B217.proved) Eq.refl Eq.refl

p1 : CX21 • CCX01 • CX21 • CX20 ≈ CX21 • CCX01 • CX20 • CX21
p1 = by-assoc-and (under (CX21 • CCX01) (ε) B43.proved) Eq.refl Eq.refl

p2 : CX12 • CCX02 • CX12 • CX20 ≈ CX21 • CCX01 • CX20 • CX21
p2 = trans (sym p0) p1

p3 : CX12 • CCX02 • CX12 • CX20 ≈ CX12 • CCX02 • CX12 • CX20
p3 = refl

p4 : CX21 • CCX01 • CX20 • CX21 ≈ CX21 • CCX01 • CX20 • CX21
p4 = refl

p5 : CX12 • CCX02 • CX12 • CX20 ≈ CX21 • CCX01 • CX20 • CX21
p5 = trans (sym p3) (trans p2 p4)

p6 : CX21 • CCX01 • CX20 • CX21 ≈ CX12 • CCX02 • CX12 • CX20
p6 = sym p5

proved : CX21 • CCX01 • CX20 • CX21 ≈ CX12 • CCX02 • CX12 • CX20
proved = p6
