{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0655 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX01 ; CX02 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0123 as B123
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0320 as B320

p0 : CX01 • CX02 • CCX01 • CCX12 • CX02 ≈ CX01 • CCX12 • CCX01
p0 = by-assoc-and (under (CX01) (ε) B320.proved) Eq.refl Eq.refl

p1 : CX01 • CX02 • CCX01 • CCX12 • CX02 ≈ CCX01 • CX01 • CCX12 • CX02
p1 = by-assoc-and (under (ε) (CCX12 • CX02) B123.proved) Eq.refl Eq.refl

p2 : CX01 • CCX12 • CCX01 ≈ CCX01 • CX01 • CCX12 • CX02
p2 = trans (sym p0) p1

p3 : CX01 • CCX12 • CCX01 ≈ CX01 • CCX12 • CCX01
p3 = refl

p4 : CCX01 • CX01 • CCX12 • CX02 ≈ CCX01 • CX01 • CCX12 • CX02
p4 = refl

p5 : CX01 • CCX12 • CCX01 ≈ CCX01 • CX01 • CCX12 • CX02
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX01 • CX01 • CCX12 • CX02 ≈ CX01 • CCX12 • CCX01
p6 = sym p5

proved : CCX01 • CX01 • CCX12 • CX02 ≈ CX01 • CCX12 • CCX01
proved = p6
