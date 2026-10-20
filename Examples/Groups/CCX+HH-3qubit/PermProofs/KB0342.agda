{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0342 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; CX01 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0013 as B13
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0038 as B38
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0340 as B340

p0 : CX01 • CCX02 • CCX12 • CX01 • CX01 ≈ CCX12 • CCX02 • CX01
p0 = by-assoc-and (under (ε) (CX01) B340.proved) Eq.refl Eq.refl

p1 : CX01 • CCX02 • CCX12 • CX01 • CX01 ≈ CX01 • CCX02 • CCX12
p1 = by-assoc-and (under (CX01 • CCX02 • CCX12) (ε) B13.proved) Eq.refl Eq.refl

p2 : CCX12 • CCX02 • CX01 ≈ CX01 • CCX02 • CCX12
p2 = trans (sym p0) p1

p3 : CCX12 • CCX02 • CX01 ≈ CCX12 • CX01 • CCX02
p3 = by-assoc-and (under (CCX12) (ε) B38.proved) Eq.refl Eq.refl

p4 : CCX12 • CCX02 • CX01 ≈ CCX12 • CX01 • CCX02
p4 = trans p3 (refl)

p5 : CX01 • CCX02 • CCX12 ≈ CX01 • CCX02 • CCX12
p5 = refl

p6 : CCX12 • CX01 • CCX02 ≈ CX01 • CCX02 • CCX12
p6 = trans (sym p4) (trans p2 p5)

proved : CCX12 • CX01 • CCX02 ≈ CX01 • CCX02 • CCX12
proved = p6
