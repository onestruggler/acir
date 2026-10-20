{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0322 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX02 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0008 as B8
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0037 as B37
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0320 as B320

p0 : CX02 • CCX01 • CCX12 • CX02 • CX02 ≈ CCX12 • CCX01 • CX02
p0 = by-assoc-and (under (ε) (CX02) B320.proved) Eq.refl Eq.refl

p1 : CX02 • CCX01 • CCX12 • CX02 • CX02 ≈ CX02 • CCX01 • CCX12
p1 = by-assoc-and (under (CX02 • CCX01 • CCX12) (ε) B8.proved) Eq.refl Eq.refl

p2 : CCX12 • CCX01 • CX02 ≈ CX02 • CCX01 • CCX12
p2 = trans (sym p0) p1

p3 : CCX12 • CCX01 • CX02 ≈ CCX12 • CX02 • CCX01
p3 = by-assoc-and (under (CCX12) (ε) B37.proved) Eq.refl Eq.refl

p4 : CCX12 • CCX01 • CX02 ≈ CCX12 • CX02 • CCX01
p4 = trans p3 (refl)

p5 : CX02 • CCX01 • CCX12 ≈ CX02 • CCX01 • CCX12
p5 = refl

p6 : CCX12 • CX02 • CCX01 ≈ CX02 • CCX01 • CCX12
p6 = trans (sym p4) (trans p2 p5)

proved : CCX12 • CX02 • CCX01 ≈ CX02 • CCX01 • CCX12
proved = p6
