{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1439 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX01 ; CX02 ; CX12 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0028 as B28
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0203 as B203
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0214 as B214
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0222 as B222
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0285 as B285

p0 : CCX01 • CCX02 • CCX01 • X1 • CX02 ≈ CX12 • CCX02 • CX12 • X1 • CX02
p0 = by-assoc-and (under (ε) (X1 • CX02) B214.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX02 • CCX01 • X1 • CX02 ≈ CCX01 • CCX02 • X1 • CCX01
p1 = by-assoc-and (under (CCX01 • CCX02) (ε) B203.proved) Eq.refl Eq.refl

p2 : CX12 • CCX02 • CX12 • X1 • CX02 ≈ CCX01 • CCX02 • X1 • CCX01
p2 = trans (sym p0) p1

p3 : CX12 • CCX02 • CX12 • X1 • CX02 ≈ CX12 • CCX02 • CX02 • CX12 • X1
p3 = by-assoc-and (under (CX12 • CCX02) (ε) B222.proved) Eq.refl Eq.refl

p4 : CX12 • CCX02 • CX02 • CX12 • X1 ≈ CX01 • CX12 • CCX02 • CX12 • X1
p4 = by-assoc-and (under (ε) (CX12 • X1) B285.proved) Eq.refl Eq.refl

p5 : CX12 • CCX02 • CX12 • X1 • CX02 ≈ CX01 • CX12 • CCX02 • CX12 • X1
p5 = trans p3 (trans p4 (refl))

p6 : CCX01 • CCX02 • X1 • CCX01 ≈ CCX01 • X1 • CCX02 • CCX01
p6 = by-assoc-and (under (CCX01) (CCX01) B28.proved) Eq.refl Eq.refl

p7 : CCX01 • CCX02 • X1 • CCX01 ≈ CCX01 • X1 • CCX02 • CCX01
p7 = trans p6 (refl)

p8 : CX01 • CX12 • CCX02 • CX12 • X1 ≈ CCX01 • X1 • CCX02 • CCX01
p8 = trans (sym p5) (trans p2 p7)

proved : CX01 • CX12 • CCX02 • CX12 • X1 ≈ CCX01 • X1 • CCX02 • CCX01
proved = p8
