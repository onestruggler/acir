{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0708 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX02 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0008 as B8
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0657 as B657

p0 : CX02 • CX02 • CCX01 • CCX12 • X1 ≈ CX02 • CCX12 • X1 • CCX01
p0 = by-assoc-and (under (CX02) (ε) B657.proved) Eq.refl Eq.refl

p1 : CX02 • CX02 • CCX01 • CCX12 • X1 ≈ CCX01 • CCX12 • X1
p1 = by-assoc-and (under (ε) (CCX01 • CCX12 • X1) B8.proved) Eq.refl Eq.refl

p2 : CX02 • CCX12 • X1 • CCX01 ≈ CCX01 • CCX12 • X1
p2 = trans (sym p0) p1

p3 : CX02 • CCX12 • X1 • CCX01 ≈ CX02 • CCX12 • X1 • CCX01
p3 = refl

p4 : CCX01 • CCX12 • X1 ≈ CCX01 • CCX12 • X1
p4 = refl

p5 : CX02 • CCX12 • X1 • CCX01 ≈ CCX01 • CCX12 • X1
p5 = trans (sym p3) (trans p2 p4)

proved : CX02 • CCX12 • X1 • CCX01 ≈ CCX01 • CCX12 • X1
proved = p5
