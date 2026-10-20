{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0657 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX02 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0120 as B120
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0322 as B322

p0 : CCX12 • CX02 • CCX01 • X1 ≈ CX02 • CCX01 • CCX12 • X1
p0 = by-assoc-and (under (ε) (X1) B322.proved) Eq.refl Eq.refl

p1 : CCX12 • CX02 • CCX01 • X1 ≈ CCX12 • X1 • CCX01
p1 = by-assoc-and (under (CCX12) (ε) B120.proved) Eq.refl Eq.refl

p2 : CX02 • CCX01 • CCX12 • X1 ≈ CCX12 • X1 • CCX01
p2 = trans (sym p0) p1

p3 : CX02 • CCX01 • CCX12 • X1 ≈ CX02 • CCX01 • CCX12 • X1
p3 = refl

p4 : CCX12 • X1 • CCX01 ≈ CCX12 • X1 • CCX01
p4 = refl

p5 : CX02 • CCX01 • CCX12 • X1 ≈ CCX12 • X1 • CCX01
p5 = trans (sym p3) (trans p2 p4)

proved : CX02 • CCX01 • CCX12 • X1 ≈ CCX12 • X1 • CCX01
proved = p5
