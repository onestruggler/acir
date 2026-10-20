{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1322 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CX01 ; CX02 ; CX12 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0035 as B35
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0504 as B504

p0 : CCX02 • CX12 • CX01 • X1 ≈ CX02 • CCX02 • CX12 • X1
p0 = by-assoc-and (under (ε) (X1) B504.proved) Eq.refl Eq.refl

p1 : CCX02 • CX12 • CX01 • X1 ≈ CCX02 • CX12 • X1 • CX01
p1 = by-assoc-and (under (CCX02 • CX12) (ε) B35.proved) Eq.refl Eq.refl

p2 : CX02 • CCX02 • CX12 • X1 ≈ CCX02 • CX12 • X1 • CX01
p2 = trans (sym p0) p1

p3 : CX02 • CCX02 • CX12 • X1 ≈ CX02 • CCX02 • CX12 • X1
p3 = refl

p4 : CCX02 • CX12 • X1 • CX01 ≈ CCX02 • CX12 • X1 • CX01
p4 = refl

p5 : CX02 • CCX02 • CX12 • X1 ≈ CCX02 • CX12 • X1 • CX01
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX02 • CX12 • X1 • CX01 ≈ CX02 • CCX02 • CX12 • X1
p6 = sym p5

proved : CCX02 • CX12 • X1 • CX01 ≈ CX02 • CCX02 • CX12 • X1
proved = p6
