{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0623 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX12 ; X0 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0140 as B140
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0307 as B307

p0 : CX12 • CCX02 • CX12 • CCX01 • X0 ≈ CCX01 • CCX02 • X0
p0 = by-assoc-and (under (ε) (X0) B307.proved) Eq.refl Eq.refl

p1 : CX12 • CCX02 • CX12 • CCX01 • X0 ≈ CX12 • CCX02 • X0 • CCX01
p1 = by-assoc-and (under (CX12 • CCX02) (ε) B140.proved) Eq.refl Eq.refl

p2 : CCX01 • CCX02 • X0 ≈ CX12 • CCX02 • X0 • CCX01
p2 = trans (sym p0) p1

p3 : CCX01 • CCX02 • X0 ≈ CCX01 • CCX02 • X0
p3 = refl

p4 : CX12 • CCX02 • X0 • CCX01 ≈ CX12 • CCX02 • X0 • CCX01
p4 = refl

p5 : CCX01 • CCX02 • X0 ≈ CX12 • CCX02 • X0 • CCX01
p5 = trans (sym p3) (trans p2 p4)

p6 : CX12 • CCX02 • X0 • CCX01 ≈ CCX01 • CCX02 • X0
p6 = sym p5

proved : CX12 • CCX02 • X0 • CCX01 ≈ CCX01 • CCX02 • X0
proved = p6
