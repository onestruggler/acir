{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB2662 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX02 ; CX12 ; X0 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0037 as B37
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0703 as B703

p0 : CCX01 • CCX02 • X0 • CCX01 • CX02 ≈ CX12 • CCX02 • X0 • CX02
p0 = by-assoc-and (under (ε) (CX02) B703.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX02 • X0 • CCX01 • CX02 ≈ CCX01 • CCX02 • X0 • CX02 • CCX01
p1 = by-assoc-and (under (CCX01 • CCX02 • X0) (ε) B37.proved) Eq.refl Eq.refl

p2 : CX12 • CCX02 • X0 • CX02 ≈ CCX01 • CCX02 • X0 • CX02 • CCX01
p2 = trans (sym p0) p1

p3 : CX12 • CCX02 • X0 • CX02 ≈ CX12 • CCX02 • X0 • CX02
p3 = refl

p4 : CCX01 • CCX02 • X0 • CX02 • CCX01 ≈ CCX01 • CCX02 • X0 • CX02 • CCX01
p4 = refl

p5 : CX12 • CCX02 • X0 • CX02 ≈ CCX01 • CCX02 • X0 • CX02 • CCX01
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX01 • CCX02 • X0 • CX02 • CCX01 ≈ CX12 • CCX02 • X0 • CX02
p6 = sym p5

proved : CCX01 • CCX02 • X0 • CX02 • CCX01 ≈ CX12 • CCX02 • X0 • CX02
proved = p6
