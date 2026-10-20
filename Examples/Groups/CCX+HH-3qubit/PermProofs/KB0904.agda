{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0904 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CX01 ; CX02 ; CX12 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0164 as B164
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0188 as B188

p0 : CCX02 • X2 • CX01 • CX02 • CX12 ≈ X2 • CCX02 • CX02 • CX12
p0 = by-assoc-and (under (ε) (CX02 • CX12) B188.proved) Eq.refl Eq.refl

p1 : CCX02 • X2 • CX01 • CX02 • CX12 ≈ CCX02 • X2 • CX12 • CX01
p1 = by-assoc-and (under (CCX02 • X2) (ε) B164.proved) Eq.refl Eq.refl

p2 : X2 • CCX02 • CX02 • CX12 ≈ CCX02 • X2 • CX12 • CX01
p2 = trans (sym p0) p1

p3 : X2 • CCX02 • CX02 • CX12 ≈ X2 • CCX02 • CX02 • CX12
p3 = refl

p4 : CCX02 • X2 • CX12 • CX01 ≈ CCX02 • X2 • CX12 • CX01
p4 = refl

p5 : X2 • CCX02 • CX02 • CX12 ≈ CCX02 • X2 • CX12 • CX01
p5 = trans (sym p3) (trans p2 p4)

p6 : CCX02 • X2 • CX12 • CX01 ≈ X2 • CCX02 • CX02 • CX12
p6 = sym p5

proved : CCX02 • X2 • CX12 • CX01 ≈ X2 • CCX02 • CX02 • CX12
proved = p6
