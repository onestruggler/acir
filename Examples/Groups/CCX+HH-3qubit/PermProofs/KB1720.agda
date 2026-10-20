{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1720 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX01 ; CX12 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0122 as B122
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0332 as B332

p0 : X2 • CX01 • CCX02 • CX12 • CCX02 ≈ X2 • CX01 • CX12 • CCX02 • CCX01
p0 = by-assoc-and (under (X2 • CX01) (ε) B332.proved) Eq.refl Eq.refl

p1 : X2 • CX01 • CCX02 • CX12 • CCX02 ≈ CCX02 • X2 • CX12 • CCX02
p1 = by-assoc-and (under (ε) (CX12 • CCX02) B122.proved) Eq.refl Eq.refl

p2 : X2 • CX01 • CX12 • CCX02 • CCX01 ≈ CCX02 • X2 • CX12 • CCX02
p2 = trans (sym p0) p1

p3 : X2 • CX01 • CX12 • CCX02 • CCX01 ≈ X2 • CX01 • CX12 • CCX02 • CCX01
p3 = refl

p4 : CCX02 • X2 • CX12 • CCX02 ≈ CCX02 • X2 • CX12 • CCX02
p4 = refl

p5 : X2 • CX01 • CX12 • CCX02 • CCX01 ≈ CCX02 • X2 • CX12 • CCX02
p5 = trans (sym p3) (trans p2 p4)

proved : X2 • CX01 • CX12 • CCX02 • CCX01 ≈ CCX02 • X2 • CX12 • CCX02
proved = p5
