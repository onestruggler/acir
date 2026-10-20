{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0815 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX02 ; CX12 ; X0 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0044 as B44
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0151 as B151
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0152 as B152

p0 : X1 • CX02 • CCX01 • X0 • CCX01 ≈ X1 • CX02 • X0 • CX12
p0 = by-assoc-and (under (X1 • CX02) (ε) B152.proved) Eq.refl Eq.refl

p1 : X1 • CX02 • CCX01 • X0 • CCX01 ≈ CCX01 • X1 • X0 • CCX01
p1 = by-assoc-and (under (ε) (X0 • CCX01) B151.proved) Eq.refl Eq.refl

p2 : X1 • CX02 • X0 • CX12 ≈ CCX01 • X1 • X0 • CCX01
p2 = trans (sym p0) p1

p3 : X1 • CX02 • X0 • CX12 ≈ X1 • CX02 • X0 • CX12
p3 = refl

p4 : CCX01 • X1 • X0 • CCX01 ≈ CCX01 • X0 • X1 • CCX01
p4 = by-assoc-and (under (CCX01) (CCX01) B44.proved) Eq.refl Eq.refl

p5 : CCX01 • X1 • X0 • CCX01 ≈ CCX01 • X0 • X1 • CCX01
p5 = trans p4 (refl)

p6 : X1 • CX02 • X0 • CX12 ≈ CCX01 • X0 • X1 • CCX01
p6 = trans (sym p3) (trans p2 p5)

p7 : CCX01 • X0 • X1 • CCX01 ≈ X1 • CX02 • X0 • CX12
p7 = sym p6

proved : CCX01 • X0 • X1 • CCX01 ≈ X1 • CX02 • X0 • CX12
proved = p7
