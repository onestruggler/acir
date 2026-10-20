{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0795 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX02 ; CX12 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0029 as B29
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0031 as B31
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0033 as B33
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0120 as B120
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0144 as B144

p0 : CX02 • CCX01 • X1 • CX12 • X1 ≈ CX02 • CCX01 • X2 • CX12
p0 = by-assoc-and (under (CX02 • CCX01) (ε) B144.proved) Eq.refl Eq.refl

p1 : CX02 • CCX01 • X1 • CX12 • X1 ≈ X1 • CCX01 • CX12 • X1
p1 = by-assoc-and (under (ε) (CX12 • X1) B120.proved) Eq.refl Eq.refl

p2 : CX02 • CCX01 • X2 • CX12 ≈ X1 • CCX01 • CX12 • X1
p2 = trans (sym p0) p1

p3 : CX02 • CCX01 • X2 • CX12 ≈ CX02 • X2 • CCX01 • CX12
p3 = by-assoc-and (under (CX02) (CX12) B29.proved) Eq.refl Eq.refl

p4 : CX02 • X2 • CCX01 • CX12 ≈ X2 • CX02 • CCX01 • CX12
p4 = by-assoc-and (under (ε) (CCX01 • CX12) B33.proved) Eq.refl Eq.refl

p5 : X2 • CX02 • CCX01 • CX12 ≈ X2 • CX02 • CX12 • CCX01
p5 = by-assoc-and (under (X2 • CX02) (ε) B31.proved) Eq.refl Eq.refl

p6 : CX02 • CCX01 • X2 • CX12 ≈ X2 • CX02 • CX12 • CCX01
p6 = trans p3 (trans p4 (trans p5 (refl)))

p7 : X1 • CCX01 • CX12 • X1 ≈ X1 • CX12 • CCX01 • X1
p7 = by-assoc-and (under (X1) (X1) B31.proved) Eq.refl Eq.refl

p8 : X1 • CCX01 • CX12 • X1 ≈ X1 • CX12 • CCX01 • X1
p8 = trans p7 (refl)

p9 : X2 • CX02 • CX12 • CCX01 ≈ X1 • CX12 • CCX01 • X1
p9 = trans (sym p6) (trans p2 p8)

proved : X2 • CX02 • CX12 • CCX01 ≈ X1 • CX12 • CCX01 • X1
proved = p9
