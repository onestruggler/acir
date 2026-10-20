{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1823 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX12 ; CX20 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0035 as B35
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0362 as B362
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1228 as B1228

p0 : CX01 • X1 • CX20 • X2 • CX12 ≈ CX01 • CX20 • CX12 • X1
p0 = by-assoc-and (under (CX01) (ε) B362.proved) Eq.refl Eq.refl

p1 : CX01 • X1 • CX20 • X2 • CX12 ≈ X1 • CX01 • CX20 • X2 • CX12
p1 = by-assoc-and (under (ε) (CX20 • X2 • CX12) B35.proved) Eq.refl Eq.refl

p2 : CX01 • CX20 • CX12 • X1 ≈ X1 • CX01 • CX20 • X2 • CX12
p2 = trans (sym p0) p1

p3 : CX01 • CX20 • CX12 • X1 ≈ CX01 • CX20 • CX12 • X1
p3 = refl

p4 : X1 • CX01 • CX20 • X2 • CX12 ≈ X0 • X2 • CX01 • CX20 • CX12
p4 = by-assoc-and (under (ε) (CX12) B1228.proved) Eq.refl Eq.refl

p5 : X1 • CX01 • CX20 • X2 • CX12 ≈ X0 • X2 • CX01 • CX20 • CX12
p5 = trans p4 (refl)

p6 : CX01 • CX20 • CX12 • X1 ≈ X0 • X2 • CX01 • CX20 • CX12
p6 = trans (sym p3) (trans p2 p5)

p7 : X0 • X2 • CX01 • CX20 • CX12 ≈ CX01 • CX20 • CX12 • X1
p7 = sym p6

proved : X0 • X2 • CX01 • CX20 • CX12 ≈ CX01 • CX20 • CX12 • X1
proved = p7
