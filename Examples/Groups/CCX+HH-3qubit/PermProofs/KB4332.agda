{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB4332 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; CX01 ; CX20 ; X0 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0170 as B170
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0826 as B826

p0 : CX01 • X0 • CCX01 • X1 • CX20 • CCX12 ≈ X0 • CCX01 • CX01 • CX20 • CCX12
p0 = by-assoc-and (under (ε) (CX20 • CCX12) B826.proved) Eq.refl Eq.refl

p1 : CX01 • X0 • CCX01 • X1 • CX20 • CCX12 ≈ CX01 • X0 • CCX01 • CCX12 • X1
p1 = by-assoc-and (under (CX01 • X0 • CCX01) (ε) B170.proved) Eq.refl Eq.refl

p2 : X0 • CCX01 • CX01 • CX20 • CCX12 ≈ CX01 • X0 • CCX01 • CCX12 • X1
p2 = trans (sym p0) p1

p3 : X0 • CCX01 • CX01 • CX20 • CCX12 ≈ X0 • CCX01 • CX01 • CX20 • CCX12
p3 = refl

p4 : CX01 • X0 • CCX01 • CCX12 • X1 ≈ CX01 • X0 • CCX01 • CCX12 • X1
p4 = refl

p5 : X0 • CCX01 • CX01 • CX20 • CCX12 ≈ CX01 • X0 • CCX01 • CCX12 • X1
p5 = trans (sym p3) (trans p2 p4)

p6 : CX01 • X0 • CCX01 • CCX12 • X1 ≈ X0 • CCX01 • CX01 • CX20 • CCX12
p6 = sym p5

proved : CX01 • X0 • CCX01 • CCX12 • X1 ≈ X0 • CCX01 • CX01 • CX20 • CCX12
proved = p6
