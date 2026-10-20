{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1925 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX12 ; CX20 ; X0 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0309 as B309
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0318 as B318
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0383 as B383

p0 : CX20 • X0 • X2 • CX12 • CCX01 ≈ CX20 • X2 • CCX01 • X0
p0 = by-assoc-and (under (CX20) (ε) B383.proved) Eq.refl Eq.refl

p1 : CX20 • X0 • X2 • CX12 • CCX01 ≈ X0 • CX20 • X2 • CX12 • CCX01
p1 = by-assoc-and (under (ε) (X2 • CX12 • CCX01) B309.proved) Eq.refl Eq.refl

p2 : CX20 • X2 • CCX01 • X0 ≈ X0 • CX20 • X2 • CX12 • CCX01
p2 = trans (sym p0) p1

p3 : CX20 • X2 • CCX01 • X0 ≈ CX20 • X2 • CCX01 • X0
p3 = refl

p4 : X0 • CX20 • X2 • CX12 • CCX01 ≈ X2 • CX20 • CX12 • CCX01
p4 = by-assoc-and (under (ε) (CX12 • CCX01) B318.proved) Eq.refl Eq.refl

p5 : X0 • CX20 • X2 • CX12 • CCX01 ≈ X2 • CX20 • CX12 • CCX01
p5 = trans p4 (refl)

p6 : CX20 • X2 • CCX01 • X0 ≈ X2 • CX20 • CX12 • CCX01
p6 = trans (sym p3) (trans p2 p5)

proved : CX20 • X2 • CCX01 • X0 ≈ X2 • CX20 • CX12 • CCX01
proved = p6
