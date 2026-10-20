{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.comm24 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX02 ; CX12 ; X0 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0003 as B3
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0150 as B150
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0152 as B152
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0153 as B153
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0186 as B186
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0222 as B222

p0 : X0 • CCX01 • X0 • X1 • CCX01 • X1 ≈ CX12 • CCX01 • X1 • CCX01 • X1
p0 = by-assoc-and (under (ε) (X1 • CCX01 • X1) B153.proved) Eq.refl Eq.refl

p1 : CX12 • CCX01 • X1 • CCX01 • X1 ≈ CX12 • X1 • CX02 • X1
p1 = by-assoc-and (under (CX12) (X1) B186.proved) Eq.refl Eq.refl

p2 : CX12 • X1 • CX02 • X1 ≈ CX02 • CX12 • X1 • X1
p2 = by-assoc-and (under (ε) (X1) B222.proved) Eq.refl Eq.refl

p3 : CX02 • CX12 • X1 • X1 ≈ CX02 • CX12
p3 = by-assoc-and (under (CX02 • CX12) (ε) B3.proved) Eq.refl Eq.refl

p4 : X0 • CCX01 • X0 • X1 • CCX01 • X1 ≈ CX02 • CX12
p4 = trans p0 (trans p1 (trans p2 (trans p3 (refl))))

p5 : X1 • CCX01 • X1 • X0 • CCX01 • X0 ≈ CX02 • CCX01 • X0 • CCX01 • X0
p5 = by-assoc-and (under (ε) (X0 • CCX01 • X0) B150.proved) Eq.refl Eq.refl

p6 : CX02 • CCX01 • X0 • CCX01 • X0 ≈ CX02 • X0 • CX12 • X0
p6 = by-assoc-and (under (CX02) (X0) B152.proved) Eq.refl Eq.refl

p7 : CX02 • X0 • CX12 • X0 ≈ CX02 • X0 • X0 • CX12
p7 = by-assoc-and (under (CX02 • X0) (ε) B45.proved) Eq.refl Eq.refl

p8 : CX02 • X0 • X0 • CX12 ≈ CX02 • CX12
p8 = by-assoc-and (under (CX02) (CX12) B12.proved) Eq.refl Eq.refl

p9 : X1 • CCX01 • X1 • X0 • CCX01 • X0 ≈ CX02 • CX12
p9 = trans p5 (trans p6 (trans p7 (trans p8 (refl))))

proved : X0 • CCX01 • X0 • X1 • CCX01 • X1 ≈ X1 • CCX01 • X1 • X0 • CCX01 • X0
proved = trans p4 (sym p9)
