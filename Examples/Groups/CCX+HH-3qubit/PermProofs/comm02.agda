{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.comm02 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX02 ; CX12 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0003 as B3
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0023 as B23
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0140 as B140
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0150 as B150
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0153 as B153
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0161 as B161
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0186 as B186

p0 : X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 ≈ X0 • CX02 • CCX01 • X0 • X0 • CCX01 • X0
p0 = by-assoc-and (under (X0) (X0 • X0 • CCX01 • X0) B150.proved) Eq.refl Eq.refl

p1 : X0 • CX02 • CCX01 • X0 • X0 • CCX01 • X0 ≈ X0 • CX02 • CCX01 • CCX01 • X0
p1 = by-assoc-and (under (X0 • CX02 • CCX01) (CCX01 • X0) B12.proved) Eq.refl Eq.refl

p2 : X0 • CX02 • CCX01 • CCX01 • X0 ≈ X0 • CX02 • X0
p2 = by-assoc-and (under (X0 • CX02) (X0) B11.proved) Eq.refl Eq.refl

p3 : X0 • CX02 • X0 ≈ X2 • CX02
p3 = by-assoc-and (under (ε) (ε) B161.proved) Eq.refl Eq.refl

p4 : X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 ≈ X2 • CX02
p4 = trans p0 (trans p1 (trans p2 (trans p3 (refl))))

p5 : X0 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ CX12 • CCX01 • X0 • X1 • CCX01 • X1 • X0
p5 = by-assoc-and (under (ε) (X0 • X1 • CCX01 • X1 • X0) B153.proved) Eq.refl Eq.refl

p6 : CX12 • CCX01 • X0 • X1 • CCX01 • X1 • X0 ≈ X0 • CCX01 • X1 • CCX01 • X1 • X0
p6 = by-assoc-and (under (ε) (X1 • CCX01 • X1 • X0) B140.proved) Eq.refl Eq.refl

p7 : X0 • CCX01 • X1 • CCX01 • X1 • X0 ≈ X0 • X1 • CX02 • X1 • X0
p7 = by-assoc-and (under (X0) (X1 • X0) B186.proved) Eq.refl Eq.refl

p8 : X0 • X1 • CX02 • X1 • X0 ≈ X0 • X1 • X1 • CX02 • X0
p8 = by-assoc-and (under (X0 • X1) (X0) B23.proved) Eq.refl Eq.refl

p9 : X0 • X1 • X1 • CX02 • X0 ≈ X0 • CX02 • X0
p9 = by-assoc-and (under (X0) (CX02 • X0) B3.proved) Eq.refl Eq.refl

p10 : X0 • CX02 • X0 ≈ X2 • CX02
p10 = by-assoc-and (under (ε) (ε) B161.proved) Eq.refl Eq.refl

p11 : X0 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX02
p11 = trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (refl))))))

proved : X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • X0 ≈ X0 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0
proved = trans p4 (sym p11)
