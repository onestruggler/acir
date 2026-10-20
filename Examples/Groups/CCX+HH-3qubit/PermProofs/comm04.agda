{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.comm04 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CX02 ; CX12 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0018 as B18
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0044 as B44
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0144 as B144
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0150 as B150
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0152 as B152
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0378 as B378
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0483 as B483

p0 : X0 • X1 • CCX01 • X1 • X0 • X1 • CCX01 • X1 ≈ X0 • CX02 • CCX01 • X0 • X1 • CCX01 • X1
p0 = by-assoc-and (under (X0) (X0 • X1 • CCX01 • X1) B150.proved) Eq.refl Eq.refl

p1 : X0 • CX02 • CCX01 • X0 • X1 • CCX01 • X1 ≈ X0 • X1 • CCX01 • X0 • CCX01 • X1
p1 = by-assoc-and (under (X0) (CCX01 • X1) B378.proved) Eq.refl Eq.refl

p2 : X0 • X1 • CCX01 • X0 • CCX01 • X1 ≈ X1 • CX12 • CCX01 • CCX01 • X1
p2 = by-assoc-and (under (ε) (CCX01 • X1) B483.proved) Eq.refl Eq.refl

p3 : X1 • CX12 • CCX01 • CCX01 • X1 ≈ X1 • CX12 • X1
p3 = by-assoc-and (under (X1 • CX12) (X1) B11.proved) Eq.refl Eq.refl

p4 : X1 • CX12 • X1 ≈ X2 • CX12
p4 = by-assoc-and (under (ε) (ε) B144.proved) Eq.refl Eq.refl

p5 : X0 • X1 • CCX01 • X1 • X0 • X1 • CCX01 • X1 ≈ X2 • CX12
p5 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (refl)))))

p6 : X1 • CCX01 • X1 • X0 • X1 • CCX01 • X1 • X0 ≈ CX02 • CCX01 • X0 • X1 • CCX01 • X1 • X0
p6 = by-assoc-and (under (ε) (X0 • X1 • CCX01 • X1 • X0) B150.proved) Eq.refl Eq.refl

p7 : CX02 • CCX01 • X0 • X1 • CCX01 • X1 • X0 ≈ X1 • CCX01 • X0 • CCX01 • X1 • X0
p7 = by-assoc-and (under (ε) (CCX01 • X1 • X0) B378.proved) Eq.refl Eq.refl

p8 : X1 • CCX01 • X0 • CCX01 • X1 • X0 ≈ X1 • X0 • CX12 • X1 • X0
p8 = by-assoc-and (under (X1) (X1 • X0) B152.proved) Eq.refl Eq.refl

p9 : X1 • X0 • CX12 • X1 • X0 ≈ X0 • X1 • CX12 • X1 • X0
p9 = by-assoc-and (under (ε) (CX12 • X1 • X0) B44.proved) Eq.refl Eq.refl

p10 : X0 • X1 • CX12 • X1 • X0 ≈ X0 • X2 • CX12 • X0
p10 = by-assoc-and (under (X0) (X0) B144.proved) Eq.refl Eq.refl

p11 : X0 • X2 • CX12 • X0 ≈ X0 • X2 • X0 • CX12
p11 = by-assoc-and (under (X0 • X2) (ε) B45.proved) Eq.refl Eq.refl

p12 : X0 • X2 • X0 • CX12 ≈ X0 • X0 • X2 • CX12
p12 = by-assoc-and (under (X0) (CX12) B18.proved) Eq.refl Eq.refl

p13 : X0 • X0 • X2 • CX12 ≈ X2 • CX12
p13 = by-assoc-and (under (ε) (X2 • CX12) B12.proved) Eq.refl Eq.refl

p14 : X1 • CCX01 • X1 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX12
p14 = trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (trans p12 (trans p13 (refl))))))))

proved : X0 • X1 • CCX01 • X1 • X0 • X1 • CCX01 • X1 ≈ X1 • CCX01 • X1 • X0 • X1 • CCX01 • X1 • X0
proved = trans p5 (sym p14)
