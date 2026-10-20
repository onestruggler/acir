{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0890 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX02 ; CX12 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0027 as B27
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0044 as B44
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0128 as B128
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0183 as B183
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0222 as B222

p0 : CX12 • X1 • X2 • CX02 • X0 ≈ X1 • CX12 • CX02 • X0
p0 = by-assoc-and (under (ε) (CX02 • X0) B183.proved) Eq.refl Eq.refl

p1 : CX12 • X1 • X2 • CX02 • X0 ≈ CX12 • X1 • X0 • CX02
p1 = by-assoc-and (under (CX12 • X1) (ε) B128.proved) Eq.refl Eq.refl

p2 : X1 • CX12 • CX02 • X0 ≈ CX12 • X1 • X0 • CX02
p2 = trans (sym p0) p1

p3 : X1 • CX12 • CX02 • X0 ≈ X1 • CX02 • CX12 • X0
p3 = by-assoc-and (under (X1) (X0) B27.proved) Eq.refl Eq.refl

p4 : X1 • CX02 • CX12 • X0 ≈ X1 • CX02 • X0 • CX12
p4 = by-assoc-and (under (X1 • CX02) (ε) B45.proved) Eq.refl Eq.refl

p5 : X1 • CX12 • CX02 • X0 ≈ X1 • CX02 • X0 • CX12
p5 = trans p3 (trans p4 (refl))

p6 : CX12 • X1 • X0 • CX02 ≈ CX12 • X0 • X1 • CX02
p6 = by-assoc-and (under (CX12) (CX02) B44.proved) Eq.refl Eq.refl

p7 : CX12 • X0 • X1 • CX02 ≈ X0 • CX12 • X1 • CX02
p7 = by-assoc-and (under (ε) (X1 • CX02) B45.proved) Eq.refl Eq.refl

p8 : X0 • CX12 • X1 • CX02 ≈ X0 • CX02 • CX12 • X1
p8 = by-assoc-and (under (X0) (ε) B222.proved) Eq.refl Eq.refl

p9 : CX12 • X1 • X0 • CX02 ≈ X0 • CX02 • CX12 • X1
p9 = trans p6 (trans p7 (trans p8 (refl)))

p10 : X1 • CX02 • X0 • CX12 ≈ X0 • CX02 • CX12 • X1
p10 = trans (sym p5) (trans p2 p9)

proved : X1 • CX02 • X0 • CX12 ≈ X0 • CX02 • CX12 • X1
proved = p10
