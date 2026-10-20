{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.braid4 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CX01 ; CX02 ; CX12 ; X1 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0003 as B3
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0027 as B27
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0028 as B28
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0035 as B35
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0150 as B150
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0214 as B214
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0285 as B285
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0307 as B307
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0331 as B331
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0751 as B751

p0 : X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 ≈ CX02 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1
p0 = by-assoc-and (under (ε) (CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1) B150.proved) Eq.refl Eq.refl

p1 : CX02 • CCX01 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 ≈ CX02 • CCX02 • CCX01 • X1 • CCX01 • X1
p1 = by-assoc-and (under (CX02) (CCX02 • CCX01 • X1 • CCX01 • X1) B11.proved) Eq.refl Eq.refl

p2 : CX02 • CCX02 • CCX01 • X1 • CCX01 • X1 ≈ X1 • CX01 • CCX02 • CCX01 • CCX01 • X1
p2 = by-assoc-and (under (ε) (CCX01 • X1) B751.proved) Eq.refl Eq.refl

p3 : X1 • CX01 • CCX02 • CCX01 • CCX01 • X1 ≈ X1 • CX01 • CCX02 • X1
p3 = by-assoc-and (under (X1 • CX01 • CCX02) (X1) B11.proved) Eq.refl Eq.refl

p4 : X1 • CX01 • CCX02 • X1 ≈ X1 • CX01 • X1 • CCX02
p4 = by-assoc-and (under (X1 • CX01) (ε) B28.proved) Eq.refl Eq.refl

p5 : X1 • CX01 • X1 • CCX02 ≈ X1 • X1 • CX01 • CCX02
p5 = by-assoc-and (under (X1) (CCX02) B35.proved) Eq.refl Eq.refl

p6 : X1 • X1 • CX01 • CCX02 ≈ CX01 • CCX02
p6 = by-assoc-and (under (ε) (CX01 • CCX02) B3.proved) Eq.refl Eq.refl

p7 : X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 ≈ CX01 • CCX02
p7 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (refl)))))))

p8 : CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 ≈ CX12 • CCX02 • CX12 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01
p8 = by-assoc-and (under (ε) (X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01) B214.proved) Eq.refl Eq.refl

p9 : CX12 • CCX02 • CX12 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 ≈ CX12 • CCX02 • CX12 • CX02 • CCX01 • CCX01 • CCX02 • CCX01
p9 = by-assoc-and (under (CX12 • CCX02 • CX12) (CCX01 • CCX02 • CCX01) B150.proved) Eq.refl Eq.refl

p10 : CX12 • CCX02 • CX12 • CX02 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX12 • CCX02 • CX02 • CX12 • CCX01 • CCX01 • CCX02 • CCX01
p10 = by-assoc-and (under (CX12 • CCX02) (CCX01 • CCX01 • CCX02 • CCX01) B27.proved) Eq.refl Eq.refl

p11 : CX12 • CCX02 • CX02 • CX12 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX01 • CX12 • CCX02 • CX12 • CCX01 • CCX01 • CCX02 • CCX01
p11 = by-assoc-and (under (ε) (CX12 • CCX01 • CCX01 • CCX02 • CCX01) B285.proved) Eq.refl Eq.refl

p12 : CX01 • CX12 • CCX02 • CX12 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX01 • CCX02 • CCX01 • CCX02 • CCX01
p12 = by-assoc-and (under (CX01) (CCX01 • CCX02 • CCX01) B307.proved) Eq.refl Eq.refl

p13 : CX01 • CCX01 • CCX02 • CCX01 • CCX02 • CCX01 ≈ CX01 • CX12 • CCX02 • CX12 • CCX02 • CCX01
p13 = by-assoc-and (under (CX01) (CCX02 • CCX01) B214.proved) Eq.refl Eq.refl

p14 : CX01 • CX12 • CCX02 • CX12 • CCX02 • CCX01 ≈ CX01 • CCX02 • CCX01 • CCX01
p14 = by-assoc-and (under (CX01) (CCX01) B331.proved) Eq.refl Eq.refl

p15 : CX01 • CCX02 • CCX01 • CCX01 ≈ CX01 • CCX02
p15 = by-assoc-and (under (CX01 • CCX02) (ε) B11.proved) Eq.refl Eq.refl

p16 : CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 ≈ CX01 • CCX02
p16 = trans p8 (trans p9 (trans p10 (trans p11 (trans p12 (trans p13 (trans p14 (trans p15 (refl))))))))

proved : X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 ≈ CCX01 • CCX02 • CCX01 • X1 • CCX01 • X1 • CCX01 • CCX02 • CCX01
proved = trans p7 (sym p16)
