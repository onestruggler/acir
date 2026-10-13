{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.braid0 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0027 as B27
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0028 as B28
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0124 as B124
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0129 as B129
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0150 as B150
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0190 as B190
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0214 as B214
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0285 as B285
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0307 as B307
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0331 as B331
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0515 as B515
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0751 as B751

p0 : X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X0 • CX02 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0
p0 = by-assoc-and (under (X0) (X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0) B150.proved) Eq.refl Eq.refl

p1 : X0 • CX02 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X0 • CX02 • CCX01 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0
p1 = by-assoc-and (under (X0 • CX02 • CCX01) (CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0) B12.proved) Eq.refl Eq.refl

p2 : X0 • CX02 • CCX01 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X0 • CX02 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0
p2 = by-assoc-and (under (X0 • CX02) (CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0) B11.proved) Eq.refl Eq.refl

p3 : X0 • CX02 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X0 • CX02 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0
p3 = by-assoc-and (under (X0 • CX02 • CCX02 • CCX01) (X1 • CCX01 • X1 • X0) B12.proved) Eq.refl Eq.refl

p4 : X0 • CX02 • CCX02 • CCX01 • X1 • CCX01 • X1 • X0 ≈ X0 • X1 • CX01 • CCX02 • CCX01 • CCX01 • X1 • X0
p4 = by-assoc-and (under (X0) (CCX01 • X1 • X0) B751.proved) Eq.refl Eq.refl

p5 : X0 • X1 • CX01 • CCX02 • CCX01 • CCX01 • X1 • X0 ≈ CX01 • X0 • CCX02 • CCX01 • CCX01 • X1 • X0
p5 = by-assoc-and (under (ε) (CCX02 • CCX01 • CCX01 • X1 • X0) B124.proved) Eq.refl Eq.refl

p6 : CX01 • X0 • CCX02 • CCX01 • CCX01 • X1 • X0 ≈ CX01 • X0 • CCX02 • X1 • X0
p6 = by-assoc-and (under (CX01 • X0 • CCX02) (X1 • X0) B11.proved) Eq.refl Eq.refl

p7 : CX01 • X0 • CCX02 • X1 • X0 ≈ CX01 • X0 • X1 • CCX02 • X0
p7 = by-assoc-and (under (CX01 • X0) (X0) B28.proved) Eq.refl Eq.refl

p8 : CX01 • X0 • X1 • CCX02 • X0 ≈ X0 • CX01 • CCX02 • X0
p8 = by-assoc-and (under (ε) (CCX02 • X0) B190.proved) Eq.refl Eq.refl

p9 : X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X0 • CX01 • CCX02 • X0
p9 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (refl)))))))))

p10 : X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX12 • CCX02 • CX12 • X0 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p10 = by-assoc-and (under (X0) (X0 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B214.proved) Eq.refl Eq.refl

p11 : X0 • CX12 • CCX02 • CX12 • X0 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX12 • CCX02 • X0 • CX12 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p11 = by-assoc-and (under (X0 • CX12 • CCX02) (X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B45.proved) Eq.refl Eq.refl

p12 : X0 • CX12 • CCX02 • X0 • CX12 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX12 • CX21 • CCX02 • CX12 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p12 = by-assoc-and (under (ε) (CX12 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B515.proved) Eq.refl Eq.refl

p13 : CX12 • CX21 • CCX02 • CX12 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX12 • CX21 • CCX02 • X0 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p13 = by-assoc-and (under (CX12 • CX21 • CCX02) (X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B45.proved) Eq.refl Eq.refl

p14 : CX12 • CX21 • CCX02 • X0 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX12 • X0 • CCX02 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p14 = by-assoc-and (under (CX12) (CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B129.proved) Eq.refl Eq.refl

p15 : CX12 • X0 • CCX02 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX12 • CCX02 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p15 = by-assoc-and (under (ε) (CCX02 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B45.proved) Eq.refl Eq.refl

p16 : X0 • CX12 • CCX02 • CX12 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX12 • CCX02 • CX12 • CX02 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p16 = by-assoc-and (under (X0 • CX12 • CCX02 • CX12) (X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B150.proved) Eq.refl Eq.refl

p17 : X0 • CX12 • CCX02 • CX12 • CX02 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX12 • CCX02 • CX02 • CX12 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p17 = by-assoc-and (under (X0 • CX12 • CCX02) (CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B27.proved) Eq.refl Eq.refl

p18 : X0 • CX12 • CCX02 • CX02 • CX12 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX01 • CX12 • CCX02 • CX12 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p18 = by-assoc-and (under (X0) (CX12 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B285.proved) Eq.refl Eq.refl

p19 : X0 • CX01 • CX12 • CCX02 • CX12 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX01 • CCX01 • CCX02 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p19 = by-assoc-and (under (X0 • CX01) (X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B307.proved) Eq.refl Eq.refl

p20 : X0 • CX01 • CCX01 • CCX02 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX01 • CCX01 • CCX02 • CCX01 • CCX02 • CCX01 • X0
p20 = by-assoc-and (under (X0 • CX01 • CCX01 • CCX02) (CCX01 • CCX02 • CCX01 • X0) B12.proved) Eq.refl Eq.refl

p21 : X0 • CX01 • CCX01 • CCX02 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX01 • CX12 • CCX02 • CX12 • CCX02 • CCX01 • X0
p21 = by-assoc-and (under (X0 • CX01) (CCX02 • CCX01 • X0) B214.proved) Eq.refl Eq.refl

p22 : X0 • CX01 • CX12 • CCX02 • CX12 • CCX02 • CCX01 • X0 ≈ X0 • CX01 • CCX02 • CCX01 • CCX01 • X0
p22 = by-assoc-and (under (X0 • CX01) (CCX01 • X0) B331.proved) Eq.refl Eq.refl

p23 : X0 • CX01 • CCX02 • CCX01 • CCX01 • X0 ≈ X0 • CX01 • CCX02 • X0
p23 = by-assoc-and (under (X0 • CX01 • CCX02) (X0) B11.proved) Eq.refl Eq.refl

p24 : X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX01 • CCX02 • X0
p24 = trans p10 (trans p11 (trans p12 (trans p13 (trans p14 (trans p15 (trans p16 (trans p17 (trans p18 (trans p19 (trans p20 (trans p21 (trans p22 (trans p23 (refl))))))))))))))

proved : X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 ≈ X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • X1 • CCX01 • X1 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
proved = trans p9 (sym p24)
