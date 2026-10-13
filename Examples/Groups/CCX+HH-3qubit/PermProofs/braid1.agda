{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.braid1 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0129 as B129
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0140 as B140
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0153 as B153
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0166 as B166
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0214 as B214
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0307 as B307
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0331 as B331
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0515 as B515

p0 : X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX12 • CCX02 • CX12 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p0 = by-assoc-and (under (X0) (X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B214.proved) Eq.refl Eq.refl

p1 : X0 • CX12 • CCX02 • CX12 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX12 • CCX02 • X0 • CX12 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p1 = by-assoc-and (under (X0 • CX12 • CCX02) (X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B45.proved) Eq.refl Eq.refl

p2 : X0 • CX12 • CCX02 • X0 • CX12 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX12 • CX21 • CCX02 • CX12 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p2 = by-assoc-and (under (ε) (CX12 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B515.proved) Eq.refl Eq.refl

p3 : CX12 • CX21 • CCX02 • CX12 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX12 • CX21 • CCX02 • X0 • CX12 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p3 = by-assoc-and (under (CX12 • CX21 • CCX02) (CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B45.proved) Eq.refl Eq.refl

p4 : CX12 • CX21 • CCX02 • X0 • CX12 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX12 • X0 • CCX02 • CX12 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p4 = by-assoc-and (under (CX12) (CX12 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B129.proved) Eq.refl Eq.refl

p5 : CX12 • X0 • CCX02 • CX12 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX12 • CCX02 • CX12 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p5 = by-assoc-and (under (ε) (CCX02 • CX12 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B45.proved) Eq.refl Eq.refl

p6 : X0 • CX12 • CCX02 • CX12 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CCX01 • CCX02 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p6 = by-assoc-and (under (X0) (X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B307.proved) Eq.refl Eq.refl

p7 : X0 • CCX01 • CCX02 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CCX01 • CCX02 • CCX01 • CCX02 • CCX01 • X0
p7 = by-assoc-and (under (X0 • CCX01 • CCX02) (CCX01 • CCX02 • CCX01 • X0) B12.proved) Eq.refl Eq.refl

p8 : X0 • CCX01 • CCX02 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX12 • CCX02 • CX12 • CCX02 • CCX01 • X0
p8 = by-assoc-and (under (X0) (CCX02 • CCX01 • X0) B214.proved) Eq.refl Eq.refl

p9 : X0 • CX12 • CCX02 • CX12 • CCX02 • CCX01 • X0 ≈ X0 • CCX02 • CCX01 • CCX01 • X0
p9 = by-assoc-and (under (X0) (CCX01 • X0) B331.proved) Eq.refl Eq.refl

p10 : X0 • CCX02 • CCX01 • CCX01 • X0 ≈ X0 • CCX02 • X0
p10 = by-assoc-and (under (X0 • CCX02) (X0) B11.proved) Eq.refl Eq.refl

p11 : X0 • CCX02 • X0 ≈ CX21 • CCX02
p11 = by-assoc-and (under (ε) (ε) B166.proved) Eq.refl Eq.refl

p12 : X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX21 • CCX02
p12 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (refl))))))))))))

p13 : X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 ≈ CX12 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0
p13 = by-assoc-and (under (ε) (X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0) B153.proved) Eq.refl Eq.refl

p14 : CX12 • CCX01 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 ≈ X0 • CCX01 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0
p14 = by-assoc-and (under (ε) (CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0) B140.proved) Eq.refl Eq.refl

p15 : X0 • CCX01 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 ≈ X0 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0
p15 = by-assoc-and (under (X0) (CCX02 • CCX01 • X0 • X0 • CCX01 • X0) B11.proved) Eq.refl Eq.refl

p16 : X0 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 ≈ X0 • CCX02 • CCX01 • CCX01 • X0
p16 = by-assoc-and (under (X0 • CCX02 • CCX01) (CCX01 • X0) B12.proved) Eq.refl Eq.refl

p17 : X0 • CCX02 • CCX01 • CCX01 • X0 ≈ X0 • CCX02 • X0
p17 = by-assoc-and (under (X0 • CCX02) (X0) B11.proved) Eq.refl Eq.refl

p18 : X0 • CCX02 • X0 ≈ CX21 • CCX02
p18 = by-assoc-and (under (ε) (ε) B166.proved) Eq.refl Eq.refl

p19 : X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 ≈ CX21 • CCX02
p19 = trans p13 (trans p14 (trans p15 (trans p16 (trans p17 (trans p18 (refl))))))

proved : X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • X0
proved = trans p12 (sym p19)
