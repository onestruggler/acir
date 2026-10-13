{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.comm05 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0027 as B27
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0029 as B29
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0036 as B36
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0037 as B37
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0150 as B150
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0152 as B152
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0161 as B161
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0214 as B214
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0281 as B281
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0385 as B385

p0 : X0 • X1 • CCX01 • X1 • X0 • CCX01 • CCX02 • CCX01 ≈ X0 • CX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01
p0 = by-assoc-and (under (X0) (X0 • CCX01 • CCX02 • CCX01) B150.proved) Eq.refl Eq.refl

p1 : X0 • CX02 • CCX01 • X0 • CCX01 • CCX02 • CCX01 ≈ X0 • CX02 • X0 • CX12 • CCX02 • CCX01
p1 = by-assoc-and (under (X0 • CX02) (CCX02 • CCX01) B152.proved) Eq.refl Eq.refl

p2 : X0 • CX02 • X0 • CX12 • CCX02 • CCX01 ≈ X2 • CX02 • CX12 • CCX02 • CCX01
p2 = by-assoc-and (under (ε) (CX12 • CCX02 • CCX01) B161.proved) Eq.refl Eq.refl

p3 : X0 • X1 • CCX01 • X1 • X0 • CCX01 • CCX02 • CCX01 ≈ X2 • CX02 • CX12 • CCX02 • CCX01
p3 = trans p0 (trans p1 (trans p2 (refl)))

p4 : CCX01 • CCX02 • CCX01 • X0 • X1 • CCX01 • X1 • X0 ≈ CX12 • CCX02 • CX12 • X0 • X1 • CCX01 • X1 • X0
p4 = by-assoc-and (under (ε) (X0 • X1 • CCX01 • X1 • X0) B214.proved) Eq.refl Eq.refl

p5 : CX12 • CCX02 • CX12 • X0 • X1 • CCX01 • X1 • X0 ≈ CX12 • CCX02 • X0 • CX12 • X1 • CCX01 • X1 • X0
p5 = by-assoc-and (under (CX12 • CCX02) (X1 • CCX01 • X1 • X0) B45.proved) Eq.refl Eq.refl

p6 : CX12 • CCX02 • X0 • CX12 • X1 • CCX01 • X1 • X0 ≈ CX12 • CCX02 • X0 • CX12 • CX02 • CCX01 • X0
p6 = by-assoc-and (under (CX12 • CCX02 • X0 • CX12) (X0) B150.proved) Eq.refl Eq.refl

p7 : CX12 • CCX02 • X0 • CX12 • CX02 • CCX01 • X0 ≈ CX12 • CCX02 • X0 • CX02 • CX12 • CCX01 • X0
p7 = by-assoc-and (under (CX12 • CCX02 • X0) (CCX01 • X0) B27.proved) Eq.refl Eq.refl

p8 : CX12 • CCX02 • X0 • CX02 • CX12 • CCX01 • X0 ≈ CX12 • CCX02 • CCX01 • X0 • CX02 • X0
p8 = by-assoc-and (under (CX12 • CCX02) (X0) B385.proved) Eq.refl Eq.refl

p9 : CX12 • CCX02 • CCX01 • X0 • CX02 • X0 ≈ CX12 • CCX02 • CCX01 • X2 • CX02
p9 = by-assoc-and (under (CX12 • CCX02 • CCX01) (ε) B161.proved) Eq.refl Eq.refl

p10 : CX12 • CCX02 • CCX01 • X2 • CX02 ≈ CX12 • CCX02 • X2 • CCX01 • CX02
p10 = by-assoc-and (under (CX12 • CCX02) (CX02) B29.proved) Eq.refl Eq.refl

p11 : CX12 • CCX02 • X2 • CCX01 • CX02 ≈ CX12 • CCX02 • X2 • CX02 • CCX01
p11 = by-assoc-and (under (CX12 • CCX02 • X2) (ε) B37.proved) Eq.refl Eq.refl

p12 : CX12 • CCX02 • X2 • CX02 • CCX01 ≈ CX12 • X2 • CX02 • CCX02 • CCX01
p12 = by-assoc-and (under (CX12) (CCX01) B281.proved) Eq.refl Eq.refl

p13 : CX12 • X2 • CX02 • CCX02 • CCX01 ≈ X2 • CX12 • CX02 • CCX02 • CCX01
p13 = by-assoc-and (under (ε) (CX02 • CCX02 • CCX01) B36.proved) Eq.refl Eq.refl

p14 : X2 • CX12 • CX02 • CCX02 • CCX01 ≈ X2 • CX02 • CX12 • CCX02 • CCX01
p14 = by-assoc-and (under (X2) (CCX02 • CCX01) B27.proved) Eq.refl Eq.refl

p15 : CCX01 • CCX02 • CCX01 • X0 • X1 • CCX01 • X1 • X0 ≈ X2 • CX02 • CX12 • CCX02 • CCX01
p15 = trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (trans p10 (trans p11 (trans p12 (trans p13 (trans p14 (refl)))))))))))

proved : X0 • X1 • CCX01 • X1 • X0 • CCX01 • CCX02 • CCX01 ≈ CCX01 • CCX02 • CCX01 • X0 • X1 • CCX01 • X1 • X0
proved = trans p3 (sym p15)
