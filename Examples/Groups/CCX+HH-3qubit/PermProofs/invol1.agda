{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.invol1 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0010 as B10
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0129 as B129
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0214 as B214
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0307 as B307
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0515 as B515

p0 : X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX12 • CCX02 • CX12 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0
p0 = by-assoc-and (under (X0) (X0 • X0 • CCX01 • CCX02 • CCX01 • X0) B214.proved) Eq.refl Eq.refl

p1 : X0 • CX12 • CCX02 • CX12 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX12 • CCX02 • X0 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0
p1 = by-assoc-and (under (X0 • CX12 • CCX02) (X0 • CCX01 • CCX02 • CCX01 • X0) B45.proved) Eq.refl Eq.refl

p2 : X0 • CX12 • CCX02 • X0 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX12 • CX21 • CCX02 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0
p2 = by-assoc-and (under (ε) (CX12 • X0 • CCX01 • CCX02 • CCX01 • X0) B515.proved) Eq.refl Eq.refl

p3 : CX12 • CX21 • CCX02 • CX12 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ CX12 • CX21 • CCX02 • X0 • CX12 • CCX01 • CCX02 • CCX01 • X0
p3 = by-assoc-and (under (CX12 • CX21 • CCX02) (CCX01 • CCX02 • CCX01 • X0) B45.proved) Eq.refl Eq.refl

p4 : CX12 • CX21 • CCX02 • X0 • CX12 • CCX01 • CCX02 • CCX01 • X0 ≈ CX12 • X0 • CCX02 • CX12 • CCX01 • CCX02 • CCX01 • X0
p4 = by-assoc-and (under (CX12) (CX12 • CCX01 • CCX02 • CCX01 • X0) B129.proved) Eq.refl Eq.refl

p5 : CX12 • X0 • CCX02 • CX12 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CX12 • CCX02 • CX12 • CCX01 • CCX02 • CCX01 • X0
p5 = by-assoc-and (under (ε) (CCX02 • CX12 • CCX01 • CCX02 • CCX01 • X0) B45.proved) Eq.refl Eq.refl

p6 : X0 • CX12 • CCX02 • CX12 • CCX01 • CCX02 • CCX01 • X0 ≈ X0 • CCX01 • CCX02 • CCX02 • CCX01 • X0
p6 = by-assoc-and (under (X0) (CCX02 • CCX01 • X0) B307.proved) Eq.refl Eq.refl

p7 : X0 • CCX01 • CCX02 • CCX02 • CCX01 • X0 ≈ X0 • CCX01 • CCX01 • X0
p7 = by-assoc-and (under (X0 • CCX01) (CCX01 • X0) B10.proved) Eq.refl Eq.refl

p8 : X0 • CCX01 • CCX01 • X0 ≈ X0 • X0
p8 = by-assoc-and (under (X0) (X0) B11.proved) Eq.refl Eq.refl

p9 : X0 • X0 ≈ ε
p9 = by-assoc-and (under (ε) (ε) B12.proved) Eq.refl Eq.refl

p10 : X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ ε
p10 = trans p0 (trans p1 (trans p2 (trans p3 (trans p4 (trans p5 (trans p6 (trans p7 (trans p8 (trans p9 (refl))))))))))

p11 : ε ≈ ε
p11 = refl

proved : X0 • CCX01 • CCX02 • CCX01 • X0 • X0 • CCX01 • CCX02 • CCX01 • X0 ≈ ε
proved = trans p10 (sym p11)
