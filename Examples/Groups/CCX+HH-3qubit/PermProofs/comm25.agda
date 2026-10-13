{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.comm25 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0121 as B121
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0153 as B153
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0214 as B214

p0 : X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 ≈ CX12 • CCX01 • CCX01 • CCX02 • CCX01
p0 = by-assoc-and (under (ε) (CCX01 • CCX02 • CCX01) B153.proved) Eq.refl Eq.refl

p1 : CX12 • CCX01 • CCX01 • CCX02 • CCX01 ≈ CX12 • CCX02 • CCX01
p1 = by-assoc-and (under (CX12) (CCX02 • CCX01) B11.proved) Eq.refl Eq.refl

p2 : X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 ≈ CX12 • CCX02 • CCX01
p2 = trans p0 (trans p1 (refl))

p3 : CCX01 • CCX02 • CCX01 • X0 • CCX01 • X0 ≈ CX12 • CCX02 • CX12 • X0 • CCX01 • X0
p3 = by-assoc-and (under (ε) (X0 • CCX01 • X0) B214.proved) Eq.refl Eq.refl

p4 : CX12 • CCX02 • CX12 • X0 • CCX01 • X0 ≈ CX12 • CCX02 • X0 • CX12 • CCX01 • X0
p4 = by-assoc-and (under (CX12 • CCX02) (CCX01 • X0) B45.proved) Eq.refl Eq.refl

p5 : CX12 • CCX02 • X0 • CX12 • CCX01 • X0 ≈ CX12 • CCX02 • CCX01 • X0 • X0
p5 = by-assoc-and (under (CX12 • CCX02) (X0) B121.proved) Eq.refl Eq.refl

p6 : CX12 • CCX02 • CCX01 • X0 • X0 ≈ CX12 • CCX02 • CCX01
p6 = by-assoc-and (under (CX12 • CCX02 • CCX01) (ε) B12.proved) Eq.refl Eq.refl

p7 : CCX01 • CCX02 • CCX01 • X0 • CCX01 • X0 ≈ CX12 • CCX02 • CCX01
p7 = trans p3 (trans p4 (trans p5 (trans p6 (refl))))

proved : X0 • CCX01 • X0 • CCX01 • CCX02 • CCX01 ≈ CCX01 • CCX02 • CCX01 • X0 • CCX01 • X0
proved = trans p2 (sym p7)
