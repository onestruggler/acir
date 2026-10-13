{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB3094 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0026 as B26
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 as B45
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0214 as B214
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0280 as B280

p0 : CCX01 • CCX02 • CCX01 • X0 • CX10 ≈ CCX01 • CCX02 • X0 • CX10 • CCX01
p0 = by-assoc-and (under (CCX01 • CCX02) (ε) B280.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX02 • CCX01 • X0 • CX10 ≈ CX12 • CCX02 • CX12 • X0 • CX10
p1 = by-assoc-and (under (ε) (X0 • CX10) B214.proved) Eq.refl Eq.refl

p2 : CCX01 • CCX02 • X0 • CX10 • CCX01 ≈ CX12 • CCX02 • CX12 • X0 • CX10
p2 = trans (sym p0) p1

p3 : CCX01 • CCX02 • X0 • CX10 • CCX01 ≈ CCX01 • CCX02 • X0 • CX10 • CCX01
p3 = refl

p4 : CX12 • CCX02 • CX12 • X0 • CX10 ≈ CX12 • CCX02 • X0 • CX12 • CX10
p4 = by-assoc-and (under (CX12 • CCX02) (CX10) B45.proved) Eq.refl Eq.refl

p5 : CX12 • CCX02 • X0 • CX12 • CX10 ≈ CX12 • CCX02 • X0 • CX10 • CX12
p5 = by-assoc-and (under (CX12 • CCX02 • X0) (ε) B26.proved) Eq.refl Eq.refl

p6 : CX12 • CCX02 • CX12 • X0 • CX10 ≈ CX12 • CCX02 • X0 • CX10 • CX12
p6 = trans p4 (trans p5 (refl))

p7 : CCX01 • CCX02 • X0 • CX10 • CCX01 ≈ CX12 • CCX02 • X0 • CX10 • CX12
p7 = trans (sym p3) (trans p2 p6)

proved : CCX01 • CCX02 • X0 • CX10 • CCX01 ≈ CX12 • CCX02 • X0 • CX10 • CX12
proved = p7
