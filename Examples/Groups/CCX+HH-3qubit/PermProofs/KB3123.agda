{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB3123 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0234 as B234
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0293 as B293
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0997 as B997
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB1173 as B1173

p0 : CCX01 • CCX12 • CX12 • CX21 • X2 ≈ CX10 • CCX01 • CCX12 • CX21 • X2
p0 = by-assoc-and (under (ε) (CX21 • X2) B293.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX12 • CX12 • CX21 • X2 ≈ CCX01 • CCX12 • X1 • CX12 • CX21
p1 = by-assoc-and (under (CCX01 • CCX12) (ε) B234.proved) Eq.refl Eq.refl

p2 : CX10 • CCX01 • CCX12 • CX21 • X2 ≈ CCX01 • CCX12 • X1 • CX12 • CX21
p2 = trans (sym p0) p1

p3 : CX10 • CCX01 • CCX12 • CX21 • X2 ≈ CX10 • CCX01 • CCX12 • CX21 • X2
p3 = refl

p4 : CCX01 • CCX12 • X1 • CX12 • CX21 ≈ CCX01 • X1 • CX12 • CX21 • CCX12
p4 = by-assoc-and (under (CCX01) (ε) B1173.proved) Eq.refl Eq.refl

p5 : CCX01 • X1 • CX12 • CX21 • CCX12 ≈ CX12 • CCX01 • CX21 • X2 • CCX12
p5 = by-assoc-and (under (ε) (CCX12) B997.proved) Eq.refl Eq.refl

p6 : CCX01 • CCX12 • X1 • CX12 • CX21 ≈ CX12 • CCX01 • CX21 • X2 • CCX12
p6 = trans p4 (trans p5 (refl))

p7 : CX10 • CCX01 • CCX12 • CX21 • X2 ≈ CX12 • CCX01 • CX21 • X2 • CCX12
p7 = trans (sym p3) (trans p2 p6)

p8 : CX12 • CCX01 • CX21 • X2 • CCX12 ≈ CX10 • CCX01 • CCX12 • CX21 • X2
p8 = sym p7

proved : CX12 • CCX01 • CX21 • X2 • CCX12 ≈ CX10 • CCX01 • CCX12 • CX21 • X2
proved = p8
