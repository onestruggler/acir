{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0997 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0031 as B31
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0234 as B234

p0 : CCX01 • CX12 • CX21 • X2 ≈ CCX01 • X1 • CX12 • CX21
p0 = by-assoc-and (under (CCX01) (ε) B234.proved) Eq.refl Eq.refl

p1 : CCX01 • CX12 • CX21 • X2 ≈ CX12 • CCX01 • CX21 • X2
p1 = by-assoc-and (under (ε) (CX21 • X2) B31.proved) Eq.refl Eq.refl

p2 : CCX01 • X1 • CX12 • CX21 ≈ CX12 • CCX01 • CX21 • X2
p2 = trans (sym p0) p1

p3 : CCX01 • X1 • CX12 • CX21 ≈ CCX01 • X1 • CX12 • CX21
p3 = refl

p4 : CX12 • CCX01 • CX21 • X2 ≈ CX12 • CCX01 • CX21 • X2
p4 = refl

p5 : CCX01 • X1 • CX12 • CX21 ≈ CX12 • CCX01 • CX21 • X2
p5 = trans (sym p3) (trans p2 p4)

proved : CCX01 • X1 • CX12 • CX21 ≈ CX12 • CCX01 • CX21 • X2
proved = p5
