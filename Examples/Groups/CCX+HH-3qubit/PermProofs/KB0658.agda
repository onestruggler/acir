{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0658 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0137 as B137
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0322 as B322

p0 : CCX12 • CX02 • CCX01 • CX01 ≈ CX02 • CCX01 • CCX12 • CX01
p0 = by-assoc-and (under (ε) (CX01) B322.proved) Eq.refl Eq.refl

p1 : CCX12 • CX02 • CCX01 • CX01 ≈ CCX12 • CX01 • CCX01
p1 = by-assoc-and (under (CCX12) (ε) B137.proved) Eq.refl Eq.refl

p2 : CX02 • CCX01 • CCX12 • CX01 ≈ CCX12 • CX01 • CCX01
p2 = trans (sym p0) p1

p3 : CX02 • CCX01 • CCX12 • CX01 ≈ CX02 • CCX01 • CCX12 • CX01
p3 = refl

p4 : CCX12 • CX01 • CCX01 ≈ CCX12 • CX01 • CCX01
p4 = refl

p5 : CX02 • CCX01 • CCX12 • CX01 ≈ CCX12 • CX01 • CCX01
p5 = trans (sym p3) (trans p2 p4)

proved : CX02 • CCX01 • CCX12 • CX01 ≈ CCX12 • CX01 • CCX01
proved = p5
