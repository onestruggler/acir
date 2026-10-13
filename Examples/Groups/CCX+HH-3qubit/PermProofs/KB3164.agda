{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB3164 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0123 as B123
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0215 as B215
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0219 as B219
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0322 as B322

p0 : CCX12 • CCX02 • CCX12 • CX02 • CCX01 ≈ CCX12 • CCX02 • CX02 • CCX01 • CCX12
p0 = by-assoc-and (under (CCX12 • CCX02) (ε) B322.proved) Eq.refl Eq.refl

p1 : CCX12 • CCX02 • CCX12 • CX02 • CCX01 ≈ CX10 • CCX02 • CX10 • CX02 • CCX01
p1 = by-assoc-and (under (ε) (CX02 • CCX01) B215.proved) Eq.refl Eq.refl

p2 : CCX12 • CCX02 • CX02 • CCX01 • CCX12 ≈ CX10 • CCX02 • CX10 • CX02 • CCX01
p2 = trans (sym p0) p1

p3 : CCX12 • CCX02 • CX02 • CCX01 • CCX12 ≈ CCX12 • CCX02 • CX02 • CCX01 • CCX12
p3 = refl

p4 : CX10 • CCX02 • CX10 • CX02 • CCX01 ≈ CX01 • CCX12 • CX01 • CX02 • CCX01
p4 = by-assoc-and (under (ε) (CX02 • CCX01) B219.proved) Eq.refl Eq.refl

p5 : CX01 • CCX12 • CX01 • CX02 • CCX01 ≈ CX01 • CCX12 • CCX01 • CX01
p5 = by-assoc-and (under (CX01 • CCX12) (ε) B123.proved) Eq.refl Eq.refl

p6 : CX10 • CCX02 • CX10 • CX02 • CCX01 ≈ CX01 • CCX12 • CCX01 • CX01
p6 = trans p4 (trans p5 (refl))

p7 : CCX12 • CCX02 • CX02 • CCX01 • CCX12 ≈ CX01 • CCX12 • CCX01 • CX01
p7 = trans (sym p3) (trans p2 p6)

proved : CCX12 • CCX02 • CX02 • CCX01 • CCX12 ≈ CX01 • CCX12 • CCX01 • CX01
proved = p7
