{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB1761 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0123 as B123
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0341 as B341

p0 : CCX02 • CCX12 • CX01 • CX02 • CCX01 ≈ CX01 • CCX12 • CCX02 • CX02 • CCX01
p0 = by-assoc-and (under (ε) (CX02 • CCX01) B341.proved) Eq.refl Eq.refl

p1 : CCX02 • CCX12 • CX01 • CX02 • CCX01 ≈ CCX02 • CCX12 • CCX01 • CX01
p1 = by-assoc-and (under (CCX02 • CCX12) (ε) B123.proved) Eq.refl Eq.refl

p2 : CX01 • CCX12 • CCX02 • CX02 • CCX01 ≈ CCX02 • CCX12 • CCX01 • CX01
p2 = trans (sym p0) p1

p3 : CX01 • CCX12 • CCX02 • CX02 • CCX01 ≈ CX01 • CCX12 • CCX02 • CX02 • CCX01
p3 = refl

p4 : CCX02 • CCX12 • CCX01 • CX01 ≈ CCX02 • CCX12 • CCX01 • CX01
p4 = refl

p5 : CX01 • CCX12 • CCX02 • CX02 • CCX01 ≈ CCX02 • CCX12 • CCX01 • CX01
p5 = trans (sym p3) (trans p2 p4)

proved : CX01 • CCX12 • CCX02 • CX02 • CCX01 ≈ CCX02 • CCX12 • CCX01 • CX01
proved = p5
