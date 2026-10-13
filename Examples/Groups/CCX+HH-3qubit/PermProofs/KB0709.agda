{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0709 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0008 as B8
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0658 as B658

p0 : CX02 • CX02 • CCX01 • CCX12 • CX01 ≈ CX02 • CCX12 • CX01 • CCX01
p0 = by-assoc-and (under (CX02) (ε) B658.proved) Eq.refl Eq.refl

p1 : CX02 • CX02 • CCX01 • CCX12 • CX01 ≈ CCX01 • CCX12 • CX01
p1 = by-assoc-and (under (ε) (CCX01 • CCX12 • CX01) B8.proved) Eq.refl Eq.refl

p2 : CX02 • CCX12 • CX01 • CCX01 ≈ CCX01 • CCX12 • CX01
p2 = trans (sym p0) p1

p3 : CX02 • CCX12 • CX01 • CCX01 ≈ CX02 • CCX12 • CX01 • CCX01
p3 = refl

p4 : CCX01 • CCX12 • CX01 ≈ CCX01 • CCX12 • CX01
p4 = refl

p5 : CX02 • CCX12 • CX01 • CCX01 ≈ CCX01 • CCX12 • CX01
p5 = trans (sym p3) (trans p2 p4)

proved : CX02 • CCX12 • CX01 • CCX01 ≈ CCX01 • CCX12 • CX01
proved = p5
