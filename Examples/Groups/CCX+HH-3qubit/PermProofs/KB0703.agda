{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0703 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0623 as B623

p0 : CX12 • CCX02 • X0 • CCX01 • CCX01 ≈ CCX01 • CCX02 • X0 • CCX01
p0 = by-assoc-and (under (ε) (CCX01) B623.proved) Eq.refl Eq.refl

p1 : CX12 • CCX02 • X0 • CCX01 • CCX01 ≈ CX12 • CCX02 • X0
p1 = by-assoc-and (under (CX12 • CCX02 • X0) (ε) B11.proved) Eq.refl Eq.refl

p2 : CCX01 • CCX02 • X0 • CCX01 ≈ CX12 • CCX02 • X0
p2 = trans (sym p0) p1

p3 : CCX01 • CCX02 • X0 • CCX01 ≈ CCX01 • CCX02 • X0 • CCX01
p3 = refl

p4 : CX12 • CCX02 • X0 ≈ CX12 • CCX02 • X0
p4 = refl

p5 : CCX01 • CCX02 • X0 • CCX01 ≈ CX12 • CCX02 • X0
p5 = trans (sym p3) (trans p2 p4)

proved : CCX01 • CCX02 • X0 • CCX01 ≈ CX12 • CCX02 • X0
proved = p5
