{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.invol2 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0012 as B12
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0140 as B140
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0153 as B153

p0 : X0 • CCX01 • X0 • X0 • CCX01 • X0 ≈ CX12 • CCX01 • X0 • CCX01 • X0
p0 = by-assoc-and (under (ε) (X0 • CCX01 • X0) B153.proved) Eq.refl Eq.refl

p1 : CX12 • CCX01 • X0 • CCX01 • X0 ≈ X0 • CCX01 • CCX01 • X0
p1 = by-assoc-and (under (ε) (CCX01 • X0) B140.proved) Eq.refl Eq.refl

p2 : X0 • CCX01 • CCX01 • X0 ≈ X0 • X0
p2 = by-assoc-and (under (X0) (X0) B11.proved) Eq.refl Eq.refl

p3 : X0 • X0 ≈ ε
p3 = by-assoc-and (under (ε) (ε) B12.proved) Eq.refl Eq.refl

p4 : X0 • CCX01 • X0 • X0 • CCX01 • X0 ≈ ε
p4 = trans p0 (trans p1 (trans p2 (trans p3 (refl))))

p5 : ε ≈ ε
p5 = refl

proved : X0 • CCX01 • X0 • X0 • CCX01 • X0 ≈ ε
proved = trans p4 (sym p5)
