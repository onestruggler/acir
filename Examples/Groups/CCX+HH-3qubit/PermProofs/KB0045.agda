{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0045 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

p0 : CX12 • X0 ≈ X0 • CX12
p0 = by-assoc-and (axiom r026) Eq.refl Eq.refl

p1 : CX12 • X0 ≈ CX12 • X0
p1 = refl

p2 : X0 • CX12 ≈ X0 • CX12
p2 = refl

p3 : CX12 • X0 ≈ X0 • CX12
p3 = trans (sym p1) (trans p0 p2)

proved : CX12 • X0 ≈ X0 • CX12
proved = p3
