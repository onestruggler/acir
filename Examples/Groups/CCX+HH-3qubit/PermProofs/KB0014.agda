{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.KB0014 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

p0 : CCX12 • CCX12 ≈ ε
p0 = by-assoc-and (axiom r024) Eq.refl Eq.refl

p1 : CCX12 • CCX12 ≈ CCX12 • CCX12
p1 = refl

p2 : ε ≈ ε
p2 = refl

p3 : CCX12 • CCX12 ≈ ε
p3 = trans (sym p1) (trans p0 p2)

proved : CCX12 • CCX12 ≈ ε
proved = p3
