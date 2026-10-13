{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Proofs.KB0000 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

p0 : X0 • X0 ≈ ε
p0 = by-assoc-and (axiom r021) Eq.refl Eq.refl

p1 : X0 • X0 ≈ X0 • X0
p1 = refl

p2 : ε ≈ ε
p2 = refl

p3 : X0 • X0 ≈ ε
p3 = trans (sym p1) (trans p0 p2)

proved : X0 • X0 ≈ ε
proved = p3
