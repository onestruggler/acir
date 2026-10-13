{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Proofs.X0X1 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Proofs.KB0242 as B242

p0 : X0 • X1 ≈ X0 • X1
p0 = refl

p1 : X1 • X0 ≈ X0 • X1
p1 = by-assoc-and (under (ε) (ε) B242.proved) Eq.refl Eq.refl

p2 : X1 • X0 ≈ X0 • X1
p2 = trans p1 (refl)

proved : X0 • X1 ≈ X1 • X0
proved = trans p0 (sym p2)
