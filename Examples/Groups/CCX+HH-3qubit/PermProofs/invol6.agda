{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.invol6 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11

p0 : CCX01 • CCX01 ≈ ε
p0 = by-assoc-and (under (ε) (ε) B11.proved) Eq.refl Eq.refl

p1 : CCX01 • CCX01 ≈ ε
p1 = trans p0 (refl)

p2 : ε ≈ ε
p2 = refl

proved : CCX01 • CCX01 ≈ ε
proved = trans p1 (sym p2)
