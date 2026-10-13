{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.decodeCCX02 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.PermProofs.KB0011 as B11

p0 : CCX02 ≈ CCX02
p0 = refl

p1 : CCX01 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CCX02 • CCX01 • CCX01
p1 = by-assoc-and (under (ε) (CCX02 • CCX01 • CCX01) B11.proved) Eq.refl Eq.refl

p2 : CCX02 • CCX01 • CCX01 ≈ CCX02
p2 = by-assoc-and (under (CCX02) (ε) B11.proved) Eq.refl Eq.refl

p3 : CCX01 • CCX01 • CCX02 • CCX01 • CCX01 ≈ CCX02
p3 = trans p1 (trans p2 (refl))

proved : CCX02 ≈ CCX01 • CCX01 • CCX02 • CCX01 • CCX01
proved = trans p0 (sym p3)
