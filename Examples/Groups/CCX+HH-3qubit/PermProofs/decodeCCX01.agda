{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.PermProofs.decodeCCX01 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine

p0 : CCX01 ≈ CCX01
p0 = refl

p1 : CCX01 ≈ CCX01
p1 = refl

proved : CCX01 ≈ CCX01
proved = trans p0 (sym p1)
