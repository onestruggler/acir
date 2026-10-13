{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.cflip3 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CCX1 as elim_CCX1

step0 : CCX02 • CCX01 • CCX02 ≈ CCX02 • CCX02 • CCX01 • CCX02 • CCX01
step0 = by-assoc-and (under (CCX02) (ε) (axiom r046)) Eq.refl Eq.refl

step1 : CCX02 • CCX02 • CCX01 • CCX02 • CCX01 ≈ CCX01 • CCX02 • CCX01
step1 = by-assoc-and (under (ε) (CCX01 • CCX02 • CCX01) (elim_CCX1.proved)) Eq.refl Eq.refl

proved : CCX02 • CCX01 • CCX02 ≈ CCX01 • CCX02 • CCX01
proved = trans step0 (trans step1 (refl))
