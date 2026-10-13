{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel29 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel128 as drel128
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CCX1 as elim_CCX1
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CCX2 as elim_CCX2

step0 : CCX01 • K12 ≈ CCX01 • K12 • CCX02 • CCX02
step0 = by-assoc-and (under (CCX01 • K12) (ε) (sym (elim_CCX1.proved))) Eq.refl Eq.refl

step1 : CCX01 • K12 • CCX02 • CCX02 ≈ CCX01 • K12 • CCX02 • K12 • K12 • CCX02
step1 = by-assoc-and (under (CCX01 • K12 • CCX02) (CCX02) (sym (axiom r023))) Eq.refl Eq.refl

step2 : CCX01 • K12 • CCX02 • K12 • K12 • CCX02 ≈ CCX01 • K12 • K12 • CCX01 • K12 • CCX02
step2 = by-assoc-and (under (CCX01 • K12) (K12 • CCX02) (sym (drel128.proved))) Eq.refl Eq.refl

step3 : CCX01 • K12 • K12 • CCX01 • K12 • CCX02 ≈ CCX01 • CCX01 • K12 • CCX02
step3 = by-assoc-and (under (CCX01) (CCX01 • K12 • CCX02) (axiom r023)) Eq.refl Eq.refl

step4 : CCX01 • CCX01 • K12 • CCX02 ≈ K12 • CCX02
step4 = by-assoc-and (under (ε) (K12 • CCX02) (elim_CCX2.proved)) Eq.refl Eq.refl

proved : CCX01 • K12 ≈ K12 • CCX02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
