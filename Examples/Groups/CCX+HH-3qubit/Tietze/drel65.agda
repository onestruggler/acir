{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel65 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel137 as drel137
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_X1 as elim_X1
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_Z1 as elim_Z1

step0 : K12 • X1 ≈ K12 • X1 • K12 • K12
step0 = by-assoc-and (under (K12 • X1) (ε) (sym (axiom r023))) Eq.refl Eq.refl

step1 : K12 • X1 • K12 • K12 ≈ K12 • X1 • K12 • Z1 • Z1 • K12
step1 = by-assoc-and (under (K12 • X1 • K12) (K12) (sym (elim_Z1.proved))) Eq.refl Eq.refl

step2 : K12 • X1 • K12 • Z1 • Z1 • K12 ≈ K12 • X1 • X1 • K12 • Z1 • K12
step2 = by-assoc-and (under (K12 • X1) (Z1 • K12) (sym (drel137.proved))) Eq.refl Eq.refl

step3 : K12 • X1 • X1 • K12 • Z1 • K12 ≈ K12 • K12 • Z1 • K12
step3 = by-assoc-and (under (K12) (K12 • Z1 • K12) (elim_X1.proved)) Eq.refl Eq.refl

step4 : K12 • K12 • Z1 • K12 ≈ Z1 • K12
step4 = by-assoc-and (under (ε) (Z1 • K12) (axiom r023)) Eq.refl Eq.refl

proved : K12 • X1 ≈ Z1 • K12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
