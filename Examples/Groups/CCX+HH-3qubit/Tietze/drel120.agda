{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel120 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel146 as drel146
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ02 as elim_CZ02
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_X2 as elim_X2
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_Z0 as elim_Z0

step0 : X2 • Z0 • CZ02 ≈ X2 • Z0 • CZ02 • X2 • X2
step0 = by-assoc-and (under (X2 • Z0 • CZ02) (ε) (sym (elim_X2.proved))) Eq.refl Eq.refl

step1 : X2 • Z0 • CZ02 • X2 • X2 ≈ X2 • Z0 • CZ02 • X2 • CZ02 • CZ02 • X2
step1 = by-assoc-and (under (X2 • Z0 • CZ02 • X2) (X2) (sym (elim_CZ02.proved))) Eq.refl Eq.refl

step2 : X2 • Z0 • CZ02 • X2 • CZ02 • CZ02 • X2 ≈ X2 • Z0 • CZ02 • CZ02 • Z0 • X2 • CZ02 • X2
step2 = by-assoc-and (under (X2 • Z0 • CZ02) (CZ02 • X2) (drel146.proved)) Eq.refl Eq.refl

step3 : X2 • Z0 • CZ02 • CZ02 • Z0 • X2 • CZ02 • X2 ≈ X2 • Z0 • Z0 • X2 • CZ02 • X2
step3 = by-assoc-and (under (X2 • Z0) (Z0 • X2 • CZ02 • X2) (elim_CZ02.proved)) Eq.refl Eq.refl

step4 : X2 • Z0 • Z0 • X2 • CZ02 • X2 ≈ X2 • X2 • CZ02 • X2
step4 = by-assoc-and (under (X2) (X2 • CZ02 • X2) (elim_Z0.proved)) Eq.refl Eq.refl

step5 : X2 • X2 • CZ02 • X2 ≈ CZ02 • X2
step5 = by-assoc-and (under (ε) (CZ02 • X2) (elim_X2.proved)) Eq.refl Eq.refl

proved : X2 • Z0 • CZ02 ≈ CZ02 • X2
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
