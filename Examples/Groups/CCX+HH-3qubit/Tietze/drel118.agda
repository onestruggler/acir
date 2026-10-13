{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel118 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel160 as drel160
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ01 as elim_CZ01
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_Z1 as elim_Z1

step0 : X0 • Z1 • CZ01 ≈ X0 • Z1 • CZ01 • X0 • X0
step0 = by-assoc-and (under (X0 • Z1 • CZ01) (ε) (sym (axiom r021))) Eq.refl Eq.refl

step1 : X0 • Z1 • CZ01 • X0 • X0 ≈ X0 • Z1 • CZ01 • X0 • CZ01 • CZ01 • X0
step1 = by-assoc-and (under (X0 • Z1 • CZ01 • X0) (X0) (sym (elim_CZ01.proved))) Eq.refl Eq.refl

step2 : X0 • Z1 • CZ01 • X0 • CZ01 • CZ01 • X0 ≈ X0 • Z1 • CZ01 • CZ01 • Z1 • X0 • CZ01 • X0
step2 = by-assoc-and (under (X0 • Z1 • CZ01) (CZ01 • X0) (drel160.proved)) Eq.refl Eq.refl

step3 : X0 • Z1 • CZ01 • CZ01 • Z1 • X0 • CZ01 • X0 ≈ X0 • Z1 • Z1 • X0 • CZ01 • X0
step3 = by-assoc-and (under (X0 • Z1) (Z1 • X0 • CZ01 • X0) (elim_CZ01.proved)) Eq.refl Eq.refl

step4 : X0 • Z1 • Z1 • X0 • CZ01 • X0 ≈ X0 • X0 • CZ01 • X0
step4 = by-assoc-and (under (X0) (X0 • CZ01 • X0) (elim_Z1.proved)) Eq.refl Eq.refl

step5 : X0 • X0 • CZ01 • X0 ≈ CZ01 • X0
step5 = by-assoc-and (under (ε) (CZ01 • X0) (axiom r021)) Eq.refl Eq.refl

proved : X0 • Z1 • CZ01 ≈ CZ01 • X0
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
