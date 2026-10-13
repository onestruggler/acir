{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel101 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel129 as drel129
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CCX1 as elim_CCX1
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_X2 as elim_X2

step0 : X2 • CX01 • CCX02 ≈ X2 • CX01 • CCX02 • X2 • X2
step0 = by-assoc-and (under (X2 • CX01 • CCX02) (ε) (sym (elim_X2.proved))) Eq.refl Eq.refl

step1 : X2 • CX01 • CCX02 • X2 • X2 ≈ X2 • CX01 • CCX02 • X2 • CCX02 • CCX02 • X2
step1 = by-assoc-and (under (X2 • CX01 • CCX02 • X2) (X2) (sym (elim_CCX1.proved))) Eq.refl Eq.refl

step2 : X2 • CX01 • CCX02 • X2 • CCX02 • CCX02 • X2 ≈ X2 • CX01 • CCX02 • CCX02 • CX01 • X2 • CCX02 • X2
step2 = by-assoc-and (under (X2 • CX01 • CCX02) (CCX02 • X2) (drel129.proved)) Eq.refl Eq.refl

step3 : X2 • CX01 • CCX02 • CCX02 • CX01 • X2 • CCX02 • X2 ≈ X2 • CX01 • CX01 • X2 • CCX02 • X2
step3 = by-assoc-and (under (X2 • CX01) (CX01 • X2 • CCX02 • X2) (elim_CCX1.proved)) Eq.refl Eq.refl

step4 : X2 • CX01 • CX01 • X2 • CCX02 • X2 ≈ X2 • X2 • CCX02 • X2
step4 = by-assoc-and (under (X2) (X2 • CCX02 • X2) (axiom r022)) Eq.refl Eq.refl

step5 : X2 • X2 • CCX02 • X2 ≈ CCX02 • X2
step5 = by-assoc-and (under (ε) (CCX02 • X2) (elim_X2.proved)) Eq.refl Eq.refl

proved : X2 • CX01 • CCX02 ≈ CCX02 • X2
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
