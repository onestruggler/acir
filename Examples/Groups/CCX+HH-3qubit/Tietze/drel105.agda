{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel105 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Proofs.X0X1 as X0X1
import Examples.Groups.CCX+HH-3qubit.Tietze.drel162 as drel162
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_X1 as elim_X1

step0 : X0 • X1 • CX01 ≈ X1 • X0 • CX01
step0 = by-assoc-and (under (ε) (CX01) (X0X1.proved)) Eq.refl Eq.refl

step1 : X1 • X0 • CX01 ≈ CX01 • CX01 • X1 • X0 • CX01
step1 = by-assoc-and (under (ε) (X1 • X0 • CX01) (sym (axiom r022))) Eq.refl Eq.refl

step2 : CX01 • CX01 • X1 • X0 • CX01 ≈ CX01 • X0 • X0 • CX01 • X1 • X0 • CX01
step2 = by-assoc-and (under (CX01) (CX01 • X1 • X0 • CX01) (sym (axiom r021))) Eq.refl Eq.refl

step3 : CX01 • X0 • X0 • CX01 • X1 • X0 • CX01 ≈ CX01 • X0 • CX01 • X1 • X0 • X1 • X0 • CX01
step3 = by-assoc-and (under (CX01 • X0) (X1 • X0 • CX01) (drel162.proved)) Eq.refl Eq.refl

step4 : CX01 • X0 • CX01 • X1 • X0 • X1 • X0 • CX01 ≈ CX01 • X0 • CX01 • X0 • X1 • X1 • X0 • CX01
step4 = by-assoc-and (under (CX01 • X0 • CX01) (X1 • X0 • CX01) (sym (X0X1.proved))) Eq.refl Eq.refl

step5 : CX01 • X0 • CX01 • X0 • X1 • X1 • X0 • CX01 ≈ CX01 • X0 • CX01 • X0 • X0 • CX01
step5 = by-assoc-and (under (CX01 • X0 • CX01 • X0) (X0 • CX01) (elim_X1.proved)) Eq.refl Eq.refl

step6 : CX01 • X0 • CX01 • X0 • X0 • CX01 ≈ CX01 • X0 • CX01 • CX01
step6 = by-assoc-and (under (CX01 • X0 • CX01) (CX01) (axiom r021)) Eq.refl Eq.refl

step7 : CX01 • X0 • CX01 • CX01 ≈ CX01 • X0
step7 = by-assoc-and (under (CX01 • X0) (ε) (axiom r022)) Eq.refl Eq.refl

proved : X0 • X1 • CX01 ≈ CX01 • X0
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (refl))))))))
