{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.elim_X1 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Proofs.X0X1 as X0X1
import Examples.Groups.CCX+HH-3qubit.Tietze.drel162 as drel162

step0 : X1 • X1 ≈ X1 • CX01 • X0 • CX01 • X0
step0 = by-assoc-and (under (X1) (ε) (axiom r002)) Eq.refl Eq.refl

step1 : X1 • CX01 • X0 • CX01 • X0 ≈ CX01 • X0 • CX01 • X0 • CX01 • X0 • CX01 • X0
step1 = by-assoc-and (under (ε) (CX01 • X0 • CX01 • X0) (axiom r002)) Eq.refl Eq.refl

step2 : CX01 • X0 • CX01 • X0 • CX01 • X0 • CX01 • X0 ≈ CX01 • X0 • CX01 • X0 • CX01 • CX01 • X1 • X0 • X0
step2 = by-assoc-and (under (CX01 • X0 • CX01 • X0 • CX01) (X0) (drel162.proved)) Eq.refl Eq.refl

step3 : CX01 • X0 • CX01 • X0 • CX01 • CX01 • X1 • X0 • X0 ≈ CX01 • X0 • CX01 • X0 • CX01 • CX01 • X1
step3 = by-assoc-and (under (CX01 • X0 • CX01 • X0 • CX01 • CX01 • X1) (ε) (axiom r021)) Eq.refl Eq.refl

step4 : CX01 • X0 • CX01 • X0 • CX01 • CX01 • X1 ≈ CX01 • X0 • CX01 • X0 • X1
step4 = by-assoc-and (under (CX01 • X0 • CX01 • X0) (X1) (axiom r022)) Eq.refl Eq.refl

step5 : CX01 • X0 • CX01 • X0 • X1 ≈ CX01 • X0 • CX01 • X1 • X0
step5 = by-assoc-and (under (CX01 • X0 • CX01) (ε) (X0X1.proved)) Eq.refl Eq.refl

step6 : CX01 • X0 • CX01 • X1 • X0 ≈ CX01 • X0 • X0 • CX01
step6 = by-assoc-and (under (CX01 • X0) (ε) (sym (drel162.proved))) Eq.refl Eq.refl

step7 : CX01 • X0 • X0 • CX01 ≈ CX01 • CX01
step7 = by-assoc-and (under (CX01) (CX01) (axiom r021)) Eq.refl Eq.refl

step8 : CX01 • CX01 ≈ ε
step8 = by-assoc-and (under (ε) (ε) (axiom r022)) Eq.refl Eq.refl

proved : X1 • X1 ≈ ε
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))
