{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel160 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Proofs.X0X1 as X0X1
import Examples.Groups.CCX+HH-3qubit.Tietze.drel162 as drel162
import Examples.Groups.CCX+HH-3qubit.Tietze.drel49 as drel49

step0 : X0 • CZ01 ≈ X0 • K12 • K12 • CZ01
step0 = by-assoc-and (under (X0) (CZ01) (sym (axiom r023))) Eq.refl Eq.refl

step1 : X0 • K12 • K12 • CZ01 ≈ K12 • X0 • K12 • CZ01
step1 = by-assoc-and (under (ε) (K12 • CZ01) (axiom r027)) Eq.refl Eq.refl

step2 : K12 • X0 • K12 • CZ01 ≈ K12 • X0 • CX01 • K12
step2 = by-assoc-and (under (K12 • X0) (ε) (drel49.proved)) Eq.refl Eq.refl

step3 : K12 • X0 • CX01 • K12 ≈ K12 • CX01 • X1 • X0 • K12
step3 = by-assoc-and (under (K12) (K12) (drel162.proved)) Eq.refl Eq.refl

step4 : K12 • CX01 • X1 • X0 • K12 ≈ K12 • CX01 • X0 • X1 • K12
step4 = by-assoc-and (under (K12 • CX01) (K12) (sym (X0X1.proved))) Eq.refl Eq.refl

step5 : K12 • CX01 • X0 • X1 • K12 ≈ K12 • CX01 • X1 • X0 • K12
step5 = by-assoc-and (under (K12 • CX01) (K12) (X0X1.proved)) Eq.refl Eq.refl

step6 : K12 • CX01 • X1 • X0 • K12 ≈ K12 • CX01 • X1 • K12 • X0
step6 = by-assoc-and (under (K12 • CX01 • X1) (ε) (axiom r027)) Eq.refl Eq.refl

step7 : K12 • CX01 • X1 • K12 • X0 ≈ K12 • CX01 • K12 • K12 • X1 • K12 • X0
step7 = by-assoc-and (under (K12 • CX01) (X1 • K12 • X0) (sym (axiom r023))) Eq.refl Eq.refl

step8 : K12 • CX01 • K12 • K12 • X1 • K12 • X0 ≈ K12 • CX01 • K12 • Z1 • X0
step8 = by-assoc-and (under (K12 • CX01 • K12) (X0) (sym (axiom r004))) Eq.refl Eq.refl

step9 : K12 • CX01 • K12 • Z1 • X0 ≈ CZ01 • Z1 • X0
step9 = by-assoc-and (under (ε) (Z1 • X0) (sym (axiom r001))) Eq.refl Eq.refl

proved : X0 • CZ01 ≈ CZ01 • Z1 • X0
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (refl))))))))))
