{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel127 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel128 as drel128

step0 : X0 • CCX02 ≈ X0 • CCX02 • K12 • K12
step0 = by-assoc-and (under (X0 • CCX02) (ε) (sym (axiom r023))) Eq.refl Eq.refl

step1 : X0 • CCX02 • K12 • K12 ≈ X0 • K12 • CCX01 • K12
step1 = by-assoc-and (under (X0) (K12) (sym (drel128.proved))) Eq.refl Eq.refl

step2 : X0 • K12 • CCX01 • K12 ≈ K12 • X0 • CCX01 • K12
step2 = by-assoc-and (under (ε) (CCX01 • K12) (axiom r027)) Eq.refl Eq.refl

step3 : K12 • X0 • CCX01 • K12 ≈ K12 • CCX01 • CX12 • X0 • K12
step3 = by-assoc-and (under (K12) (K12) (axiom r042)) Eq.refl Eq.refl

step4 : K12 • CCX01 • CX12 • X0 • K12 ≈ CCX02 • K12 • CX12 • X0 • K12
step4 = by-assoc-and (under (ε) (CX12 • X0 • K12) (drel128.proved)) Eq.refl Eq.refl

step5 : CCX02 • K12 • CX12 • X0 • K12 ≈ CCX02 • K12 • K12 • CX21 • K12 • X0 • K12
step5 = by-assoc-and (under (CCX02 • K12) (X0 • K12) (axiom r007)) Eq.refl Eq.refl

step6 : CCX02 • K12 • K12 • CX21 • K12 • X0 • K12 ≈ CCX02 • CX21 • K12 • X0 • K12
step6 = by-assoc-and (under (CCX02) (CX21 • K12 • X0 • K12) (axiom r023)) Eq.refl Eq.refl

step7 : CCX02 • CX21 • K12 • X0 • K12 ≈ CCX02 • CX21 • K12 • K12 • X0
step7 = by-assoc-and (under (CCX02 • CX21 • K12) (ε) (axiom r027)) Eq.refl Eq.refl

step8 : CCX02 • CX21 • K12 • K12 • X0 ≈ CCX02 • CX21 • X0
step8 = by-assoc-and (under (CCX02 • CX21) (X0) (axiom r023)) Eq.refl Eq.refl

proved : X0 • CCX02 ≈ CCX02 • CX21 • X0
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))
