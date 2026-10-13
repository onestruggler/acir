{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX12 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_CX_b as bifunct_X_CX_b
import Examples.Groups.CCX+HH-3qubit.Tietze.drel127 as drel127
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CCX1 as elim_CCX1
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX12_lemma as elim_CX12_lemma

step0 : CX12 • CX12 ≈ CX12 • K12 • X0 • CCX02 • X0 • CCX02 • K12
step0 = by-assoc-and (under (CX12) (ε) (sym (elim_CX12_lemma.proved))) Eq.refl Eq.refl

step1 : CX12 • K12 • X0 • CCX02 • X0 • CCX02 • K12 ≈ K12 • X0 • CCX02 • X0 • CCX02 • K12 • K12 • X0 • CCX02 • X0 • CCX02 • K12
step1 = by-assoc-and (under (ε) (K12 • X0 • CCX02 • X0 • CCX02 • K12) (sym (elim_CX12_lemma.proved))) Eq.refl Eq.refl

step2 : K12 • X0 • CCX02 • X0 • CCX02 • K12 • K12 • X0 • CCX02 • X0 • CCX02 • K12 ≈ K12 • X0 • CCX02 • X0 • CCX02 • X0 • CCX02 • X0 • CCX02 • K12
step2 = by-assoc-and (under (K12 • X0 • CCX02 • X0 • CCX02) (X0 • CCX02 • X0 • CCX02 • K12) (axiom r023)) Eq.refl Eq.refl

step3 : K12 • X0 • CCX02 • X0 • CCX02 • X0 • CCX02 • X0 • CCX02 • K12 ≈ K12 • X0 • CCX02 • X0 • CCX02 • X0 • CCX02 • CCX02 • CX21 • X0 • K12
step3 = by-assoc-and (under (K12 • X0 • CCX02 • X0 • CCX02 • X0 • CCX02) (K12) (drel127.proved)) Eq.refl Eq.refl

step4 : K12 • X0 • CCX02 • X0 • CCX02 • X0 • CCX02 • CCX02 • CX21 • X0 • K12 ≈ K12 • X0 • CCX02 • X0 • CCX02 • X0 • CX21 • X0 • K12
step4 = by-assoc-and (under (K12 • X0 • CCX02 • X0 • CCX02 • X0) (CX21 • X0 • K12) (elim_CCX1.proved)) Eq.refl Eq.refl

step5 : K12 • X0 • CCX02 • X0 • CCX02 • X0 • CX21 • X0 • K12 ≈ K12 • X0 • CCX02 • X0 • CCX02 • CX21 • X0 • X0 • K12
step5 = by-assoc-and (under (K12 • X0 • CCX02 • X0 • CCX02) (X0 • K12) (sym (bifunct_X_CX_b.proved))) Eq.refl Eq.refl

step6 : K12 • X0 • CCX02 • X0 • CCX02 • CX21 • X0 • X0 • K12 ≈ K12 • X0 • CCX02 • X0 • X0 • CCX02 • X0 • K12
step6 = by-assoc-and (under (K12 • X0 • CCX02 • X0) (X0 • K12) (sym (drel127.proved))) Eq.refl Eq.refl

step7 : K12 • X0 • CCX02 • X0 • X0 • CCX02 • X0 • K12 ≈ K12 • X0 • CCX02 • CCX02 • X0 • K12
step7 = by-assoc-and (under (K12 • X0 • CCX02) (CCX02 • X0 • K12) (axiom r021)) Eq.refl Eq.refl

step8 : K12 • X0 • CCX02 • CCX02 • X0 • K12 ≈ K12 • X0 • X0 • K12
step8 = by-assoc-and (under (K12 • X0) (X0 • K12) (elim_CCX1.proved)) Eq.refl Eq.refl

step9 : K12 • X0 • X0 • K12 ≈ K12 • K12
step9 = by-assoc-and (under (K12) (K12) (axiom r021)) Eq.refl Eq.refl

step10 : K12 • K12 ≈ ε
step10 = by-assoc-and (under (ε) (ε) (axiom r023)) Eq.refl Eq.refl

proved : CX12 • CX12 ≈ ε
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (refl)))))))))))
