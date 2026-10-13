{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_SWAP12_alt where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ12 as elim_CZ12
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12

step0 : K12 • CZ12 • K12 • CZ12 • K12 • CZ12 ≈ SWAP12 • SWAP12 • K12 • CZ12 • K12 • CZ12 • K12 • CZ12
step0 = by-assoc-and (under (ε) (K12 • CZ12 • K12 • CZ12 • K12 • CZ12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step1 : SWAP12 • SWAP12 • K12 • CZ12 • K12 • CZ12 • K12 • CZ12 ≈ SWAP12 • CZ12 • K12 • CZ12 • K12 • CZ12 • K12 • K12 • CZ12 • K12 • CZ12 • K12 • CZ12
step1 = by-assoc-and (under (SWAP12) (K12 • CZ12 • K12 • CZ12 • K12 • CZ12) (axiom r020)) Eq.refl Eq.refl

step2 : SWAP12 • CZ12 • K12 • CZ12 • K12 • CZ12 • K12 • K12 • CZ12 • K12 • CZ12 • K12 • CZ12 ≈ SWAP12 • CZ12 • K12 • CZ12 • K12 • CZ12 • CZ12 • K12 • CZ12 • K12 • CZ12
step2 = by-assoc-and (under (SWAP12 • CZ12 • K12 • CZ12 • K12 • CZ12) (CZ12 • K12 • CZ12 • K12 • CZ12) (axiom r023)) Eq.refl Eq.refl

step3 : SWAP12 • CZ12 • K12 • CZ12 • K12 • CZ12 • CZ12 • K12 • CZ12 • K12 • CZ12 ≈ SWAP12 • CZ12 • K12 • CZ12 • K12 • K12 • CZ12 • K12 • CZ12
step3 = by-assoc-and (under (SWAP12 • CZ12 • K12 • CZ12 • K12) (K12 • CZ12 • K12 • CZ12) (elim_CZ12.proved)) Eq.refl Eq.refl

step4 : SWAP12 • CZ12 • K12 • CZ12 • K12 • K12 • CZ12 • K12 • CZ12 ≈ SWAP12 • CZ12 • K12 • CZ12 • CZ12 • K12 • CZ12
step4 = by-assoc-and (under (SWAP12 • CZ12 • K12 • CZ12) (CZ12 • K12 • CZ12) (axiom r023)) Eq.refl Eq.refl

step5 : SWAP12 • CZ12 • K12 • CZ12 • CZ12 • K12 • CZ12 ≈ SWAP12 • CZ12 • K12 • K12 • CZ12
step5 = by-assoc-and (under (SWAP12 • CZ12 • K12) (K12 • CZ12) (elim_CZ12.proved)) Eq.refl Eq.refl

step6 : SWAP12 • CZ12 • K12 • K12 • CZ12 ≈ SWAP12 • CZ12 • CZ12
step6 = by-assoc-and (under (SWAP12 • CZ12) (CZ12) (axiom r023)) Eq.refl Eq.refl

step7 : SWAP12 • CZ12 • CZ12 ≈ SWAP12
step7 = by-assoc-and (under (SWAP12) (ε) (elim_CZ12.proved)) Eq.refl Eq.refl

proved : K12 • CZ12 • K12 • CZ12 • K12 • CZ12 ≈ SWAP12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (refl))))))))
