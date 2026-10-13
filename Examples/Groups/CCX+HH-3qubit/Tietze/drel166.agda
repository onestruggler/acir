{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel166 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel165 as drel165
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CZ_b as symmetry_CZ_b

step0 : CX01 • CZ02 ≈ CX01 • SWAP12 • CZ01 • SWAP12
step0 = by-assoc-and (under (CX01) (ε) (axiom r018)) Eq.refl Eq.refl

step1 : CX01 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • SWAP12 • CX01 • SWAP12 • CZ01 • SWAP12
step1 = by-assoc-and (under (ε) (CX01 • SWAP12 • CZ01 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step2 : SWAP12 • SWAP12 • CX01 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • CX02 • CZ01 • SWAP12
step2 = by-assoc-and (under (SWAP12) (CZ01 • SWAP12) (sym (axiom r009))) Eq.refl Eq.refl

step3 : SWAP12 • CX02 • CZ01 • SWAP12 ≈ SWAP12 • CX02 • SWAP01 • CZ01 • SWAP01 • SWAP12
step3 = by-assoc-and (under (SWAP12 • CX02) (SWAP12) (symmetry_CZ_b.proved)) Eq.refl Eq.refl

step4 : SWAP12 • CX02 • SWAP01 • CZ01 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • SWAP01 • CX02 • SWAP01 • CZ01 • SWAP01 • SWAP12
step4 = by-assoc-and (under (SWAP12) (CX02 • SWAP01 • CZ01 • SWAP01 • SWAP12) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step5 : SWAP12 • SWAP01 • SWAP01 • CX02 • SWAP01 • CZ01 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • CX12 • CZ01 • SWAP01 • SWAP12
step5 = by-assoc-and (under (SWAP12 • SWAP01) (CZ01 • SWAP01 • SWAP12) (sym (axiom r030))) Eq.refl Eq.refl

step6 : SWAP12 • SWAP01 • CX12 • CZ01 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • CZ01 • CX12 • SWAP01 • SWAP12
step6 = by-assoc-and (under (SWAP12 • SWAP01) (SWAP01 • SWAP12) (drel165.proved)) Eq.refl Eq.refl

step7 : SWAP12 • SWAP01 • CZ01 • CX12 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • CZ01 • SWAP01 • CX02 • SWAP01 • SWAP01 • SWAP12
step7 = by-assoc-and (under (SWAP12 • SWAP01 • CZ01) (SWAP01 • SWAP12) (axiom r030)) Eq.refl Eq.refl

step8 : SWAP12 • SWAP01 • CZ01 • SWAP01 • CX02 • SWAP01 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • CZ01 • SWAP01 • CX02 • SWAP12
step8 = by-assoc-and (under (SWAP12 • SWAP01 • CZ01 • SWAP01 • CX02) (SWAP12) (elim_SWAP01.proved)) Eq.refl Eq.refl

step9 : SWAP12 • SWAP01 • CZ01 • SWAP01 • CX02 • SWAP12 ≈ SWAP12 • CZ01 • CX02 • SWAP12
step9 = by-assoc-and (under (SWAP12) (CX02 • SWAP12) (sym (symmetry_CZ_b.proved))) Eq.refl Eq.refl

step10 : SWAP12 • CZ01 • CX02 • SWAP12 ≈ SWAP12 • CZ01 • SWAP12 • CX01 • SWAP12 • SWAP12
step10 = by-assoc-and (under (SWAP12 • CZ01) (SWAP12) (axiom r009)) Eq.refl Eq.refl

step11 : SWAP12 • CZ01 • SWAP12 • CX01 • SWAP12 • SWAP12 ≈ SWAP12 • CZ01 • SWAP12 • CX01
step11 = by-assoc-and (under (SWAP12 • CZ01 • SWAP12 • CX01) (ε) (elim_SWAP12.proved)) Eq.refl Eq.refl

step12 : SWAP12 • CZ01 • SWAP12 • CX01 ≈ CZ02 • CX01
step12 = by-assoc-and (under (ε) (CX01) (sym (axiom r018))) Eq.refl Eq.refl

proved : CX01 • CZ02 ≈ CZ02 • CX01
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (trans step11 (trans step12 (refl)))))))))))))
