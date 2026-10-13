{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel139 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CZ_b as symmetry_CZ_b
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CZ_c as symmetry_CZ_c
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CZ_e as symmetry_CZ_e

step0 : CX12 • CZ02 ≈ SWAP01 • CX02 • SWAP01 • CZ02
step0 = by-assoc-and (under (ε) (CZ02) (axiom r030)) Eq.refl Eq.refl

step1 : SWAP01 • CX02 • SWAP01 • CZ02 ≈ SWAP01 • SWAP12 • CX01 • SWAP12 • SWAP01 • CZ02
step1 = by-assoc-and (under (SWAP01) (SWAP01 • CZ02) (axiom r009)) Eq.refl Eq.refl

step2 : SWAP01 • SWAP12 • CX01 • SWAP12 • SWAP01 • CZ02 ≈ SWAP01 • SWAP12 • CX01 • SWAP12 • SWAP01 • SWAP01 • CZ12 • SWAP01
step2 = by-assoc-and (under (SWAP01 • SWAP12 • CX01 • SWAP12 • SWAP01) (ε) (symmetry_CZ_c.proved)) Eq.refl Eq.refl

step3 : SWAP01 • SWAP12 • CX01 • SWAP12 • SWAP01 • SWAP01 • CZ12 • SWAP01 ≈ SWAP01 • SWAP12 • CX01 • SWAP12 • SWAP01 • SWAP01 • SWAP12 • CZ12 • SWAP12 • SWAP01
step3 = by-assoc-and (under (SWAP01 • SWAP12 • CX01 • SWAP12 • SWAP01 • SWAP01) (SWAP01) (symmetry_CZ_e.proved)) Eq.refl Eq.refl

step4 : SWAP01 • SWAP12 • CX01 • SWAP12 • SWAP01 • SWAP01 • SWAP12 • CZ12 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • CX01 • SWAP12 • SWAP12 • CZ12 • SWAP12 • SWAP01
step4 = by-assoc-and (under (SWAP01 • SWAP12 • CX01 • SWAP12) (SWAP12 • CZ12 • SWAP12 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

step5 : SWAP01 • SWAP12 • CX01 • SWAP12 • SWAP12 • CZ12 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • CX01 • CZ12 • SWAP12 • SWAP01
step5 = by-assoc-and (under (SWAP01 • SWAP12 • CX01) (CZ12 • SWAP12 • SWAP01) (elim_SWAP12.proved)) Eq.refl Eq.refl

step6 : SWAP01 • SWAP12 • CX01 • CZ12 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • CZ12 • CZ02 • CX01 • SWAP12 • SWAP01
step6 = by-assoc-and (under (SWAP01 • SWAP12) (SWAP12 • SWAP01) (axiom r043)) Eq.refl Eq.refl

step7 : SWAP01 • SWAP12 • CZ12 • CZ02 • CX01 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • CZ12 • SWAP12 • CZ01 • SWAP12 • CX01 • SWAP12 • SWAP01
step7 = by-assoc-and (under (SWAP01 • SWAP12 • CZ12) (CX01 • SWAP12 • SWAP01) (axiom r018)) Eq.refl Eq.refl

step8 : SWAP01 • SWAP12 • CZ12 • SWAP12 • CZ01 • SWAP12 • CX01 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • CZ12 • SWAP12 • CZ01 • CX02 • SWAP01
step8 = by-assoc-and (under (SWAP01 • SWAP12 • CZ12 • SWAP12 • CZ01) (SWAP01) (sym (axiom r009))) Eq.refl Eq.refl

step9 : SWAP01 • SWAP12 • CZ12 • SWAP12 • CZ01 • CX02 • SWAP01 ≈ SWAP01 • CZ12 • CZ01 • CX02 • SWAP01
step9 = by-assoc-and (under (SWAP01) (CZ01 • CX02 • SWAP01) (sym (symmetry_CZ_e.proved))) Eq.refl Eq.refl

step10 : SWAP01 • CZ12 • CZ01 • CX02 • SWAP01 ≈ SWAP01 • CZ12 • SWAP01 • CZ01 • SWAP01 • CX02 • SWAP01
step10 = by-assoc-and (under (SWAP01 • CZ12) (CX02 • SWAP01) (symmetry_CZ_b.proved)) Eq.refl Eq.refl

step11 : SWAP01 • CZ12 • SWAP01 • CZ01 • SWAP01 • CX02 • SWAP01 ≈ SWAP01 • CZ12 • SWAP01 • CZ01 • CX12
step11 = by-assoc-and (under (SWAP01 • CZ12 • SWAP01 • CZ01) (ε) (sym (axiom r030))) Eq.refl Eq.refl

step12 : SWAP01 • CZ12 • SWAP01 • CZ01 • CX12 ≈ CZ02 • CZ01 • CX12
step12 = by-assoc-and (under (ε) (CZ01 • CX12) (sym (symmetry_CZ_c.proved))) Eq.refl Eq.refl

proved : CX12 • CZ02 ≈ CZ02 • CZ01 • CX12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (trans step11 (trans step12 (refl)))))))))))))
