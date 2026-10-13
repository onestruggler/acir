{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel157 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel168 as drel168
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_e as symmetry_CX_e
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CZ_b as symmetry_CZ_b

step0 : CZ01 • Z1 • CX10 ≈ CZ01 • SWAP01 • Z0 • SWAP01 • CX10
step0 = by-assoc-and (under (CZ01) (CX10) (axiom r034)) Eq.refl Eq.refl

step1 : CZ01 • SWAP01 • Z0 • SWAP01 • CX10 ≈ SWAP01 • CZ01 • SWAP01 • SWAP01 • Z0 • SWAP01 • CX10
step1 = by-assoc-and (under (ε) (SWAP01 • Z0 • SWAP01 • CX10) (symmetry_CZ_b.proved)) Eq.refl Eq.refl

step2 : SWAP01 • CZ01 • SWAP01 • SWAP01 • Z0 • SWAP01 • CX10 ≈ SWAP01 • CZ01 • Z0 • SWAP01 • CX10
step2 = by-assoc-and (under (SWAP01 • CZ01) (Z0 • SWAP01 • CX10) (elim_SWAP01.proved)) Eq.refl Eq.refl

step3 : SWAP01 • CZ01 • Z0 • SWAP01 • CX10 ≈ SWAP01 • CZ01 • Z0 • SWAP01 • CX10 • SWAP01 • SWAP01
step3 = by-assoc-and (under (SWAP01 • CZ01 • Z0 • SWAP01 • CX10) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step4 : SWAP01 • CZ01 • Z0 • SWAP01 • CX10 • SWAP01 • SWAP01 ≈ SWAP01 • CZ01 • Z0 • CX01 • SWAP01
step4 = by-assoc-and (under (SWAP01 • CZ01 • Z0) (SWAP01) (sym (symmetry_CX_e.proved))) Eq.refl Eq.refl

step5 : SWAP01 • CZ01 • Z0 • CX01 • SWAP01 ≈ SWAP01 • CX01 • CZ01 • SWAP01
step5 = by-assoc-and (under (SWAP01) (SWAP01) (sym (drel168.proved))) Eq.refl Eq.refl

step6 : SWAP01 • CX01 • CZ01 • SWAP01 ≈ SWAP01 • SWAP01 • CX10 • SWAP01 • CZ01 • SWAP01
step6 = by-assoc-and (under (SWAP01) (CZ01 • SWAP01) (symmetry_CX_e.proved)) Eq.refl Eq.refl

step7 : SWAP01 • SWAP01 • CX10 • SWAP01 • CZ01 • SWAP01 ≈ CX10 • SWAP01 • CZ01 • SWAP01
step7 = by-assoc-and (under (ε) (CX10 • SWAP01 • CZ01 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

step8 : CX10 • SWAP01 • CZ01 • SWAP01 ≈ CX10 • CZ01
step8 = by-assoc-and (under (CX10) (ε) (sym (symmetry_CZ_b.proved))) Eq.refl Eq.refl

proved : CZ01 • Z1 • CX10 ≈ CX10 • CZ01
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))
