{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CCX_c where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_SWAP01 as symmetry_SWAP01
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_SWAP01_alt as symmetry_SWAP01_alt

step0 : CCX01 ≈ SWAP12 • CCX02 • SWAP12
step0 = by-assoc-and (under (ε) (ε) (axiom r033)) Eq.refl Eq.refl

step1 : SWAP12 • CCX02 • SWAP12 ≈ SWAP12 • SWAP01 • CCX12 • SWAP01 • SWAP12
step1 = by-assoc-and (under (SWAP12) (SWAP12) (axiom r014)) Eq.refl Eq.refl

step2 : SWAP12 • SWAP01 • CCX12 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • CCX12 • SWAP02 • SWAP02 • SWAP01 • SWAP12
step2 = by-assoc-and (under (SWAP12 • SWAP01 • CCX12) (SWAP01 • SWAP12) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step3 : SWAP12 • SWAP01 • CCX12 • SWAP02 • SWAP02 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • SWAP02 • SWAP02 • CCX12 • SWAP02 • SWAP02 • SWAP01 • SWAP12
step3 = by-assoc-and (under (SWAP12 • SWAP01) (CCX12 • SWAP02 • SWAP02 • SWAP01 • SWAP12) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step4 : SWAP12 • SWAP01 • SWAP02 • SWAP02 • CCX12 • SWAP02 • SWAP02 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • SWAP02 • CCX01 • SWAP02 • SWAP01 • SWAP12
step4 = by-assoc-and (under (SWAP12 • SWAP01 • SWAP02) (SWAP02 • SWAP01 • SWAP12) (sym (axiom r032))) Eq.refl Eq.refl

step5 : SWAP12 • SWAP01 • SWAP02 • CCX01 • SWAP02 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • SWAP02 • CCX01 • SWAP02 • SWAP02 • SWAP12 • SWAP02 • SWAP12
step5 = by-assoc-and (under (SWAP12 • SWAP01 • SWAP02 • CCX01 • SWAP02) (SWAP12) (symmetry_SWAP01.proved)) Eq.refl Eq.refl

step6 : SWAP12 • SWAP01 • SWAP02 • CCX01 • SWAP02 • SWAP02 • SWAP12 • SWAP02 • SWAP12 ≈ SWAP12 • SWAP02 • SWAP12 • SWAP02 • SWAP02 • CCX01 • SWAP02 • SWAP02 • SWAP12 • SWAP02 • SWAP12
step6 = by-assoc-and (under (SWAP12) (SWAP02 • CCX01 • SWAP02 • SWAP02 • SWAP12 • SWAP02 • SWAP12) (symmetry_SWAP01.proved)) Eq.refl Eq.refl

step7 : SWAP12 • SWAP02 • SWAP12 • SWAP02 • SWAP02 • CCX01 • SWAP02 • SWAP02 • SWAP12 • SWAP02 • SWAP12 ≈ SWAP12 • SWAP02 • SWAP12 • SWAP02 • SWAP02 • CCX01 • SWAP12 • SWAP02 • SWAP12
step7 = by-assoc-and (under (SWAP12 • SWAP02 • SWAP12 • SWAP02 • SWAP02 • CCX01) (SWAP12 • SWAP02 • SWAP12) (elim_SWAP02.proved)) Eq.refl Eq.refl

step8 : SWAP12 • SWAP02 • SWAP12 • SWAP02 • SWAP02 • CCX01 • SWAP12 • SWAP02 • SWAP12 ≈ SWAP12 • SWAP02 • SWAP12 • CCX01 • SWAP12 • SWAP02 • SWAP12
step8 = by-assoc-and (under (SWAP12 • SWAP02 • SWAP12) (CCX01 • SWAP12 • SWAP02 • SWAP12) (elim_SWAP02.proved)) Eq.refl Eq.refl

step9 : SWAP12 • SWAP02 • SWAP12 • CCX01 • SWAP12 • SWAP02 • SWAP12 ≈ SWAP12 • SWAP02 • SWAP12 • CCX01 • SWAP01
step9 = by-assoc-and (under (SWAP12 • SWAP02 • SWAP12 • CCX01) (ε) (sym (symmetry_SWAP01_alt.proved))) Eq.refl Eq.refl

step10 : SWAP12 • SWAP02 • SWAP12 • CCX01 • SWAP01 ≈ SWAP01 • CCX01 • SWAP01
step10 = by-assoc-and (under (ε) (CCX01 • SWAP01) (sym (symmetry_SWAP01_alt.proved))) Eq.refl Eq.refl

proved : CCX01 ≈ SWAP01 • CCX01 • SWAP01
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (refl)))))))))))
