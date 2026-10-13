{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CCX_g where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CCX_f as symmetry_CCX_f
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_SWAP02 as symmetry_SWAP02

step0 : CCX12 ≈ CCX12 • SWAP01 • SWAP01
step0 = by-assoc-and (under (CCX12) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step1 : CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • CCX12 • SWAP01 • SWAP01
step1 = by-assoc-and (under (ε) (CCX12 • SWAP01 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step2 : SWAP01 • SWAP01 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • CCX02 • SWAP01
step2 = by-assoc-and (under (SWAP01) (SWAP01) (sym (axiom r014))) Eq.refl Eq.refl

step3 : SWAP01 • CCX02 • SWAP01 ≈ SWAP01 • SWAP02 • CCX02 • SWAP02 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (symmetry_CCX_f.proved)) Eq.refl Eq.refl

step4 : SWAP01 • SWAP02 • CCX02 • SWAP02 • SWAP01 ≈ SWAP01 • SWAP02 • CCX02 • SWAP01 • SWAP12 • SWAP01 • SWAP01
step4 = by-assoc-and (under (SWAP01 • SWAP02 • CCX02) (SWAP01) (symmetry_SWAP02.proved)) Eq.refl Eq.refl

step5 : SWAP01 • SWAP02 • CCX02 • SWAP01 • SWAP12 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • SWAP12 • SWAP01 • CCX02 • SWAP01 • SWAP12 • SWAP01 • SWAP01
step5 = by-assoc-and (under (SWAP01) (CCX02 • SWAP01 • SWAP12 • SWAP01 • SWAP01) (symmetry_SWAP02.proved)) Eq.refl Eq.refl

step6 : SWAP01 • SWAP01 • SWAP12 • SWAP01 • CCX02 • SWAP01 • SWAP12 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • SWAP12 • SWAP01 • CCX02 • SWAP01 • SWAP12
step6 = by-assoc-and (under (SWAP01 • SWAP01 • SWAP12 • SWAP01 • CCX02 • SWAP01 • SWAP12) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

step7 : SWAP01 • SWAP01 • SWAP12 • SWAP01 • CCX02 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • CCX02 • SWAP01 • SWAP12
step7 = by-assoc-and (under (ε) (SWAP12 • SWAP01 • CCX02 • SWAP01 • SWAP12) (elim_SWAP01.proved)) Eq.refl Eq.refl

step8 : SWAP12 • SWAP01 • CCX02 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • SWAP01 • CCX12 • SWAP01 • SWAP01 • SWAP12
step8 = by-assoc-and (under (SWAP12 • SWAP01) (SWAP01 • SWAP12) (axiom r014)) Eq.refl Eq.refl

step9 : SWAP12 • SWAP01 • SWAP01 • CCX12 • SWAP01 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • SWAP01 • CCX12 • SWAP12
step9 = by-assoc-and (under (SWAP12 • SWAP01 • SWAP01 • CCX12) (SWAP12) (elim_SWAP01.proved)) Eq.refl Eq.refl

step10 : SWAP12 • SWAP01 • SWAP01 • CCX12 • SWAP12 ≈ SWAP12 • CCX12 • SWAP12
step10 = by-assoc-and (under (SWAP12) (CCX12 • SWAP12) (elim_SWAP01.proved)) Eq.refl Eq.refl

proved : CCX12 ≈ SWAP12 • CCX12 • SWAP12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (refl)))))))))))
