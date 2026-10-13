{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel112 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX12 as elim_CX12
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_d as symmetry_CX_d
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_i as symmetry_CX_i

step0 : CX01 • CX12 ≈ CX12 • CX12 • CX01 • CX12
step0 = by-assoc-and (under (ε) (CX01 • CX12) (sym (elim_CX12.proved))) Eq.refl Eq.refl

step1 : CX12 • CX12 • CX01 • CX12 ≈ CX12 • CX01 • CX01 • CX12 • CX01 • CX12
step1 = by-assoc-and (under (CX12) (CX12 • CX01 • CX12) (sym (axiom r022))) Eq.refl Eq.refl

step2 : CX12 • CX01 • CX01 • CX12 • CX01 • CX12 ≈ CX12 • CX01 • CX01 • CX12 • CX01 • SWAP12 • CX21 • SWAP12
step2 = by-assoc-and (under (CX12 • CX01 • CX01 • CX12 • CX01) (ε) (symmetry_CX_d.proved)) Eq.refl Eq.refl

step3 : CX12 • CX01 • CX01 • CX12 • CX01 • SWAP12 • CX21 • SWAP12 ≈ CX12 • CX01 • CX01 • SWAP12 • CX21 • SWAP12 • CX01 • SWAP12 • CX21 • SWAP12
step3 = by-assoc-and (under (CX12 • CX01 • CX01) (CX01 • SWAP12 • CX21 • SWAP12) (symmetry_CX_d.proved)) Eq.refl Eq.refl

step4 : CX12 • CX01 • CX01 • SWAP12 • CX21 • SWAP12 • CX01 • SWAP12 • CX21 • SWAP12 ≈ CX12 • CX01 • CX01 • SWAP12 • CX21 • CX02 • CX21 • SWAP12
step4 = by-assoc-and (under (CX12 • CX01 • CX01 • SWAP12 • CX21) (CX21 • SWAP12) (sym (axiom r009))) Eq.refl Eq.refl

step5 : CX12 • CX01 • CX01 • SWAP12 • CX21 • CX02 • CX21 • SWAP12 ≈ CX12 • CX01 • SWAP12 • SWAP12 • CX01 • SWAP12 • CX21 • CX02 • CX21 • SWAP12
step5 = by-assoc-and (under (CX12 • CX01) (CX01 • SWAP12 • CX21 • CX02 • CX21 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step6 : CX12 • CX01 • SWAP12 • SWAP12 • CX01 • SWAP12 • CX21 • CX02 • CX21 • SWAP12 ≈ CX12 • CX01 • SWAP12 • CX02 • CX21 • CX02 • CX21 • SWAP12
step6 = by-assoc-and (under (CX12 • CX01 • SWAP12) (CX21 • CX02 • CX21 • SWAP12) (sym (axiom r009))) Eq.refl Eq.refl

step7 : CX12 • CX01 • SWAP12 • CX02 • CX21 • CX02 • CX21 • SWAP12 ≈ CX12 • CX01 • SWAP12 • CX02 • CX21 • CX02 • SWAP02 • CX01 • SWAP02 • SWAP12
step7 = by-assoc-and (under (CX12 • CX01 • SWAP12 • CX02 • CX21 • CX02) (SWAP12) (symmetry_CX_i.proved)) Eq.refl Eq.refl

step8 : CX12 • CX01 • SWAP12 • CX02 • CX21 • CX02 • SWAP02 • CX01 • SWAP02 • SWAP12 ≈ CX12 • CX01 • SWAP12 • CX02 • SWAP02 • CX01 • SWAP02 • CX02 • SWAP02 • CX01 • SWAP02 • SWAP12
step8 = by-assoc-and (under (CX12 • CX01 • SWAP12 • CX02) (CX02 • SWAP02 • CX01 • SWAP02 • SWAP12) (symmetry_CX_i.proved)) Eq.refl Eq.refl

step9 : CX12 • CX01 • SWAP12 • CX02 • SWAP02 • CX01 • SWAP02 • CX02 • SWAP02 • CX01 • SWAP02 • SWAP12 ≈ CX12 • CX01 • SWAP12 • CX02 • SWAP02 • CX01 • CX20 • CX01 • SWAP02 • SWAP12
step9 = by-assoc-and (under (CX12 • CX01 • SWAP12 • CX02 • SWAP02 • CX01) (CX01 • SWAP02 • SWAP12) (sym (axiom r029))) Eq.refl Eq.refl

step10 : CX12 • CX01 • SWAP12 • CX02 • SWAP02 • CX01 • CX20 • CX01 • SWAP02 • SWAP12 ≈ CX12 • CX01 • SWAP12 • SWAP02 • SWAP02 • CX02 • SWAP02 • CX01 • CX20 • CX01 • SWAP02 • SWAP12
step10 = by-assoc-and (under (CX12 • CX01 • SWAP12) (CX02 • SWAP02 • CX01 • CX20 • CX01 • SWAP02 • SWAP12) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step11 : CX12 • CX01 • SWAP12 • SWAP02 • SWAP02 • CX02 • SWAP02 • CX01 • CX20 • CX01 • SWAP02 • SWAP12 ≈ CX12 • CX01 • SWAP12 • SWAP02 • CX20 • CX01 • CX20 • CX01 • SWAP02 • SWAP12
step11 = by-assoc-and (under (CX12 • CX01 • SWAP12 • SWAP02) (CX01 • CX20 • CX01 • SWAP02 • SWAP12) (sym (axiom r029))) Eq.refl Eq.refl

step12 : CX12 • CX01 • SWAP12 • SWAP02 • CX20 • CX01 • CX20 • CX01 • SWAP02 • SWAP12 ≈ CX12 • CX01 • SWAP12 • SWAP02 • CX21 • SWAP02 • SWAP12
step12 = by-assoc-and (under (CX12 • CX01 • SWAP12 • SWAP02) (SWAP02 • SWAP12) (sym (axiom r006))) Eq.refl Eq.refl

step13 : CX12 • CX01 • SWAP12 • SWAP02 • CX21 • SWAP02 • SWAP12 ≈ CX12 • CX01 • SWAP12 • SWAP02 • SWAP02 • CX01 • SWAP02 • SWAP02 • SWAP12
step13 = by-assoc-and (under (CX12 • CX01 • SWAP12 • SWAP02) (SWAP02 • SWAP12) (symmetry_CX_i.proved)) Eq.refl Eq.refl

step14 : CX12 • CX01 • SWAP12 • SWAP02 • SWAP02 • CX01 • SWAP02 • SWAP02 • SWAP12 ≈ CX12 • CX01 • SWAP12 • SWAP02 • SWAP02 • CX01 • SWAP12
step14 = by-assoc-and (under (CX12 • CX01 • SWAP12 • SWAP02 • SWAP02 • CX01) (SWAP12) (elim_SWAP02.proved)) Eq.refl Eq.refl

step15 : CX12 • CX01 • SWAP12 • SWAP02 • SWAP02 • CX01 • SWAP12 ≈ CX12 • CX01 • SWAP12 • CX01 • SWAP12
step15 = by-assoc-and (under (CX12 • CX01 • SWAP12) (CX01 • SWAP12) (elim_SWAP02.proved)) Eq.refl Eq.refl

step16 : CX12 • CX01 • SWAP12 • CX01 • SWAP12 ≈ CX12 • CX01 • CX02
step16 = by-assoc-and (under (CX12 • CX01) (ε) (sym (axiom r009))) Eq.refl Eq.refl

proved : CX01 • CX12 ≈ CX12 • CX01 • CX02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (trans step11 (trans step12 (trans step13 (trans step14 (trans step15 (trans step16 (refl)))))))))))))))))
