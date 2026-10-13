{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel141 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel155 as drel155
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_i as symmetry_CX_i

step0 : CX01 • CCX01 ≈ CX01 • SWAP02 • CCX12 • SWAP02
step0 = by-assoc-and (under (CX01) (ε) (axiom r032)) Eq.refl Eq.refl

step1 : CX01 • SWAP02 • CCX12 • SWAP02 ≈ SWAP02 • SWAP02 • CX01 • SWAP02 • CCX12 • SWAP02
step1 = by-assoc-and (under (ε) (CX01 • SWAP02 • CCX12 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step2 : SWAP02 • SWAP02 • CX01 • SWAP02 • CCX12 • SWAP02 ≈ SWAP02 • CX21 • CCX12 • SWAP02
step2 = by-assoc-and (under (SWAP02) (CCX12 • SWAP02) (sym (symmetry_CX_i.proved))) Eq.refl Eq.refl

step3 : SWAP02 • CX21 • CCX12 • SWAP02 ≈ SWAP02 • CCX12 • CX20 • CX21 • SWAP02
step3 = by-assoc-and (under (SWAP02) (SWAP02) (drel155.proved)) Eq.refl Eq.refl

step4 : SWAP02 • CCX12 • CX20 • CX21 • SWAP02 ≈ SWAP02 • CCX12 • SWAP02 • CX02 • SWAP02 • CX21 • SWAP02
step4 = by-assoc-and (under (SWAP02 • CCX12) (CX21 • SWAP02) (axiom r029)) Eq.refl Eq.refl

step5 : SWAP02 • CCX12 • SWAP02 • CX02 • SWAP02 • CX21 • SWAP02 ≈ CCX01 • CX02 • SWAP02 • CX21 • SWAP02
step5 = by-assoc-and (under (ε) (CX02 • SWAP02 • CX21 • SWAP02) (sym (axiom r032))) Eq.refl Eq.refl

step6 : CCX01 • CX02 • SWAP02 • CX21 • SWAP02 ≈ CCX01 • CX02 • SWAP02 • SWAP02 • CX01 • SWAP02 • SWAP02
step6 = by-assoc-and (under (CCX01 • CX02 • SWAP02) (SWAP02) (symmetry_CX_i.proved)) Eq.refl Eq.refl

step7 : CCX01 • CX02 • SWAP02 • SWAP02 • CX01 • SWAP02 • SWAP02 ≈ CCX01 • CX02 • SWAP02 • SWAP02 • CX01
step7 = by-assoc-and (under (CCX01 • CX02 • SWAP02 • SWAP02 • CX01) (ε) (elim_SWAP02.proved)) Eq.refl Eq.refl

step8 : CCX01 • CX02 • SWAP02 • SWAP02 • CX01 ≈ CCX01 • CX02 • CX01
step8 = by-assoc-and (under (CCX01 • CX02) (CX01) (elim_SWAP02.proved)) Eq.refl Eq.refl

proved : CX01 • CCX01 ≈ CCX01 • CX02 • CX01
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))
