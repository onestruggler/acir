{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel140 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel155 as drel155
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01

step0 : CX20 • CCX02 ≈ CX20 • SWAP01 • CCX12 • SWAP01
step0 = by-assoc-and (under (CX20) (ε) (axiom r014)) Eq.refl Eq.refl

step1 : CX20 • SWAP01 • CCX12 • SWAP01 ≈ SWAP01 • SWAP01 • CX20 • SWAP01 • CCX12 • SWAP01
step1 = by-assoc-and (under (ε) (CX20 • SWAP01 • CCX12 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step2 : SWAP01 • SWAP01 • CX20 • SWAP01 • CCX12 • SWAP01 ≈ SWAP01 • CX21 • CCX12 • SWAP01
step2 = by-assoc-and (under (SWAP01) (CCX12 • SWAP01) (sym (axiom r031))) Eq.refl Eq.refl

step3 : SWAP01 • CX21 • CCX12 • SWAP01 ≈ SWAP01 • CCX12 • CX20 • CX21 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (drel155.proved)) Eq.refl Eq.refl

step4 : SWAP01 • CCX12 • CX20 • CX21 • SWAP01 ≈ SWAP01 • CCX12 • CX20 • SWAP01 • CX20 • SWAP01 • SWAP01
step4 = by-assoc-and (under (SWAP01 • CCX12 • CX20) (SWAP01) (axiom r031)) Eq.refl Eq.refl

step5 : SWAP01 • CCX12 • CX20 • SWAP01 • CX20 • SWAP01 • SWAP01 ≈ SWAP01 • CCX12 • CX20 • SWAP01 • CX20
step5 = by-assoc-and (under (SWAP01 • CCX12 • CX20 • SWAP01 • CX20) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

step6 : SWAP01 • CCX12 • CX20 • SWAP01 • CX20 ≈ SWAP01 • CCX12 • SWAP01 • SWAP01 • CX20 • SWAP01 • CX20
step6 = by-assoc-and (under (SWAP01 • CCX12) (CX20 • SWAP01 • CX20) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step7 : SWAP01 • CCX12 • SWAP01 • SWAP01 • CX20 • SWAP01 • CX20 ≈ SWAP01 • CCX12 • SWAP01 • CX21 • CX20
step7 = by-assoc-and (under (SWAP01 • CCX12 • SWAP01) (CX20) (sym (axiom r031))) Eq.refl Eq.refl

step8 : SWAP01 • CCX12 • SWAP01 • CX21 • CX20 ≈ CCX02 • CX21 • CX20
step8 = by-assoc-and (under (ε) (CX21 • CX20) (sym (axiom r014))) Eq.refl Eq.refl

proved : CX20 • CCX02 ≈ CCX02 • CX21 • CX20
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))
