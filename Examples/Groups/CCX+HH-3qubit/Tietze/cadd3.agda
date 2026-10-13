{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.cadd3 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.cadd0 as cadd0
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02

step0 : CX20 • CCX01 • CX20 ≈ CX20 • CCX01 • SWAP02 • CX02 • SWAP02
step0 = by-assoc-and (under (CX20 • CCX01) (ε) (axiom r029)) Eq.refl Eq.refl

step1 : CX20 • CCX01 • SWAP02 • CX02 • SWAP02 ≈ SWAP02 • CX02 • SWAP02 • CCX01 • SWAP02 • CX02 • SWAP02
step1 = by-assoc-and (under (ε) (CCX01 • SWAP02 • CX02 • SWAP02) (axiom r029)) Eq.refl Eq.refl

step2 : SWAP02 • CX02 • SWAP02 • CCX01 • SWAP02 • CX02 • SWAP02 ≈ SWAP02 • CX02 • SWAP02 • SWAP02 • CCX12 • SWAP02 • SWAP02 • CX02 • SWAP02
step2 = by-assoc-and (under (SWAP02 • CX02 • SWAP02) (SWAP02 • CX02 • SWAP02) (axiom r032)) Eq.refl Eq.refl

step3 : SWAP02 • CX02 • SWAP02 • SWAP02 • CCX12 • SWAP02 • SWAP02 • CX02 • SWAP02 ≈ SWAP02 • CX02 • SWAP02 • SWAP02 • CCX12 • CX02 • SWAP02
step3 = by-assoc-and (under (SWAP02 • CX02 • SWAP02 • SWAP02 • CCX12) (CX02 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

step4 : SWAP02 • CX02 • SWAP02 • SWAP02 • CCX12 • CX02 • SWAP02 ≈ SWAP02 • CX02 • CCX12 • CX02 • SWAP02
step4 = by-assoc-and (under (SWAP02 • CX02) (CCX12 • CX02 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

step5 : SWAP02 • CX02 • CCX12 • CX02 • SWAP02 ≈ SWAP02 • CCX01 • CCX12 • CCX01 • SWAP02
step5 = by-assoc-and (under (SWAP02) (SWAP02) (cadd0.proved)) Eq.refl Eq.refl

step6 : SWAP02 • CCX01 • CCX12 • CCX01 • SWAP02 ≈ SWAP02 • CCX01 • CCX12 • SWAP02 • CCX12 • SWAP02 • SWAP02
step6 = by-assoc-and (under (SWAP02 • CCX01 • CCX12) (SWAP02) (axiom r032)) Eq.refl Eq.refl

step7 : SWAP02 • CCX01 • CCX12 • SWAP02 • CCX12 • SWAP02 • SWAP02 ≈ SWAP02 • SWAP02 • CCX12 • SWAP02 • CCX12 • SWAP02 • CCX12 • SWAP02 • SWAP02
step7 = by-assoc-and (under (SWAP02) (CCX12 • SWAP02 • CCX12 • SWAP02 • SWAP02) (axiom r032)) Eq.refl Eq.refl

step8 : SWAP02 • SWAP02 • CCX12 • SWAP02 • CCX12 • SWAP02 • CCX12 • SWAP02 • SWAP02 ≈ SWAP02 • SWAP02 • CCX12 • SWAP02 • CCX12 • SWAP02 • CCX12
step8 = by-assoc-and (under (SWAP02 • SWAP02 • CCX12 • SWAP02 • CCX12 • SWAP02 • CCX12) (ε) (elim_SWAP02.proved)) Eq.refl Eq.refl

step9 : SWAP02 • SWAP02 • CCX12 • SWAP02 • CCX12 • SWAP02 • CCX12 ≈ CCX12 • SWAP02 • CCX12 • SWAP02 • CCX12
step9 = by-assoc-and (under (ε) (CCX12 • SWAP02 • CCX12 • SWAP02 • CCX12) (elim_SWAP02.proved)) Eq.refl Eq.refl

step10 : CCX12 • SWAP02 • CCX12 • SWAP02 • CCX12 ≈ CCX12 • CCX01 • CCX12
step10 = by-assoc-and (under (CCX12) (CCX12) (sym (axiom r032))) Eq.refl Eq.refl

proved : CX20 • CCX01 • CX20 ≈ CCX12 • CCX01 • CCX12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (refl)))))))))))
