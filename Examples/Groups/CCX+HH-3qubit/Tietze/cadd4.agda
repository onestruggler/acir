{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.cadd4 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.cadd3 as cadd3
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CCX_c as symmetry_CCX_c

step0 : CX21 • CCX01 • CX21 ≈ CX21 • CCX01 • SWAP01 • CX20 • SWAP01
step0 = by-assoc-and (under (CX21 • CCX01) (ε) (axiom r031)) Eq.refl Eq.refl

step1 : CX21 • CCX01 • SWAP01 • CX20 • SWAP01 ≈ SWAP01 • CX20 • SWAP01 • CCX01 • SWAP01 • CX20 • SWAP01
step1 = by-assoc-and (under (ε) (CCX01 • SWAP01 • CX20 • SWAP01) (axiom r031)) Eq.refl Eq.refl

step2 : SWAP01 • CX20 • SWAP01 • CCX01 • SWAP01 • CX20 • SWAP01 ≈ SWAP01 • CX20 • CCX01 • CX20 • SWAP01
step2 = by-assoc-and (under (SWAP01 • CX20) (CX20 • SWAP01) (sym (symmetry_CCX_c.proved))) Eq.refl Eq.refl

step3 : SWAP01 • CX20 • CCX01 • CX20 • SWAP01 ≈ SWAP01 • CCX12 • CCX01 • CCX12 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (cadd3.proved)) Eq.refl Eq.refl

step4 : SWAP01 • CCX12 • CCX01 • CCX12 • SWAP01 ≈ SWAP01 • CCX12 • SWAP01 • CCX01 • SWAP01 • CCX12 • SWAP01
step4 = by-assoc-and (under (SWAP01 • CCX12) (CCX12 • SWAP01) (symmetry_CCX_c.proved)) Eq.refl Eq.refl

step5 : SWAP01 • CCX12 • SWAP01 • CCX01 • SWAP01 • CCX12 • SWAP01 ≈ SWAP01 • CCX12 • SWAP01 • CCX01 • CCX02
step5 = by-assoc-and (under (SWAP01 • CCX12 • SWAP01 • CCX01) (ε) (sym (axiom r014))) Eq.refl Eq.refl

step6 : SWAP01 • CCX12 • SWAP01 • CCX01 • CCX02 ≈ CCX02 • CCX01 • CCX02
step6 = by-assoc-and (under (ε) (CCX01 • CCX02) (sym (axiom r014))) Eq.refl Eq.refl

proved : CX21 • CCX01 • CX21 ≈ CCX02 • CCX01 • CCX02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
