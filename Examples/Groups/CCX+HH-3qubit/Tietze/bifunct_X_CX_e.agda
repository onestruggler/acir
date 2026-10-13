{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_CX_e where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01

step0 : CX02 • X1 ≈ CX02 • SWAP01 • X0 • SWAP01
step0 = by-assoc-and (under (CX02) (ε) (axiom r028)) Eq.refl Eq.refl

step1 : CX02 • SWAP01 • X0 • SWAP01 ≈ SWAP01 • SWAP01 • CX02 • SWAP01 • X0 • SWAP01
step1 = by-assoc-and (under (ε) (CX02 • SWAP01 • X0 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step2 : SWAP01 • SWAP01 • CX02 • SWAP01 • X0 • SWAP01 ≈ SWAP01 • CX12 • X0 • SWAP01
step2 = by-assoc-and (under (SWAP01) (X0 • SWAP01) (sym (axiom r030))) Eq.refl Eq.refl

step3 : SWAP01 • CX12 • X0 • SWAP01 ≈ SWAP01 • X0 • CX12 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (axiom r026)) Eq.refl Eq.refl

step4 : SWAP01 • X0 • CX12 • SWAP01 ≈ SWAP01 • X0 • SWAP01 • CX02 • SWAP01 • SWAP01
step4 = by-assoc-and (under (SWAP01 • X0) (SWAP01) (axiom r030)) Eq.refl Eq.refl

step5 : SWAP01 • X0 • SWAP01 • CX02 • SWAP01 • SWAP01 ≈ X1 • CX02 • SWAP01 • SWAP01
step5 = by-assoc-and (under (ε) (CX02 • SWAP01 • SWAP01) (sym (axiom r028))) Eq.refl Eq.refl

step6 : X1 • CX02 • SWAP01 • SWAP01 ≈ X1 • CX02
step6 = by-assoc-and (under (X1 • CX02) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

proved : CX02 • X1 ≈ X1 • CX02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
