{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_g where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_SWAP02 as symmetry_SWAP02

step0 : CX21 ≈ SWAP01 • CX20 • SWAP01
step0 = by-assoc-and (under (ε) (ε) (axiom r031)) Eq.refl Eq.refl

step1 : SWAP01 • CX20 • SWAP01 ≈ SWAP01 • SWAP02 • CX02 • SWAP02 • SWAP01
step1 = by-assoc-and (under (SWAP01) (SWAP01) (axiom r029)) Eq.refl Eq.refl

step2 : SWAP01 • SWAP02 • CX02 • SWAP02 • SWAP01 ≈ SWAP01 • SWAP02 • CX02 • SWAP01 • SWAP12 • SWAP01 • SWAP01
step2 = by-assoc-and (under (SWAP01 • SWAP02 • CX02) (SWAP01) (symmetry_SWAP02.proved)) Eq.refl Eq.refl

step3 : SWAP01 • SWAP02 • CX02 • SWAP01 • SWAP12 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • SWAP12 • SWAP01 • CX02 • SWAP01 • SWAP12 • SWAP01 • SWAP01
step3 = by-assoc-and (under (SWAP01) (CX02 • SWAP01 • SWAP12 • SWAP01 • SWAP01) (symmetry_SWAP02.proved)) Eq.refl Eq.refl

step4 : SWAP01 • SWAP01 • SWAP12 • SWAP01 • CX02 • SWAP01 • SWAP12 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • SWAP12 • SWAP01 • CX02 • SWAP01 • SWAP12
step4 = by-assoc-and (under (SWAP01 • SWAP01 • SWAP12 • SWAP01 • CX02 • SWAP01 • SWAP12) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

step5 : SWAP01 • SWAP01 • SWAP12 • SWAP01 • CX02 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • CX02 • SWAP01 • SWAP12
step5 = by-assoc-and (under (ε) (SWAP12 • SWAP01 • CX02 • SWAP01 • SWAP12) (elim_SWAP01.proved)) Eq.refl Eq.refl

step6 : SWAP12 • SWAP01 • CX02 • SWAP01 • SWAP12 ≈ SWAP12 • CX12 • SWAP12
step6 = by-assoc-and (under (SWAP12) (SWAP12) (sym (axiom r030))) Eq.refl Eq.refl

proved : CX21 ≈ SWAP12 • CX12 • SWAP12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
