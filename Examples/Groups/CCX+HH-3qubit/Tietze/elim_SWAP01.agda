{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX10 as elim_CX10

step0 : SWAP01 • SWAP01 ≈ SWAP01 • CX01 • CX10 • CX01
step0 = by-assoc-and (under (SWAP01) (ε) (axiom r013)) Eq.refl Eq.refl

step1 : SWAP01 • CX01 • CX10 • CX01 ≈ CX01 • CX10 • CX01 • CX01 • CX10 • CX01
step1 = by-assoc-and (under (ε) (CX01 • CX10 • CX01) (axiom r013)) Eq.refl Eq.refl

step2 : CX01 • CX10 • CX01 • CX01 • CX10 • CX01 ≈ CX01 • CX10 • CX10 • CX01
step2 = by-assoc-and (under (CX01 • CX10) (CX10 • CX01) (axiom r022)) Eq.refl Eq.refl

step3 : CX01 • CX10 • CX10 • CX01 ≈ CX01 • CX01
step3 = by-assoc-and (under (CX01) (CX01) (elim_CX10.proved)) Eq.refl Eq.refl

step4 : CX01 • CX01 ≈ ε
step4 = by-assoc-and (under (ε) (ε) (axiom r022)) Eq.refl Eq.refl

proved : SWAP01 • SWAP01 ≈ ε
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
