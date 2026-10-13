{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX12_lemma where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01

step0 : K12 • X0 • CCX02 • X0 • CCX02 • K12 ≈ K12 • X0 • CCX02 • X0 • SWAP01 • CCX12 • SWAP01 • K12
step0 = by-assoc-and (under (K12 • X0 • CCX02 • X0) (K12) (axiom r014)) Eq.refl Eq.refl

step1 : K12 • X0 • CCX02 • X0 • SWAP01 • CCX12 • SWAP01 • K12 ≈ K12 • X0 • SWAP01 • CCX12 • SWAP01 • X0 • SWAP01 • CCX12 • SWAP01 • K12
step1 = by-assoc-and (under (K12 • X0) (X0 • SWAP01 • CCX12 • SWAP01 • K12) (axiom r014)) Eq.refl Eq.refl

step2 : K12 • X0 • SWAP01 • CCX12 • SWAP01 • X0 • SWAP01 • CCX12 • SWAP01 • K12 ≈ K12 • X0 • SWAP01 • CCX12 • X1 • CCX12 • SWAP01 • K12
step2 = by-assoc-and (under (K12 • X0 • SWAP01 • CCX12) (CCX12 • SWAP01 • K12) (sym (axiom r028))) Eq.refl Eq.refl

step3 : K12 • X0 • SWAP01 • CCX12 • X1 • CCX12 • SWAP01 • K12 ≈ K12 • SWAP01 • SWAP01 • X0 • SWAP01 • CCX12 • X1 • CCX12 • SWAP01 • K12
step3 = by-assoc-and (under (K12) (X0 • SWAP01 • CCX12 • X1 • CCX12 • SWAP01 • K12) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step4 : K12 • SWAP01 • SWAP01 • X0 • SWAP01 • CCX12 • X1 • CCX12 • SWAP01 • K12 ≈ K12 • SWAP01 • X1 • CCX12 • X1 • CCX12 • SWAP01 • K12
step4 = by-assoc-and (under (K12 • SWAP01) (CCX12 • X1 • CCX12 • SWAP01 • K12) (sym (axiom r028))) Eq.refl Eq.refl

step5 : K12 • SWAP01 • X1 • CCX12 • X1 • CCX12 • SWAP01 • K12 ≈ K12 • SWAP01 • CX20 • SWAP01 • K12
step5 = by-assoc-and (under (K12 • SWAP01) (SWAP01 • K12) (sym (axiom r005))) Eq.refl Eq.refl

step6 : K12 • SWAP01 • CX20 • SWAP01 • K12 ≈ K12 • CX21 • K12
step6 = by-assoc-and (under (K12) (K12) (sym (axiom r031))) Eq.refl Eq.refl

step7 : K12 • CX21 • K12 ≈ CX12
step7 = by-assoc-and (under (ε) (ε) (sym (axiom r007))) Eq.refl Eq.refl

proved : K12 • X0 • CCX02 • X0 • CCX02 • K12 ≈ CX12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (refl))))))))
