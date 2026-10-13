{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel58 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01

step0 : Z1 • K01 ≈ SWAP01 • Z0 • SWAP01 • K01
step0 = by-assoc-and (under (ε) (K01) (axiom r034)) Eq.refl Eq.refl

step1 : SWAP01 • Z0 • SWAP01 • K01 ≈ SWAP01 • Z0 • SWAP01 • SWAP01 • K01 • SWAP01
step1 = by-assoc-and (under (SWAP01 • Z0 • SWAP01) (ε) (axiom r035)) Eq.refl Eq.refl

step2 : SWAP01 • Z0 • SWAP01 • SWAP01 • K01 • SWAP01 ≈ SWAP01 • Z0 • K01 • SWAP01
step2 = by-assoc-and (under (SWAP01 • Z0) (K01 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

step3 : SWAP01 • Z0 • K01 • SWAP01 ≈ SWAP01 • K01 • K01 • Z0 • K01 • SWAP01
step3 = by-assoc-and (under (SWAP01) (Z0 • K01 • SWAP01) (sym (axiom r025))) Eq.refl Eq.refl

step4 : SWAP01 • K01 • K01 • Z0 • K01 • SWAP01 ≈ SWAP01 • K01 • X0 • K01 • K01 • SWAP01
step4 = by-assoc-and (under (SWAP01 • K01) (K01 • SWAP01) (axiom r041)) Eq.refl Eq.refl

step5 : SWAP01 • K01 • X0 • K01 • K01 • SWAP01 ≈ SWAP01 • K01 • X0 • SWAP01
step5 = by-assoc-and (under (SWAP01 • K01 • X0) (SWAP01) (axiom r025)) Eq.refl Eq.refl

step6 : SWAP01 • K01 • X0 • SWAP01 ≈ SWAP01 • SWAP01 • K01 • SWAP01 • X0 • SWAP01
step6 = by-assoc-and (under (SWAP01) (X0 • SWAP01) (axiom r035)) Eq.refl Eq.refl

step7 : SWAP01 • SWAP01 • K01 • SWAP01 • X0 • SWAP01 ≈ K01 • SWAP01 • X0 • SWAP01
step7 = by-assoc-and (under (ε) (K01 • SWAP01 • X0 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

step8 : K01 • SWAP01 • X0 • SWAP01 ≈ K01 • X1
step8 = by-assoc-and (under (K01) (ε) (sym (axiom r028))) Eq.refl Eq.refl

proved : Z1 • K01 ≈ K01 • X1
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))
