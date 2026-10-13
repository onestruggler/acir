{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel89 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel74 as drel74
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_h as symmetry_CX_h

step0 : CZ12 • K01 ≈ SWAP01 • CZ02 • SWAP01 • K01
step0 = by-assoc-and (under (ε) (K01) (axiom r019)) Eq.refl Eq.refl

step1 : SWAP01 • CZ02 • SWAP01 • K01 ≈ SWAP01 • CZ02 • SWAP01 • SWAP01 • K01 • SWAP01
step1 = by-assoc-and (under (SWAP01 • CZ02 • SWAP01) (ε) (axiom r035)) Eq.refl Eq.refl

step2 : SWAP01 • CZ02 • SWAP01 • SWAP01 • K01 • SWAP01 ≈ SWAP01 • CZ02 • K01 • SWAP01
step2 = by-assoc-and (under (SWAP01 • CZ02) (K01 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

step3 : SWAP01 • CZ02 • K01 • SWAP01 ≈ SWAP01 • K01 • CX20 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (sym (drel74.proved))) Eq.refl Eq.refl

step4 : SWAP01 • K01 • CX20 • SWAP01 ≈ SWAP01 • SWAP01 • K01 • SWAP01 • CX20 • SWAP01
step4 = by-assoc-and (under (SWAP01) (CX20 • SWAP01) (axiom r035)) Eq.refl Eq.refl

step5 : SWAP01 • SWAP01 • K01 • SWAP01 • CX20 • SWAP01 ≈ K01 • SWAP01 • CX20 • SWAP01
step5 = by-assoc-and (under (ε) (K01 • SWAP01 • CX20 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

step6 : K01 • SWAP01 • CX20 • SWAP01 ≈ K01 • SWAP01 • SWAP01 • CX21 • SWAP01 • SWAP01
step6 = by-assoc-and (under (K01 • SWAP01) (SWAP01) (symmetry_CX_h.proved)) Eq.refl Eq.refl

step7 : K01 • SWAP01 • SWAP01 • CX21 • SWAP01 • SWAP01 ≈ K01 • SWAP01 • SWAP01 • CX21
step7 = by-assoc-and (under (K01 • SWAP01 • SWAP01 • CX21) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

step8 : K01 • SWAP01 • SWAP01 • CX21 ≈ K01 • CX21
step8 = by-assoc-and (under (K01) (CX21) (elim_SWAP01.proved)) Eq.refl Eq.refl

proved : CZ12 • K01 ≈ K01 • CX21
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))
