{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel158 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel173 as drel173
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01

step0 : CZ12 • Z1 • CX12 ≈ CZ12 • Z1 • SWAP01 • CX02 • SWAP01
step0 = by-assoc-and (under (CZ12 • Z1) (ε) (axiom r030)) Eq.refl Eq.refl

step1 : CZ12 • Z1 • SWAP01 • CX02 • SWAP01 ≈ CZ12 • SWAP01 • Z0 • SWAP01 • SWAP01 • CX02 • SWAP01
step1 = by-assoc-and (under (CZ12) (SWAP01 • CX02 • SWAP01) (axiom r034)) Eq.refl Eq.refl

step2 : CZ12 • SWAP01 • Z0 • SWAP01 • SWAP01 • CX02 • SWAP01 ≈ CZ12 • SWAP01 • Z0 • CX02 • SWAP01
step2 = by-assoc-and (under (CZ12 • SWAP01 • Z0) (CX02 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

step3 : CZ12 • SWAP01 • Z0 • CX02 • SWAP01 ≈ SWAP01 • CZ02 • SWAP01 • SWAP01 • Z0 • CX02 • SWAP01
step3 = by-assoc-and (under (ε) (SWAP01 • Z0 • CX02 • SWAP01) (axiom r019)) Eq.refl Eq.refl

step4 : SWAP01 • CZ02 • SWAP01 • SWAP01 • Z0 • CX02 • SWAP01 ≈ SWAP01 • CZ02 • Z0 • CX02 • SWAP01
step4 = by-assoc-and (under (SWAP01 • CZ02) (Z0 • CX02 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

step5 : SWAP01 • CZ02 • Z0 • CX02 • SWAP01 ≈ SWAP01 • CX02 • CZ02 • SWAP01
step5 = by-assoc-and (under (SWAP01) (SWAP01) (drel173.proved)) Eq.refl Eq.refl

step6 : SWAP01 • CX02 • CZ02 • SWAP01 ≈ SWAP01 • CX02 • SWAP01 • SWAP01 • CZ02 • SWAP01
step6 = by-assoc-and (under (SWAP01 • CX02) (CZ02 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step7 : SWAP01 • CX02 • SWAP01 • SWAP01 • CZ02 • SWAP01 ≈ SWAP01 • CX02 • SWAP01 • CZ12
step7 = by-assoc-and (under (SWAP01 • CX02 • SWAP01) (ε) (sym (axiom r019))) Eq.refl Eq.refl

step8 : SWAP01 • CX02 • SWAP01 • CZ12 ≈ CX12 • CZ12
step8 = by-assoc-and (under (ε) (CZ12) (sym (axiom r030))) Eq.refl Eq.refl

proved : CZ12 • Z1 • CX12 ≈ CX12 • CZ12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))
