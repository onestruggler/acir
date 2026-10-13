{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_CZ_b where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_CX_e as bifunct_X_CX_e
import Examples.Groups.CCX+HH-3qubit.Tietze.drel137 as drel137
import Examples.Groups.CCX+HH-3qubit.Tietze.drel47 as drel47
import Examples.Groups.CCX+HH-3qubit.Tietze.drel48 as drel48
import Examples.Groups.CCX+HH-3qubit.Tietze.drel65 as drel65
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01

step0 : CZ12 • Z0 ≈ SWAP01 • CZ02 • SWAP01 • Z0
step0 = by-assoc-and (under (ε) (Z0) (axiom r019)) Eq.refl Eq.refl

step1 : SWAP01 • CZ02 • SWAP01 • Z0 ≈ SWAP01 • CZ02 • SWAP01 • Z0 • SWAP01 • SWAP01
step1 = by-assoc-and (under (SWAP01 • CZ02 • SWAP01 • Z0) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step2 : SWAP01 • CZ02 • SWAP01 • Z0 • SWAP01 • SWAP01 ≈ SWAP01 • CZ02 • Z1 • SWAP01
step2 = by-assoc-and (under (SWAP01 • CZ02) (SWAP01) (sym (axiom r034))) Eq.refl Eq.refl

step3 : SWAP01 • CZ02 • Z1 • SWAP01 ≈ SWAP01 • K12 • K12 • CZ02 • Z1 • SWAP01
step3 = by-assoc-and (under (SWAP01) (CZ02 • Z1 • SWAP01) (sym (axiom r023))) Eq.refl Eq.refl

step4 : SWAP01 • K12 • K12 • CZ02 • Z1 • SWAP01 ≈ SWAP01 • K12 • CX02 • K12 • Z1 • SWAP01
step4 = by-assoc-and (under (SWAP01 • K12) (Z1 • SWAP01) (drel47.proved)) Eq.refl Eq.refl

step5 : SWAP01 • K12 • CX02 • K12 • Z1 • SWAP01 ≈ SWAP01 • K12 • CX02 • X1 • K12 • SWAP01
step5 = by-assoc-and (under (SWAP01 • K12 • CX02) (SWAP01) (sym (drel137.proved))) Eq.refl Eq.refl

step6 : SWAP01 • K12 • CX02 • X1 • K12 • SWAP01 ≈ SWAP01 • K12 • X1 • CX02 • K12 • SWAP01
step6 = by-assoc-and (under (SWAP01 • K12) (K12 • SWAP01) (bifunct_X_CX_e.proved)) Eq.refl Eq.refl

step7 : SWAP01 • K12 • X1 • CX02 • K12 • SWAP01 ≈ SWAP01 • Z1 • K12 • CX02 • K12 • SWAP01
step7 = by-assoc-and (under (SWAP01) (CX02 • K12 • SWAP01) (drel65.proved)) Eq.refl Eq.refl

step8 : SWAP01 • Z1 • K12 • CX02 • K12 • SWAP01 ≈ SWAP01 • Z1 • CZ02 • K12 • K12 • SWAP01
step8 = by-assoc-and (under (SWAP01 • Z1) (K12 • SWAP01) (sym (drel48.proved))) Eq.refl Eq.refl

step9 : SWAP01 • Z1 • CZ02 • K12 • K12 • SWAP01 ≈ SWAP01 • Z1 • CZ02 • SWAP01
step9 = by-assoc-and (under (SWAP01 • Z1 • CZ02) (SWAP01) (axiom r023)) Eq.refl Eq.refl

step10 : SWAP01 • Z1 • CZ02 • SWAP01 ≈ SWAP01 • SWAP01 • Z0 • SWAP01 • CZ02 • SWAP01
step10 = by-assoc-and (under (SWAP01) (CZ02 • SWAP01) (axiom r034)) Eq.refl Eq.refl

step11 : SWAP01 • SWAP01 • Z0 • SWAP01 • CZ02 • SWAP01 ≈ Z0 • SWAP01 • CZ02 • SWAP01
step11 = by-assoc-and (under (ε) (Z0 • SWAP01 • CZ02 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

step12 : Z0 • SWAP01 • CZ02 • SWAP01 ≈ Z0 • CZ12
step12 = by-assoc-and (under (Z0) (ε) (sym (axiom r019))) Eq.refl Eq.refl

proved : CZ12 • Z0 ≈ Z0 • CZ12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (trans step11 (trans step12 (refl)))))))))))))
