{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_CZ_b where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CZ02 ; CZ12 ; SWAP01 ; X0 ; X1 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r019 ; r028 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_CZ_a as bifunct_X_CZ_a
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01

step0 : X0 • CZ12 ≈ X0 • SWAP01 • CZ02 • SWAP01
step0 = by-assoc-and (under (X0) (ε) (axiom r019)) Eq.refl Eq.refl

step1 : X0 • SWAP01 • CZ02 • SWAP01 ≈ SWAP01 • SWAP01 • X0 • SWAP01 • CZ02 • SWAP01
step1 = by-assoc-and (under (ε) (X0 • SWAP01 • CZ02 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step2 : SWAP01 • SWAP01 • X0 • SWAP01 • CZ02 • SWAP01 ≈ SWAP01 • X1 • CZ02 • SWAP01
step2 = by-assoc-and (under (SWAP01) (CZ02 • SWAP01) (sym (axiom r028))) Eq.refl Eq.refl

step3 : SWAP01 • X1 • CZ02 • SWAP01 ≈ SWAP01 • CZ02 • X1 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (bifunct_X_CZ_a.proved)) Eq.refl Eq.refl

step4 : SWAP01 • CZ02 • X1 • SWAP01 ≈ SWAP01 • CZ02 • SWAP01 • X0 • SWAP01 • SWAP01
step4 = by-assoc-and (under (SWAP01 • CZ02) (SWAP01) (axiom r028)) Eq.refl Eq.refl

step5 : SWAP01 • CZ02 • SWAP01 • X0 • SWAP01 • SWAP01 ≈ SWAP01 • CZ02 • SWAP01 • X0
step5 = by-assoc-and (under (SWAP01 • CZ02 • SWAP01 • X0) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

step6 : SWAP01 • CZ02 • SWAP01 • X0 ≈ CZ12 • X0
step6 = by-assoc-and (under (ε) (X0) (sym (axiom r019))) Eq.refl Eq.refl

proved : X0 • CZ12 ≈ CZ12 • X0
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
