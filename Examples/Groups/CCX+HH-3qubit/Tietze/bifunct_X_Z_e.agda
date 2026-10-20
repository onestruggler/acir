{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_Z_e where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (SWAP02 ; X0 ; X2 ; Z0 ; Z2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r015 ; r016 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_Z_f as bifunct_X_Z_f
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02

step0 : X0 • Z2 ≈ X0 • SWAP02 • Z0 • SWAP02
step0 = by-assoc-and (under (X0) (ε) (axiom r016)) Eq.refl Eq.refl

step1 : X0 • SWAP02 • Z0 • SWAP02 ≈ SWAP02 • SWAP02 • X0 • SWAP02 • Z0 • SWAP02
step1 = by-assoc-and (under (ε) (X0 • SWAP02 • Z0 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step2 : SWAP02 • SWAP02 • X0 • SWAP02 • Z0 • SWAP02 ≈ SWAP02 • X2 • Z0 • SWAP02
step2 = by-assoc-and (under (SWAP02) (Z0 • SWAP02) (sym (axiom r015))) Eq.refl Eq.refl

step3 : SWAP02 • X2 • Z0 • SWAP02 ≈ SWAP02 • Z0 • X2 • SWAP02
step3 = by-assoc-and (under (SWAP02) (SWAP02) (bifunct_X_Z_f.proved)) Eq.refl Eq.refl

step4 : SWAP02 • Z0 • X2 • SWAP02 ≈ SWAP02 • Z0 • SWAP02 • X0 • SWAP02 • SWAP02
step4 = by-assoc-and (under (SWAP02 • Z0) (SWAP02) (axiom r015)) Eq.refl Eq.refl

step5 : SWAP02 • Z0 • SWAP02 • X0 • SWAP02 • SWAP02 ≈ Z2 • X0 • SWAP02 • SWAP02
step5 = by-assoc-and (under (ε) (X0 • SWAP02 • SWAP02) (sym (axiom r016))) Eq.refl Eq.refl

step6 : Z2 • X0 • SWAP02 • SWAP02 ≈ Z2 • X0
step6 = by-assoc-and (under (Z2 • X0) (ε) (elim_SWAP02.proved)) Eq.refl Eq.refl

proved : X0 • Z2 ≈ Z2 • X0
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
