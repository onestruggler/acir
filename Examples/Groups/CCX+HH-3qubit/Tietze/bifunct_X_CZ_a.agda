{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_CZ_a where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CZ01 ; CZ02 ; K12 ; SWAP12 ; X1 ; X2 ; Z2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r001 ; r018 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_CX_e as bifunct_Z_CX_e
import Examples.Groups.CCX+HH-3qubit.Tietze.drel64 as drel64
import Examples.Groups.CCX+HH-3qubit.Tietze.drel66 as drel66
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_X_c as symmetry_X_c

step0 : X1 • CZ02 ≈ X1 • SWAP12 • CZ01 • SWAP12
step0 = by-assoc-and (under (X1) (ε) (axiom r018)) Eq.refl Eq.refl

step1 : X1 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • SWAP12 • X1 • SWAP12 • CZ01 • SWAP12
step1 = by-assoc-and (under (ε) (X1 • SWAP12 • CZ01 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step2 : SWAP12 • SWAP12 • X1 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • X2 • CZ01 • SWAP12
step2 = by-assoc-and (under (SWAP12) (CZ01 • SWAP12) (sym (symmetry_X_c.proved))) Eq.refl Eq.refl

step3 : SWAP12 • X2 • CZ01 • SWAP12 ≈ SWAP12 • X2 • K12 • CX01 • K12 • SWAP12
step3 = by-assoc-and (under (SWAP12 • X2) (SWAP12) (axiom r001)) Eq.refl Eq.refl

step4 : SWAP12 • X2 • K12 • CX01 • K12 • SWAP12 ≈ SWAP12 • K12 • Z2 • CX01 • K12 • SWAP12
step4 = by-assoc-and (under (SWAP12) (CX01 • K12 • SWAP12) (drel64.proved)) Eq.refl Eq.refl

step5 : SWAP12 • K12 • Z2 • CX01 • K12 • SWAP12 ≈ SWAP12 • K12 • CX01 • Z2 • K12 • SWAP12
step5 = by-assoc-and (under (SWAP12 • K12) (K12 • SWAP12) (bifunct_Z_CX_e.proved)) Eq.refl Eq.refl

step6 : SWAP12 • K12 • CX01 • Z2 • K12 • SWAP12 ≈ SWAP12 • K12 • CX01 • K12 • X2 • SWAP12
step6 = by-assoc-and (under (SWAP12 • K12 • CX01) (SWAP12) (sym (drel66.proved))) Eq.refl Eq.refl

step7 : SWAP12 • K12 • CX01 • K12 • X2 • SWAP12 ≈ SWAP12 • K12 • CX01 • K12 • SWAP12 • X1 • SWAP12 • SWAP12
step7 = by-assoc-and (under (SWAP12 • K12 • CX01 • K12) (SWAP12) (symmetry_X_c.proved)) Eq.refl Eq.refl

step8 : SWAP12 • K12 • CX01 • K12 • SWAP12 • X1 • SWAP12 • SWAP12 ≈ SWAP12 • K12 • CX01 • K12 • SWAP12 • X1
step8 = by-assoc-and (under (SWAP12 • K12 • CX01 • K12 • SWAP12 • X1) (ε) (elim_SWAP12.proved)) Eq.refl Eq.refl

step9 : SWAP12 • K12 • CX01 • K12 • SWAP12 • X1 ≈ SWAP12 • CZ01 • SWAP12 • X1
step9 = by-assoc-and (under (SWAP12) (SWAP12 • X1) (sym (axiom r001))) Eq.refl Eq.refl

step10 : SWAP12 • CZ01 • SWAP12 • X1 ≈ CZ02 • X1
step10 = by-assoc-and (under (ε) (X1) (sym (axiom r018))) Eq.refl Eq.refl

proved : X1 • CZ02 ≈ CZ02 • X1
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (refl)))))))))))
