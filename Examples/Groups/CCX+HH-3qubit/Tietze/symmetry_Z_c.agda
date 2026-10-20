{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_Z_c where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (K12 ; SWAP12 ; X1 ; X2 ; Z1 ; Z2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r023 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel137 as drel137
import Examples.Groups.CCX+HH-3qubit.Tietze.drel64 as drel64
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_K_a as symmetry_K_a
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_X_c as symmetry_X_c

step0 : Z2 ≈ K12 • K12 • Z2
step0 = by-assoc-and (under (ε) (Z2) (sym (axiom r023))) Eq.refl Eq.refl

step1 : K12 • K12 • Z2 ≈ K12 • X2 • K12
step1 = by-assoc-and (under (K12) (ε) (sym (drel64.proved))) Eq.refl Eq.refl

step2 : K12 • X2 • K12 ≈ K12 • SWAP12 • X1 • SWAP12 • K12
step2 = by-assoc-and (under (K12) (K12) (symmetry_X_c.proved)) Eq.refl Eq.refl

step3 : K12 • SWAP12 • X1 • SWAP12 • K12 ≈ K12 • SWAP12 • X1 • SWAP12 • SWAP12 • K12 • SWAP12
step3 = by-assoc-and (under (K12 • SWAP12 • X1 • SWAP12) (ε) (symmetry_K_a.proved)) Eq.refl Eq.refl

step4 : K12 • SWAP12 • X1 • SWAP12 • SWAP12 • K12 • SWAP12 ≈ K12 • SWAP12 • X1 • K12 • SWAP12
step4 = by-assoc-and (under (K12 • SWAP12 • X1) (K12 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

step5 : K12 • SWAP12 • X1 • K12 • SWAP12 ≈ SWAP12 • K12 • SWAP12 • SWAP12 • X1 • K12 • SWAP12
step5 = by-assoc-and (under (ε) (SWAP12 • X1 • K12 • SWAP12) (symmetry_K_a.proved)) Eq.refl Eq.refl

step6 : SWAP12 • K12 • SWAP12 • SWAP12 • X1 • K12 • SWAP12 ≈ SWAP12 • K12 • X1 • K12 • SWAP12
step6 = by-assoc-and (under (SWAP12 • K12) (X1 • K12 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

step7 : SWAP12 • K12 • X1 • K12 • SWAP12 ≈ SWAP12 • K12 • K12 • Z1 • SWAP12
step7 = by-assoc-and (under (SWAP12 • K12) (SWAP12) (drel137.proved)) Eq.refl Eq.refl

step8 : SWAP12 • K12 • K12 • Z1 • SWAP12 ≈ SWAP12 • Z1 • SWAP12
step8 = by-assoc-and (under (SWAP12) (Z1 • SWAP12) (axiom r023)) Eq.refl Eq.refl

proved : Z2 ≈ SWAP12 • Z1 • SWAP12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))
