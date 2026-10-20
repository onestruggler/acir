{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel182 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CZ01 ; CZ02 ; SWAP12 ; Z1 ; Z2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r018 ; r033 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel21 as drel21
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_Z_c as symmetry_Z_c

step0 : Z2 • CCX01 ≈ Z2 • SWAP12 • CCX02 • SWAP12
step0 = by-assoc-and (under (Z2) (ε) (axiom r033)) Eq.refl Eq.refl

step1 : Z2 • SWAP12 • CCX02 • SWAP12 ≈ SWAP12 • Z1 • SWAP12 • SWAP12 • CCX02 • SWAP12
step1 = by-assoc-and (under (ε) (SWAP12 • CCX02 • SWAP12) (symmetry_Z_c.proved)) Eq.refl Eq.refl

step2 : SWAP12 • Z1 • SWAP12 • SWAP12 • CCX02 • SWAP12 ≈ SWAP12 • Z1 • CCX02 • SWAP12
step2 = by-assoc-and (under (SWAP12 • Z1) (CCX02 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

step3 : SWAP12 • Z1 • CCX02 • SWAP12 ≈ SWAP12 • CCX02 • CZ02 • Z1 • SWAP12
step3 = by-assoc-and (under (SWAP12) (SWAP12) (drel21.proved)) Eq.refl Eq.refl

step4 : SWAP12 • CCX02 • CZ02 • Z1 • SWAP12 ≈ SWAP12 • CCX02 • CZ02 • SWAP12 • SWAP12 • Z1 • SWAP12
step4 = by-assoc-and (under (SWAP12 • CCX02 • CZ02) (Z1 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step5 : SWAP12 • CCX02 • CZ02 • SWAP12 • SWAP12 • Z1 • SWAP12 ≈ SWAP12 • CCX02 • CZ02 • SWAP12 • Z2
step5 = by-assoc-and (under (SWAP12 • CCX02 • CZ02 • SWAP12) (ε) (sym (symmetry_Z_c.proved))) Eq.refl Eq.refl

step6 : SWAP12 • CCX02 • CZ02 • SWAP12 • Z2 ≈ SWAP12 • CCX02 • SWAP12 • CZ01 • SWAP12 • SWAP12 • Z2
step6 = by-assoc-and (under (SWAP12 • CCX02) (SWAP12 • Z2) (axiom r018)) Eq.refl Eq.refl

step7 : SWAP12 • CCX02 • SWAP12 • CZ01 • SWAP12 • SWAP12 • Z2 ≈ SWAP12 • CCX02 • SWAP12 • CZ01 • Z2
step7 = by-assoc-and (under (SWAP12 • CCX02 • SWAP12 • CZ01) (Z2) (elim_SWAP12.proved)) Eq.refl Eq.refl

step8 : SWAP12 • CCX02 • SWAP12 • CZ01 • Z2 ≈ CCX01 • CZ01 • Z2
step8 = by-assoc-and (under (ε) (CZ01 • Z2) (sym (axiom r033))) Eq.refl Eq.refl

proved : Z2 • CCX01 ≈ CCX01 • CZ01 • Z2
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))
