{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel146 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CZ02 ; SWAP02 ; X0 ; X2 ; Z0 ; Z2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r015 ; r016 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel156 as drel156
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CZ_a as symmetry_CZ_a

step0 : X2 • CZ02 ≈ X2 • SWAP02 • CZ02 • SWAP02
step0 = by-assoc-and (under (X2) (ε) (symmetry_CZ_a.proved)) Eq.refl Eq.refl

step1 : X2 • SWAP02 • CZ02 • SWAP02 ≈ SWAP02 • X0 • SWAP02 • SWAP02 • CZ02 • SWAP02
step1 = by-assoc-and (under (ε) (SWAP02 • CZ02 • SWAP02) (axiom r015)) Eq.refl Eq.refl

step2 : SWAP02 • X0 • SWAP02 • SWAP02 • CZ02 • SWAP02 ≈ SWAP02 • X0 • CZ02 • SWAP02
step2 = by-assoc-and (under (SWAP02 • X0) (CZ02 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

step3 : SWAP02 • X0 • CZ02 • SWAP02 ≈ SWAP02 • CZ02 • Z2 • X0 • SWAP02
step3 = by-assoc-and (under (SWAP02) (SWAP02) (drel156.proved)) Eq.refl Eq.refl

step4 : SWAP02 • CZ02 • Z2 • X0 • SWAP02 ≈ SWAP02 • CZ02 • SWAP02 • Z0 • SWAP02 • X0 • SWAP02
step4 = by-assoc-and (under (SWAP02 • CZ02) (X0 • SWAP02) (axiom r016)) Eq.refl Eq.refl

step5 : SWAP02 • CZ02 • SWAP02 • Z0 • SWAP02 • X0 • SWAP02 ≈ SWAP02 • CZ02 • SWAP02 • Z0 • X2
step5 = by-assoc-and (under (SWAP02 • CZ02 • SWAP02 • Z0) (ε) (sym (axiom r015))) Eq.refl Eq.refl

step6 : SWAP02 • CZ02 • SWAP02 • Z0 • X2 ≈ CZ02 • Z0 • X2
step6 = by-assoc-and (under (ε) (Z0 • X2) (sym (symmetry_CZ_a.proved))) Eq.refl Eq.refl

proved : X2 • CZ02 ≈ CZ02 • Z0 • X2
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
