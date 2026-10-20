{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_Z_b where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (SWAP02 ; Z0 ; Z2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r016 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_Z0 as elim_Z0
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_Z2 as elim_Z2

step0 : Z0 ≈ Z0 • SWAP02 • SWAP02
step0 = by-assoc-and (under (Z0) (ε) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step1 : Z0 • SWAP02 • SWAP02 ≈ Z0 • SWAP02 • Z2 • Z2 • SWAP02
step1 = by-assoc-and (under (Z0 • SWAP02) (SWAP02) (sym (elim_Z2.proved))) Eq.refl Eq.refl

step2 : Z0 • SWAP02 • Z2 • Z2 • SWAP02 ≈ Z0 • SWAP02 • Z2 • SWAP02 • SWAP02 • Z2 • SWAP02
step2 = by-assoc-and (under (Z0 • SWAP02 • Z2) (Z2 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step3 : Z0 • SWAP02 • Z2 • SWAP02 • SWAP02 • Z2 • SWAP02 ≈ Z0 • SWAP02 • SWAP02 • Z0 • SWAP02 • SWAP02 • SWAP02 • Z2 • SWAP02
step3 = by-assoc-and (under (Z0 • SWAP02) (SWAP02 • SWAP02 • Z2 • SWAP02) (axiom r016)) Eq.refl Eq.refl

step4 : Z0 • SWAP02 • SWAP02 • Z0 • SWAP02 • SWAP02 • SWAP02 • Z2 • SWAP02 ≈ Z0 • Z0 • SWAP02 • SWAP02 • SWAP02 • Z2 • SWAP02
step4 = by-assoc-and (under (Z0) (Z0 • SWAP02 • SWAP02 • SWAP02 • Z2 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

step5 : Z0 • Z0 • SWAP02 • SWAP02 • SWAP02 • Z2 • SWAP02 ≈ SWAP02 • SWAP02 • SWAP02 • Z2 • SWAP02
step5 = by-assoc-and (under (ε) (SWAP02 • SWAP02 • SWAP02 • Z2 • SWAP02) (elim_Z0.proved)) Eq.refl Eq.refl

step6 : SWAP02 • SWAP02 • SWAP02 • Z2 • SWAP02 ≈ SWAP02 • Z2 • SWAP02
step6 = by-assoc-and (under (ε) (SWAP02 • Z2 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

proved : Z0 ≈ SWAP02 • Z2 • SWAP02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
