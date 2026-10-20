{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CZ_a where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CZ02 ; CZ12 ; SWAP01 ; SWAP02 ; SWAP12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r019 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CZ_e as symmetry_CZ_e
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_SWAP02 as symmetry_SWAP02

step0 : CZ02 ≈ CZ02 • SWAP01 • SWAP01
step0 = by-assoc-and (under (CZ02) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step1 : CZ02 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • CZ02 • SWAP01 • SWAP01
step1 = by-assoc-and (under (ε) (CZ02 • SWAP01 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step2 : SWAP01 • SWAP01 • CZ02 • SWAP01 • SWAP01 ≈ SWAP01 • CZ12 • SWAP01
step2 = by-assoc-and (under (SWAP01) (SWAP01) (sym (axiom r019))) Eq.refl Eq.refl

step3 : SWAP01 • CZ12 • SWAP01 ≈ SWAP01 • SWAP12 • CZ12 • SWAP12 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (symmetry_CZ_e.proved)) Eq.refl Eq.refl

step4 : SWAP01 • SWAP12 • CZ12 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • SWAP01 • CZ02 • SWAP01 • SWAP12 • SWAP01
step4 = by-assoc-and (under (SWAP01 • SWAP12) (SWAP12 • SWAP01) (axiom r019)) Eq.refl Eq.refl

step5 : SWAP01 • SWAP12 • SWAP01 • CZ02 • SWAP01 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • SWAP01 • CZ02 • SWAP02
step5 = by-assoc-and (under (SWAP01 • SWAP12 • SWAP01 • CZ02) (ε) (sym (symmetry_SWAP02.proved))) Eq.refl Eq.refl

step6 : SWAP01 • SWAP12 • SWAP01 • CZ02 • SWAP02 ≈ SWAP02 • CZ02 • SWAP02
step6 = by-assoc-and (under (ε) (CZ02 • SWAP02) (sym (symmetry_SWAP02.proved))) Eq.refl Eq.refl

proved : CZ02 ≈ SWAP02 • CZ02 • SWAP02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
