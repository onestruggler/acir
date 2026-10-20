{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CZ_b where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CZ01 ; CZ02 ; SWAP01 ; SWAP02 ; SWAP12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r018 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CZ_a as symmetry_CZ_a
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_SWAP01_alt as symmetry_SWAP01_alt

step0 : CZ01 ≈ CZ01 • SWAP12 • SWAP12
step0 = by-assoc-and (under (CZ01) (ε) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step1 : CZ01 • SWAP12 • SWAP12 ≈ SWAP12 • SWAP12 • CZ01 • SWAP12 • SWAP12
step1 = by-assoc-and (under (ε) (CZ01 • SWAP12 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step2 : SWAP12 • SWAP12 • CZ01 • SWAP12 • SWAP12 ≈ SWAP12 • CZ02 • SWAP12
step2 = by-assoc-and (under (SWAP12) (SWAP12) (sym (axiom r018))) Eq.refl Eq.refl

step3 : SWAP12 • CZ02 • SWAP12 ≈ SWAP12 • SWAP02 • CZ02 • SWAP02 • SWAP12
step3 = by-assoc-and (under (SWAP12) (SWAP12) (symmetry_CZ_a.proved)) Eq.refl Eq.refl

step4 : SWAP12 • SWAP02 • CZ02 • SWAP02 • SWAP12 ≈ SWAP12 • SWAP02 • SWAP12 • CZ01 • SWAP12 • SWAP02 • SWAP12
step4 = by-assoc-and (under (SWAP12 • SWAP02) (SWAP02 • SWAP12) (axiom r018)) Eq.refl Eq.refl

step5 : SWAP12 • SWAP02 • SWAP12 • CZ01 • SWAP12 • SWAP02 • SWAP12 ≈ SWAP12 • SWAP02 • SWAP12 • CZ01 • SWAP01
step5 = by-assoc-and (under (SWAP12 • SWAP02 • SWAP12 • CZ01) (ε) (sym (symmetry_SWAP01_alt.proved))) Eq.refl Eq.refl

step6 : SWAP12 • SWAP02 • SWAP12 • CZ01 • SWAP01 ≈ SWAP01 • CZ01 • SWAP01
step6 = by-assoc-and (under (ε) (CZ01 • SWAP01) (sym (symmetry_SWAP01_alt.proved))) Eq.refl Eq.refl

proved : CZ01 ≈ SWAP01 • CZ01 • SWAP01
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
