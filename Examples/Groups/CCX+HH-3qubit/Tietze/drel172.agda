{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel172 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX02 ; CZ01 ; CZ02 ; CZ12 ; SWAP12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r009 ; r018 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel109 as drel109
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CZ_e as symmetry_CZ_e

step0 : CZ12 • CX02 ≈ CZ12 • SWAP12 • CX01 • SWAP12
step0 = by-assoc-and (under (CZ12) (ε) (axiom r009)) Eq.refl Eq.refl

step1 : CZ12 • SWAP12 • CX01 • SWAP12 ≈ SWAP12 • CZ12 • SWAP12 • SWAP12 • CX01 • SWAP12
step1 = by-assoc-and (under (ε) (SWAP12 • CX01 • SWAP12) (symmetry_CZ_e.proved)) Eq.refl Eq.refl

step2 : SWAP12 • CZ12 • SWAP12 • SWAP12 • CX01 • SWAP12 ≈ SWAP12 • CZ12 • CX01 • SWAP12
step2 = by-assoc-and (under (SWAP12 • CZ12) (CX01 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

step3 : SWAP12 • CZ12 • CX01 • SWAP12 ≈ SWAP12 • CX01 • CZ02 • CZ12 • SWAP12
step3 = by-assoc-and (under (SWAP12) (SWAP12) (drel109.proved)) Eq.refl Eq.refl

step4 : SWAP12 • CX01 • CZ02 • CZ12 • SWAP12 ≈ SWAP12 • CX01 • SWAP12 • CZ01 • SWAP12 • CZ12 • SWAP12
step4 = by-assoc-and (under (SWAP12 • CX01) (CZ12 • SWAP12) (axiom r018)) Eq.refl Eq.refl

step5 : SWAP12 • CX01 • SWAP12 • CZ01 • SWAP12 • CZ12 • SWAP12 ≈ SWAP12 • CX01 • SWAP12 • CZ01 • CZ12
step5 = by-assoc-and (under (SWAP12 • CX01 • SWAP12 • CZ01) (ε) (sym (symmetry_CZ_e.proved))) Eq.refl Eq.refl

step6 : SWAP12 • CX01 • SWAP12 • CZ01 • CZ12 ≈ CX02 • CZ01 • CZ12
step6 = by-assoc-and (under (ε) (CZ01 • CZ12) (sym (axiom r009))) Eq.refl Eq.refl

proved : CZ12 • CX02 ≈ CX02 • CZ01 • CZ12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
