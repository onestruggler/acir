{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel170 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CZ01 ; CZ02 ; CZ12 ; SWAP01 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r019 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel151 as drel151
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CCX_c as symmetry_CCX_c
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CZ_b as symmetry_CZ_b

step0 : CZ12 • CCX01 ≈ CZ12 • SWAP01 • CCX01 • SWAP01
step0 = by-assoc-and (under (CZ12) (ε) (symmetry_CCX_c.proved)) Eq.refl Eq.refl

step1 : CZ12 • SWAP01 • CCX01 • SWAP01 ≈ SWAP01 • CZ02 • SWAP01 • SWAP01 • CCX01 • SWAP01
step1 = by-assoc-and (under (ε) (SWAP01 • CCX01 • SWAP01) (axiom r019)) Eq.refl Eq.refl

step2 : SWAP01 • CZ02 • SWAP01 • SWAP01 • CCX01 • SWAP01 ≈ SWAP01 • CZ02 • CCX01 • SWAP01
step2 = by-assoc-and (under (SWAP01 • CZ02) (CCX01 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

step3 : SWAP01 • CZ02 • CCX01 • SWAP01 ≈ SWAP01 • CCX01 • CZ01 • CZ02 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (drel151.proved)) Eq.refl Eq.refl

step4 : SWAP01 • CCX01 • CZ01 • CZ02 • SWAP01 ≈ SWAP01 • CCX01 • SWAP01 • CZ01 • SWAP01 • CZ02 • SWAP01
step4 = by-assoc-and (under (SWAP01 • CCX01) (CZ02 • SWAP01) (symmetry_CZ_b.proved)) Eq.refl Eq.refl

step5 : SWAP01 • CCX01 • SWAP01 • CZ01 • SWAP01 • CZ02 • SWAP01 ≈ SWAP01 • CCX01 • SWAP01 • CZ01 • CZ12
step5 = by-assoc-and (under (SWAP01 • CCX01 • SWAP01 • CZ01) (ε) (sym (axiom r019))) Eq.refl Eq.refl

step6 : SWAP01 • CCX01 • SWAP01 • CZ01 • CZ12 ≈ CCX01 • CZ01 • CZ12
step6 = by-assoc-and (under (ε) (CZ01 • CZ12) (sym (symmetry_CCX_c.proved))) Eq.refl Eq.refl

proved : CZ12 • CCX01 ≈ CCX01 • CZ01 • CZ12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
