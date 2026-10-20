{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CCX_f where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; SWAP01 ; SWAP02 ; SWAP12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r033 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CCX_c as symmetry_CCX_c
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_SWAP02_alt as symmetry_SWAP02_alt

step0 : CCX02 ≈ CCX02 • SWAP12 • SWAP12
step0 = by-assoc-and (under (CCX02) (ε) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step1 : CCX02 • SWAP12 • SWAP12 ≈ SWAP12 • SWAP12 • CCX02 • SWAP12 • SWAP12
step1 = by-assoc-and (under (ε) (CCX02 • SWAP12 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step2 : SWAP12 • SWAP12 • CCX02 • SWAP12 • SWAP12 ≈ SWAP12 • CCX01 • SWAP12
step2 = by-assoc-and (under (SWAP12) (SWAP12) (sym (axiom r033))) Eq.refl Eq.refl

step3 : SWAP12 • CCX01 • SWAP12 ≈ SWAP12 • SWAP01 • CCX01 • SWAP01 • SWAP12
step3 = by-assoc-and (under (SWAP12) (SWAP12) (symmetry_CCX_c.proved)) Eq.refl Eq.refl

step4 : SWAP12 • SWAP01 • CCX01 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • SWAP12 • CCX02 • SWAP12 • SWAP01 • SWAP12
step4 = by-assoc-and (under (SWAP12 • SWAP01) (SWAP01 • SWAP12) (axiom r033)) Eq.refl Eq.refl

step5 : SWAP12 • SWAP01 • SWAP12 • CCX02 • SWAP12 • SWAP01 • SWAP12 ≈ SWAP12 • SWAP01 • SWAP12 • CCX02 • SWAP02
step5 = by-assoc-and (under (SWAP12 • SWAP01 • SWAP12 • CCX02) (ε) (sym (symmetry_SWAP02_alt.proved))) Eq.refl Eq.refl

step6 : SWAP12 • SWAP01 • SWAP12 • CCX02 • SWAP02 ≈ SWAP02 • CCX02 • SWAP02
step6 = by-assoc-and (under (ε) (CCX02 • SWAP02) (sym (symmetry_SWAP02_alt.proved))) Eq.refl Eq.refl

proved : CCX02 ≈ SWAP02 • CCX02 • SWAP02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
