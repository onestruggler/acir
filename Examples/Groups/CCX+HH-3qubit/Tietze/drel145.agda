{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel145 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CZ01 ; SWAP01 ; X0 ; X1 ; Z0 ; Z1 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r028 ; r034 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel160 as drel160
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CZ_b as symmetry_CZ_b

step0 : X1 • CZ01 ≈ X1 • SWAP01 • CZ01 • SWAP01
step0 = by-assoc-and (under (X1) (ε) (symmetry_CZ_b.proved)) Eq.refl Eq.refl

step1 : X1 • SWAP01 • CZ01 • SWAP01 ≈ SWAP01 • X0 • SWAP01 • SWAP01 • CZ01 • SWAP01
step1 = by-assoc-and (under (ε) (SWAP01 • CZ01 • SWAP01) (axiom r028)) Eq.refl Eq.refl

step2 : SWAP01 • X0 • SWAP01 • SWAP01 • CZ01 • SWAP01 ≈ SWAP01 • X0 • CZ01 • SWAP01
step2 = by-assoc-and (under (SWAP01 • X0) (CZ01 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

step3 : SWAP01 • X0 • CZ01 • SWAP01 ≈ SWAP01 • CZ01 • Z1 • X0 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (drel160.proved)) Eq.refl Eq.refl

step4 : SWAP01 • CZ01 • Z1 • X0 • SWAP01 ≈ SWAP01 • CZ01 • SWAP01 • Z0 • SWAP01 • X0 • SWAP01
step4 = by-assoc-and (under (SWAP01 • CZ01) (X0 • SWAP01) (axiom r034)) Eq.refl Eq.refl

step5 : SWAP01 • CZ01 • SWAP01 • Z0 • SWAP01 • X0 • SWAP01 ≈ CZ01 • Z0 • SWAP01 • X0 • SWAP01
step5 = by-assoc-and (under (ε) (Z0 • SWAP01 • X0 • SWAP01) (sym (symmetry_CZ_b.proved))) Eq.refl Eq.refl

step6 : CZ01 • Z0 • SWAP01 • X0 • SWAP01 ≈ CZ01 • Z0 • X1
step6 = by-assoc-and (under (CZ01 • Z0) (ε) (sym (axiom r028))) Eq.refl Eq.refl

proved : X1 • CZ01 ≈ CZ01 • Z0 • X1
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
