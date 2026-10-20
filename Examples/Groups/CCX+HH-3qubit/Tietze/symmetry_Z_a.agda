{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_Z_a where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX02 ; CX20 ; SWAP02 ; Z1 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r010 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_CX_a as bifunct_Z_CX_a
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_CX_c as bifunct_Z_CX_c
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02

step0 : Z1 ≈ SWAP02 • SWAP02 • Z1
step0 = by-assoc-and (under (ε) (Z1) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step1 : SWAP02 • SWAP02 • Z1 ≈ SWAP02 • CX02 • CX20 • CX02 • Z1
step1 = by-assoc-and (under (SWAP02) (Z1) (axiom r010)) Eq.refl Eq.refl

step2 : SWAP02 • CX02 • CX20 • CX02 • Z1 ≈ SWAP02 • CX02 • CX20 • Z1 • CX02
step2 = by-assoc-and (under (SWAP02 • CX02 • CX20) (ε) (sym (bifunct_Z_CX_c.proved))) Eq.refl Eq.refl

step3 : SWAP02 • CX02 • CX20 • Z1 • CX02 ≈ SWAP02 • CX02 • Z1 • CX20 • CX02
step3 = by-assoc-and (under (SWAP02 • CX02) (CX02) (sym (bifunct_Z_CX_a.proved))) Eq.refl Eq.refl

step4 : SWAP02 • CX02 • Z1 • CX20 • CX02 ≈ SWAP02 • Z1 • CX02 • CX20 • CX02
step4 = by-assoc-and (under (SWAP02) (CX20 • CX02) (sym (bifunct_Z_CX_c.proved))) Eq.refl Eq.refl

step5 : SWAP02 • Z1 • CX02 • CX20 • CX02 ≈ SWAP02 • Z1 • SWAP02
step5 = by-assoc-and (under (SWAP02 • Z1) (ε) (sym (axiom r010))) Eq.refl Eq.refl

proved : Z1 ≈ SWAP02 • Z1 • SWAP02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
