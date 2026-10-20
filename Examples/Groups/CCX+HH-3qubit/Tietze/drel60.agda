{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel60 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CZ02 ; CZ12 ; SWAP01 ; Z2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r019 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_SWAP_c as bifunct_Z_SWAP_c
import Examples.Groups.CCX+HH-3qubit.Tietze.drel62 as drel62

step0 : CZ12 • Z2 ≈ SWAP01 • CZ02 • SWAP01 • Z2
step0 = by-assoc-and (under (ε) (Z2) (axiom r019)) Eq.refl Eq.refl

step1 : SWAP01 • CZ02 • SWAP01 • Z2 ≈ SWAP01 • CZ02 • Z2 • SWAP01
step1 = by-assoc-and (under (SWAP01 • CZ02) (ε) (sym (bifunct_Z_SWAP_c.proved))) Eq.refl Eq.refl

step2 : SWAP01 • CZ02 • Z2 • SWAP01 ≈ SWAP01 • Z2 • CZ02 • SWAP01
step2 = by-assoc-and (under (SWAP01) (SWAP01) (drel62.proved)) Eq.refl Eq.refl

step3 : SWAP01 • Z2 • CZ02 • SWAP01 ≈ Z2 • SWAP01 • CZ02 • SWAP01
step3 = by-assoc-and (under (ε) (CZ02 • SWAP01) (sym (bifunct_Z_SWAP_c.proved))) Eq.refl Eq.refl

step4 : Z2 • SWAP01 • CZ02 • SWAP01 ≈ Z2 • CZ12
step4 = by-assoc-and (under (Z2) (ε) (sym (axiom r019))) Eq.refl Eq.refl

proved : CZ12 • Z2 ≈ Z2 • CZ12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
