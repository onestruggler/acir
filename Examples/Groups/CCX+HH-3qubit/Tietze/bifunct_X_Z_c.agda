{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_Z_c where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (SWAP01 ; X2 ; Z0 ; Z1 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r034 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_SWAP_b as bifunct_X_SWAP_b
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_Z_f as bifunct_X_Z_f

step0 : X2 • Z1 ≈ X2 • SWAP01 • Z0 • SWAP01
step0 = by-assoc-and (under (X2) (ε) (axiom r034)) Eq.refl Eq.refl

step1 : X2 • SWAP01 • Z0 • SWAP01 ≈ SWAP01 • X2 • Z0 • SWAP01
step1 = by-assoc-and (under (ε) (Z0 • SWAP01) (bifunct_X_SWAP_b.proved)) Eq.refl Eq.refl

step2 : SWAP01 • X2 • Z0 • SWAP01 ≈ SWAP01 • Z0 • X2 • SWAP01
step2 = by-assoc-and (under (SWAP01) (SWAP01) (bifunct_X_Z_f.proved)) Eq.refl Eq.refl

step3 : SWAP01 • Z0 • X2 • SWAP01 ≈ SWAP01 • Z0 • SWAP01 • X2
step3 = by-assoc-and (under (SWAP01 • Z0) (ε) (bifunct_X_SWAP_b.proved)) Eq.refl Eq.refl

step4 : SWAP01 • Z0 • SWAP01 • X2 ≈ Z1 • X2
step4 = by-assoc-and (under (ε) (X2) (sym (axiom r034))) Eq.refl Eq.refl

proved : X2 • Z1 ≈ Z1 • X2
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
