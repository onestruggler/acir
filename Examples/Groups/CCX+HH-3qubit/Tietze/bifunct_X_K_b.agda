{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_K_b where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (K01 ; K12 ; SWAP02 ; X0 ; X2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r011 ; r015 ; r027 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02

step0 : X2 • K01 ≈ X2 • SWAP02 • K12 • SWAP02
step0 = by-assoc-and (under (X2) (ε) (axiom r011)) Eq.refl Eq.refl

step1 : X2 • SWAP02 • K12 • SWAP02 ≈ SWAP02 • X0 • SWAP02 • SWAP02 • K12 • SWAP02
step1 = by-assoc-and (under (ε) (SWAP02 • K12 • SWAP02) (axiom r015)) Eq.refl Eq.refl

step2 : SWAP02 • X0 • SWAP02 • SWAP02 • K12 • SWAP02 ≈ SWAP02 • X0 • K12 • SWAP02
step2 = by-assoc-and (under (SWAP02 • X0) (K12 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

step3 : SWAP02 • X0 • K12 • SWAP02 ≈ SWAP02 • K12 • X0 • SWAP02
step3 = by-assoc-and (under (SWAP02) (SWAP02) (axiom r027)) Eq.refl Eq.refl

step4 : SWAP02 • K12 • X0 • SWAP02 ≈ SWAP02 • K12 • SWAP02 • SWAP02 • X0 • SWAP02
step4 = by-assoc-and (under (SWAP02 • K12) (X0 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step5 : SWAP02 • K12 • SWAP02 • SWAP02 • X0 • SWAP02 ≈ SWAP02 • K12 • SWAP02 • X2
step5 = by-assoc-and (under (SWAP02 • K12 • SWAP02) (ε) (sym (axiom r015))) Eq.refl Eq.refl

step6 : SWAP02 • K12 • SWAP02 • X2 ≈ K01 • X2
step6 = by-assoc-and (under (ε) (X2) (sym (axiom r011))) Eq.refl Eq.refl

proved : X2 • K01 ≈ K01 • X2
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
