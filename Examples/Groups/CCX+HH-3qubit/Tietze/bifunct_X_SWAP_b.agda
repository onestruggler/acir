{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_SWAP_b where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX10 ; SWAP01 ; X2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r013 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_CX_c as bifunct_X_CX_c
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_CX_d as bifunct_X_CX_d

step0 : X2 • SWAP01 ≈ X2 • CX01 • CX10 • CX01
step0 = by-assoc-and (under (X2) (ε) (axiom r013)) Eq.refl Eq.refl

step1 : X2 • CX01 • CX10 • CX01 ≈ CX01 • X2 • CX10 • CX01
step1 = by-assoc-and (under (ε) (CX10 • CX01) (sym (bifunct_X_CX_d.proved))) Eq.refl Eq.refl

step2 : CX01 • X2 • CX10 • CX01 ≈ CX01 • CX10 • X2 • CX01
step2 = by-assoc-and (under (CX01) (CX01) (sym (bifunct_X_CX_c.proved))) Eq.refl Eq.refl

step3 : CX01 • CX10 • X2 • CX01 ≈ CX01 • CX10 • CX01 • X2
step3 = by-assoc-and (under (CX01 • CX10) (ε) (sym (bifunct_X_CX_d.proved))) Eq.refl Eq.refl

step4 : CX01 • CX10 • CX01 • X2 ≈ SWAP01 • X2
step4 = by-assoc-and (under (ε) (X2) (sym (axiom r013))) Eq.refl Eq.refl

proved : X2 • SWAP01 ≈ SWAP01 • X2
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
