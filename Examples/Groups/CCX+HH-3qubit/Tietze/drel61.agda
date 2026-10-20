{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel61 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX02 ; SWAP12 ; X1 ; X2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r009 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel82 as drel82
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_X_c as symmetry_X_c

step0 : CX02 • X2 ≈ CX02 • SWAP12 • X1 • SWAP12
step0 = by-assoc-and (under (CX02) (ε) (symmetry_X_c.proved)) Eq.refl Eq.refl

step1 : CX02 • SWAP12 • X1 • SWAP12 ≈ SWAP12 • CX01 • SWAP12 • SWAP12 • X1 • SWAP12
step1 = by-assoc-and (under (ε) (SWAP12 • X1 • SWAP12) (axiom r009)) Eq.refl Eq.refl

step2 : SWAP12 • CX01 • SWAP12 • SWAP12 • X1 • SWAP12 ≈ SWAP12 • CX01 • X1 • SWAP12
step2 = by-assoc-and (under (SWAP12 • CX01) (X1 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

step3 : SWAP12 • CX01 • X1 • SWAP12 ≈ SWAP12 • X1 • CX01 • SWAP12
step3 = by-assoc-and (under (SWAP12) (SWAP12) (sym (drel82.proved))) Eq.refl Eq.refl

step4 : SWAP12 • X1 • CX01 • SWAP12 ≈ SWAP12 • X1 • SWAP12 • SWAP12 • CX01 • SWAP12
step4 = by-assoc-and (under (SWAP12 • X1) (CX01 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step5 : SWAP12 • X1 • SWAP12 • SWAP12 • CX01 • SWAP12 ≈ SWAP12 • X1 • SWAP12 • CX02
step5 = by-assoc-and (under (SWAP12 • X1 • SWAP12) (ε) (sym (axiom r009))) Eq.refl Eq.refl

step6 : SWAP12 • X1 • SWAP12 • CX02 ≈ X2 • CX02
step6 = by-assoc-and (under (ε) (CX02) (sym (symmetry_X_c.proved))) Eq.refl Eq.refl

proved : CX02 • X2 ≈ X2 • CX02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
