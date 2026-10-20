{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel81 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX02 ; SWAP12 ; Z0 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r009 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_SWAP_a as bifunct_Z_SWAP_a
import Examples.Groups.CCX+HH-3qubit.Tietze.drel78 as drel78

step0 : CX02 • Z0 ≈ SWAP12 • CX01 • SWAP12 • Z0
step0 = by-assoc-and (under (ε) (Z0) (axiom r009)) Eq.refl Eq.refl

step1 : SWAP12 • CX01 • SWAP12 • Z0 ≈ SWAP12 • CX01 • Z0 • SWAP12
step1 = by-assoc-and (under (SWAP12 • CX01) (ε) (sym (bifunct_Z_SWAP_a.proved))) Eq.refl Eq.refl

step2 : SWAP12 • CX01 • Z0 • SWAP12 ≈ SWAP12 • Z0 • CX01 • SWAP12
step2 = by-assoc-and (under (SWAP12) (SWAP12) (drel78.proved)) Eq.refl Eq.refl

step3 : SWAP12 • Z0 • CX01 • SWAP12 ≈ Z0 • SWAP12 • CX01 • SWAP12
step3 = by-assoc-and (under (ε) (CX01 • SWAP12) (sym (bifunct_Z_SWAP_a.proved))) Eq.refl Eq.refl

step4 : Z0 • SWAP12 • CX01 • SWAP12 ≈ Z0 • CX02
step4 = by-assoc-and (under (Z0) (ε) (sym (axiom r009))) Eq.refl Eq.refl

proved : CX02 • Z0 ≈ Z0 • CX02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
