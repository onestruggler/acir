{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX02 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX02 ; SWAP12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r009 ; r022 ; refl ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12

step0 : CX02 • CX02 ≈ CX02 • SWAP12 • CX01 • SWAP12
step0 = by-assoc-and (under (CX02) (ε) (axiom r009)) Eq.refl Eq.refl

step1 : CX02 • SWAP12 • CX01 • SWAP12 ≈ SWAP12 • CX01 • SWAP12 • SWAP12 • CX01 • SWAP12
step1 = by-assoc-and (under (ε) (SWAP12 • CX01 • SWAP12) (axiom r009)) Eq.refl Eq.refl

step2 : SWAP12 • CX01 • SWAP12 • SWAP12 • CX01 • SWAP12 ≈ SWAP12 • CX01 • CX01 • SWAP12
step2 = by-assoc-and (under (SWAP12 • CX01) (CX01 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

step3 : SWAP12 • CX01 • CX01 • SWAP12 ≈ SWAP12 • SWAP12
step3 = by-assoc-and (under (SWAP12) (SWAP12) (axiom r022)) Eq.refl Eq.refl

step4 : SWAP12 • SWAP12 ≈ ε
step4 = by-assoc-and (under (ε) (ε) (elim_SWAP12.proved)) Eq.refl Eq.refl

proved : CX02 • CX02 ≈ ε
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
