{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_h where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX02 ; CX12 ; CX20 ; CX21 ; SWAP01 ; SWAP02 ; SWAP12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r029 ; r030 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_g as symmetry_CX_g
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_SWAP02 as symmetry_SWAP02

step0 : CX20 ≈ SWAP02 • CX02 • SWAP02
step0 = by-assoc-and (under (ε) (ε) (axiom r029)) Eq.refl Eq.refl

step1 : SWAP02 • CX02 • SWAP02 ≈ SWAP02 • CX02 • SWAP01 • SWAP12 • SWAP01
step1 = by-assoc-and (under (SWAP02 • CX02) (ε) (symmetry_SWAP02.proved)) Eq.refl Eq.refl

step2 : SWAP02 • CX02 • SWAP01 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • SWAP01 • CX02 • SWAP01 • SWAP12 • SWAP01
step2 = by-assoc-and (under (ε) (CX02 • SWAP01 • SWAP12 • SWAP01) (symmetry_SWAP02.proved)) Eq.refl Eq.refl

step3 : SWAP01 • SWAP12 • SWAP01 • CX02 • SWAP01 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • CX12 • SWAP12 • SWAP01
step3 = by-assoc-and (under (SWAP01 • SWAP12) (SWAP12 • SWAP01) (sym (axiom r030))) Eq.refl Eq.refl

step4 : SWAP01 • SWAP12 • CX12 • SWAP12 • SWAP01 ≈ SWAP01 • CX21 • SWAP01
step4 = by-assoc-and (under (SWAP01) (SWAP01) (sym (symmetry_CX_g.proved))) Eq.refl Eq.refl

proved : CX20 ≈ SWAP01 • CX21 • SWAP01
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
