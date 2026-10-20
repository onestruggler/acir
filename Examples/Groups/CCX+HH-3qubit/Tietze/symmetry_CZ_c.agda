{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CZ_c where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CZ02 ; CZ12 ; SWAP01 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r019 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01

step0 : CZ02 ≈ CZ02 • SWAP01 • SWAP01
step0 = by-assoc-and (under (CZ02) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step1 : CZ02 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • CZ02 • SWAP01 • SWAP01
step1 = by-assoc-and (under (ε) (CZ02 • SWAP01 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step2 : SWAP01 • SWAP01 • CZ02 • SWAP01 • SWAP01 ≈ SWAP01 • CZ12 • SWAP01
step2 = by-assoc-and (under (SWAP01) (SWAP01) (sym (axiom r019))) Eq.refl Eq.refl

proved : CZ02 ≈ SWAP01 • CZ12 • SWAP01
proved = trans step0 (trans step1 (trans step2 (refl)))
