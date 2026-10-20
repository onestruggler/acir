{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CZ_e where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CZ12 ; K12 ; SWAP12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r020 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_SWAP12_alt as symmetry_SWAP12_alt

step0 : CZ12 ≈ SWAP12 • SWAP12 • CZ12
step0 = by-assoc-and (under (ε) (CZ12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step1 : SWAP12 • SWAP12 • CZ12 ≈ SWAP12 • CZ12 • K12 • CZ12 • K12 • CZ12 • K12 • CZ12
step1 = by-assoc-and (under (SWAP12) (CZ12) (axiom r020)) Eq.refl Eq.refl

step2 : SWAP12 • CZ12 • K12 • CZ12 • K12 • CZ12 • K12 • CZ12 ≈ SWAP12 • CZ12 • SWAP12
step2 = by-assoc-and (under (SWAP12 • CZ12) (ε) (symmetry_SWAP12_alt.proved)) Eq.refl Eq.refl

proved : CZ12 ≈ SWAP12 • CZ12 • SWAP12
proved = trans step0 (trans step1 (trans step2 (refl)))
