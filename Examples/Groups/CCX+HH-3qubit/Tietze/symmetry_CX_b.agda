{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_b where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX10 ; CX12 ; SWAP02 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_f as symmetry_CX_f

step0 : CX10 ≈ CX10 • SWAP02 • SWAP02
step0 = by-assoc-and (under (CX10) (ε) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step1 : CX10 • SWAP02 • SWAP02 ≈ SWAP02 • SWAP02 • CX10 • SWAP02 • SWAP02
step1 = by-assoc-and (under (ε) (CX10 • SWAP02 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step2 : SWAP02 • SWAP02 • CX10 • SWAP02 • SWAP02 ≈ SWAP02 • CX12 • SWAP02
step2 = by-assoc-and (under (SWAP02) (SWAP02) (sym (symmetry_CX_f.proved))) Eq.refl Eq.refl

proved : CX10 ≈ SWAP02 • CX12 • SWAP02
proved = trans step0 (trans step1 (trans step2 (refl)))
