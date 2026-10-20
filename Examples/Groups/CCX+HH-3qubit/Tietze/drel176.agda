{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel176 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX12 ; CX21 ; CZ01 ; CZ02 ; SWAP12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r018 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel165 as drel165
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_g as symmetry_CX_g

step0 : CX21 • CZ02 ≈ CX21 • SWAP12 • CZ01 • SWAP12
step0 = by-assoc-and (under (CX21) (ε) (axiom r018)) Eq.refl Eq.refl

step1 : CX21 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • CX12 • SWAP12 • SWAP12 • CZ01 • SWAP12
step1 = by-assoc-and (under (ε) (SWAP12 • CZ01 • SWAP12) (symmetry_CX_g.proved)) Eq.refl Eq.refl

step2 : SWAP12 • CX12 • SWAP12 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • CX12 • CZ01 • SWAP12
step2 = by-assoc-and (under (SWAP12 • CX12) (CZ01 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

step3 : SWAP12 • CX12 • CZ01 • SWAP12 ≈ SWAP12 • CZ01 • CX12 • SWAP12
step3 = by-assoc-and (under (SWAP12) (SWAP12) (drel165.proved)) Eq.refl Eq.refl

step4 : SWAP12 • CZ01 • CX12 • SWAP12 ≈ SWAP12 • CZ01 • SWAP12 • SWAP12 • CX12 • SWAP12
step4 = by-assoc-and (under (SWAP12 • CZ01) (CX12 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step5 : SWAP12 • CZ01 • SWAP12 • SWAP12 • CX12 • SWAP12 ≈ SWAP12 • CZ01 • SWAP12 • CX21
step5 = by-assoc-and (under (SWAP12 • CZ01 • SWAP12) (ε) (sym (symmetry_CX_g.proved))) Eq.refl Eq.refl

step6 : SWAP12 • CZ01 • SWAP12 • CX21 ≈ CZ02 • CX21
step6 = by-assoc-and (under (ε) (CX21) (sym (axiom r018))) Eq.refl Eq.refl

proved : CX21 • CZ02 ≈ CZ02 • CX21
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
