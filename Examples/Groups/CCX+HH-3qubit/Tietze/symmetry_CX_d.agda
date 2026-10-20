{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_d where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX12 ; CX21 ; SWAP12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r008 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel154 as drel154
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX12 as elim_CX12
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX21 as elim_CX21

step0 : CX12 ≈ CX12 • CX21 • CX21
step0 = by-assoc-and (under (CX12) (ε) (sym (elim_CX21.proved))) Eq.refl Eq.refl

step1 : CX12 • CX21 • CX21 ≈ CX12 • CX21 • CX12 • CX12 • CX21
step1 = by-assoc-and (under (CX12 • CX21) (CX21) (sym (elim_CX12.proved))) Eq.refl Eq.refl

step2 : CX12 • CX21 • CX12 • CX12 • CX21 ≈ SWAP12 • CX12 • CX21
step2 = by-assoc-and (under (ε) (CX12 • CX21) (sym (axiom r008))) Eq.refl Eq.refl

step3 : SWAP12 • CX12 • CX21 ≈ SWAP12 • CX21 • SWAP12
step3 = by-assoc-and (under (SWAP12) (ε) (drel154.proved)) Eq.refl Eq.refl

proved : CX12 ≈ SWAP12 • CX21 • SWAP12
proved = trans step0 (trans step1 (trans step2 (trans step3 (refl))))
