{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel154 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX12 ; CX21 ; SWAP12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r008 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX12 as elim_CX12
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_g as symmetry_CX_g

step0 : CX12 • CX21 ≈ CX12 • SWAP12 • CX12 • SWAP12
step0 = by-assoc-and (under (CX12) (ε) (symmetry_CX_g.proved)) Eq.refl Eq.refl

step1 : CX12 • SWAP12 • CX12 • SWAP12 ≈ CX12 • SWAP12 • CX12 • CX12 • CX21 • CX12
step1 = by-assoc-and (under (CX12 • SWAP12 • CX12) (ε) (axiom r008)) Eq.refl Eq.refl

step2 : CX12 • SWAP12 • CX12 • CX12 • CX21 • CX12 ≈ CX12 • SWAP12 • CX21 • CX12
step2 = by-assoc-and (under (CX12 • SWAP12) (CX21 • CX12) (elim_CX12.proved)) Eq.refl Eq.refl

step3 : CX12 • SWAP12 • CX21 • CX12 ≈ CX12 • CX12 • CX21 • CX12 • CX21 • CX12
step3 = by-assoc-and (under (CX12) (CX21 • CX12) (axiom r008)) Eq.refl Eq.refl

step4 : CX12 • CX12 • CX21 • CX12 • CX21 • CX12 ≈ CX21 • CX12 • CX21 • CX12
step4 = by-assoc-and (under (ε) (CX21 • CX12 • CX21 • CX12) (elim_CX12.proved)) Eq.refl Eq.refl

step5 : CX21 • CX12 • CX21 • CX12 ≈ CX21 • SWAP12
step5 = by-assoc-and (under (CX21) (ε) (sym (axiom r008))) Eq.refl Eq.refl

proved : CX12 • CX21 ≈ CX21 • SWAP12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
