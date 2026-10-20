{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_X_c where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX12 ; CX21 ; SWAP12 ; X1 ; X2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r008 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel133 as drel133
import Examples.Groups.CCX+HH-3qubit.Tietze.drel70 as drel70
import Examples.Groups.CCX+HH-3qubit.Tietze.drel84 as drel84
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12

step0 : X2 ≈ X2 • SWAP12 • SWAP12
step0 = by-assoc-and (under (X2) (ε) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step1 : X2 • SWAP12 • SWAP12 ≈ X2 • CX12 • CX21 • CX12 • SWAP12
step1 = by-assoc-and (under (X2) (SWAP12) (axiom r008)) Eq.refl Eq.refl

step2 : X2 • CX12 • CX21 • CX12 • SWAP12 ≈ CX12 • X2 • CX21 • CX12 • SWAP12
step2 = by-assoc-and (under (ε) (CX21 • CX12 • SWAP12) (drel84.proved)) Eq.refl Eq.refl

step3 : CX12 • X2 • CX21 • CX12 • SWAP12 ≈ CX12 • CX21 • X1 • X2 • CX12 • SWAP12
step3 = by-assoc-and (under (CX12) (CX12 • SWAP12) (drel133.proved)) Eq.refl Eq.refl

step4 : CX12 • CX21 • X1 • X2 • CX12 • SWAP12 ≈ CX12 • CX21 • CX12 • X1 • SWAP12
step4 = by-assoc-and (under (CX12 • CX21) (SWAP12) (sym (drel70.proved))) Eq.refl Eq.refl

step5 : CX12 • CX21 • CX12 • X1 • SWAP12 ≈ SWAP12 • X1 • SWAP12
step5 = by-assoc-and (under (ε) (X1 • SWAP12) (sym (axiom r008))) Eq.refl Eq.refl

proved : X2 ≈ SWAP12 • X1 • SWAP12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
