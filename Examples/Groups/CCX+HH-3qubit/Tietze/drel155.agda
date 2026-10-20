{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel155 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX12 ; CX10 ; CX12 ; CX20 ; CX21 ; SWAP12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r044 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CCX_g as symmetry_CCX_g
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_g as symmetry_CX_g
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_j as symmetry_CX_j

step0 : CX21 • CCX12 ≈ SWAP12 • CX12 • SWAP12 • CCX12
step0 = by-assoc-and (under (ε) (CCX12) (symmetry_CX_g.proved)) Eq.refl Eq.refl

step1 : SWAP12 • CX12 • SWAP12 • CCX12 ≈ SWAP12 • CX12 • SWAP12 • CCX12 • SWAP12 • SWAP12
step1 = by-assoc-and (under (SWAP12 • CX12 • SWAP12 • CCX12) (ε) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step2 : SWAP12 • CX12 • SWAP12 • CCX12 • SWAP12 • SWAP12 ≈ SWAP12 • CX12 • CCX12 • SWAP12
step2 = by-assoc-and (under (SWAP12 • CX12) (SWAP12) (sym (symmetry_CCX_g.proved))) Eq.refl Eq.refl

step3 : SWAP12 • CX12 • CCX12 • SWAP12 ≈ SWAP12 • CCX12 • CX10 • CX12 • SWAP12
step3 = by-assoc-and (under (SWAP12) (SWAP12) (axiom r044)) Eq.refl Eq.refl

step4 : SWAP12 • CCX12 • CX10 • CX12 • SWAP12 ≈ SWAP12 • CCX12 • CX10 • SWAP12 • SWAP12 • CX12 • SWAP12
step4 = by-assoc-and (under (SWAP12 • CCX12 • CX10) (CX12 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step5 : SWAP12 • CCX12 • CX10 • SWAP12 • SWAP12 • CX12 • SWAP12 ≈ SWAP12 • CCX12 • CX10 • SWAP12 • CX21
step5 = by-assoc-and (under (SWAP12 • CCX12 • CX10 • SWAP12) (ε) (sym (symmetry_CX_g.proved))) Eq.refl Eq.refl

step6 : SWAP12 • CCX12 • CX10 • SWAP12 • CX21 ≈ SWAP12 • CCX12 • SWAP12 • SWAP12 • CX10 • SWAP12 • CX21
step6 = by-assoc-and (under (SWAP12 • CCX12) (CX10 • SWAP12 • CX21) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step7 : SWAP12 • CCX12 • SWAP12 • SWAP12 • CX10 • SWAP12 • CX21 ≈ SWAP12 • CCX12 • SWAP12 • CX20 • CX21
step7 = by-assoc-and (under (SWAP12 • CCX12 • SWAP12) (CX21) (sym (symmetry_CX_j.proved))) Eq.refl Eq.refl

step8 : SWAP12 • CCX12 • SWAP12 • CX20 • CX21 ≈ CCX12 • CX20 • CX21
step8 = by-assoc-and (under (ε) (CX20 • CX21) (sym (symmetry_CCX_g.proved))) Eq.refl Eq.refl

proved : CX21 • CCX12 ≈ CCX12 • CX20 • CX21
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))
