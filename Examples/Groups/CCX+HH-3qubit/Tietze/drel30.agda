{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel30 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX12 ; CX21 ; K12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r023 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel46 as drel46
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX12 as elim_CX12
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX21 as elim_CX21

step0 : CX21 • K12 ≈ CX21 • K12 • CX12 • CX12
step0 = by-assoc-and (under (CX21 • K12) (ε) (sym (elim_CX12.proved))) Eq.refl Eq.refl

step1 : CX21 • K12 • CX12 • CX12 ≈ CX21 • K12 • CX12 • K12 • K12 • CX12
step1 = by-assoc-and (under (CX21 • K12 • CX12) (CX12) (sym (axiom r023))) Eq.refl Eq.refl

step2 : CX21 • K12 • CX12 • K12 • K12 • CX12 ≈ CX21 • K12 • K12 • CX21 • K12 • CX12
step2 = by-assoc-and (under (CX21 • K12) (K12 • CX12) (sym (drel46.proved))) Eq.refl Eq.refl

step3 : CX21 • K12 • K12 • CX21 • K12 • CX12 ≈ CX21 • CX21 • K12 • CX12
step3 = by-assoc-and (under (CX21) (CX21 • K12 • CX12) (axiom r023)) Eq.refl Eq.refl

step4 : CX21 • CX21 • K12 • CX12 ≈ K12 • CX12
step4 = by-assoc-and (under (ε) (K12 • CX12) (elim_CX21.proved)) Eq.refl Eq.refl

proved : CX21 • K12 ≈ K12 • CX12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
