{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.cflip2 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; SWAP12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r033 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.cflip1 as cflip1
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CCX_g as symmetry_CCX_g

step0 : CCX02 • CCX12 • CCX02 ≈ CCX02 • CCX12 • CCX02 • SWAP12 • SWAP12
step0 = by-assoc-and (under (CCX02 • CCX12 • CCX02) (ε) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step1 : CCX02 • CCX12 • CCX02 • SWAP12 • SWAP12 ≈ CCX02 • SWAP12 • CCX12 • SWAP12 • CCX02 • SWAP12 • SWAP12
step1 = by-assoc-and (under (CCX02) (CCX02 • SWAP12 • SWAP12) (symmetry_CCX_g.proved)) Eq.refl Eq.refl

step2 : CCX02 • SWAP12 • CCX12 • SWAP12 • CCX02 • SWAP12 • SWAP12 ≈ SWAP12 • SWAP12 • CCX02 • SWAP12 • CCX12 • SWAP12 • CCX02 • SWAP12 • SWAP12
step2 = by-assoc-and (under (ε) (CCX02 • SWAP12 • CCX12 • SWAP12 • CCX02 • SWAP12 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step3 : SWAP12 • SWAP12 • CCX02 • SWAP12 • CCX12 • SWAP12 • CCX02 • SWAP12 • SWAP12 ≈ SWAP12 • SWAP12 • CCX02 • SWAP12 • CCX12 • CCX01 • SWAP12
step3 = by-assoc-and (under (SWAP12 • SWAP12 • CCX02 • SWAP12 • CCX12) (SWAP12) (sym (axiom r033))) Eq.refl Eq.refl

step4 : SWAP12 • SWAP12 • CCX02 • SWAP12 • CCX12 • CCX01 • SWAP12 ≈ SWAP12 • CCX01 • CCX12 • CCX01 • SWAP12
step4 = by-assoc-and (under (SWAP12) (CCX12 • CCX01 • SWAP12) (sym (axiom r033))) Eq.refl Eq.refl

step5 : SWAP12 • CCX01 • CCX12 • CCX01 • SWAP12 ≈ SWAP12 • CCX12 • CCX01 • CCX12 • SWAP12
step5 = by-assoc-and (under (SWAP12) (SWAP12) (cflip1.proved)) Eq.refl Eq.refl

step6 : SWAP12 • CCX12 • CCX01 • CCX12 • SWAP12 ≈ SWAP12 • CCX12 • SWAP12 • CCX02 • SWAP12 • CCX12 • SWAP12
step6 = by-assoc-and (under (SWAP12 • CCX12) (CCX12 • SWAP12) (axiom r033)) Eq.refl Eq.refl

step7 : SWAP12 • CCX12 • SWAP12 • CCX02 • SWAP12 • CCX12 • SWAP12 ≈ SWAP12 • CCX12 • SWAP12 • CCX02 • CCX12
step7 = by-assoc-and (under (SWAP12 • CCX12 • SWAP12 • CCX02) (ε) (sym (symmetry_CCX_g.proved))) Eq.refl Eq.refl

step8 : SWAP12 • CCX12 • SWAP12 • CCX02 • CCX12 ≈ CCX12 • CCX02 • CCX12
step8 = by-assoc-and (under (ε) (CCX02 • CCX12) (sym (symmetry_CCX_g.proved))) Eq.refl Eq.refl

proved : CCX02 • CCX12 • CCX02 ≈ CCX12 • CCX02 • CCX12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))
