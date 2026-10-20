{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.cflip1 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; SWAP01 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r014 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.cflip3 as cflip3
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CCX_c as symmetry_CCX_c

step0 : CCX01 • CCX12 • CCX01 ≈ CCX01 • CCX12 • SWAP01 • CCX01 • SWAP01
step0 = by-assoc-and (under (CCX01 • CCX12) (ε) (symmetry_CCX_c.proved)) Eq.refl Eq.refl

step1 : CCX01 • CCX12 • SWAP01 • CCX01 • SWAP01 ≈ SWAP01 • CCX01 • SWAP01 • CCX12 • SWAP01 • CCX01 • SWAP01
step1 = by-assoc-and (under (ε) (CCX12 • SWAP01 • CCX01 • SWAP01) (symmetry_CCX_c.proved)) Eq.refl Eq.refl

step2 : SWAP01 • CCX01 • SWAP01 • CCX12 • SWAP01 • CCX01 • SWAP01 ≈ SWAP01 • CCX01 • CCX02 • CCX01 • SWAP01
step2 = by-assoc-and (under (SWAP01 • CCX01) (CCX01 • SWAP01) (sym (axiom r014))) Eq.refl Eq.refl

step3 : SWAP01 • CCX01 • CCX02 • CCX01 • SWAP01 ≈ SWAP01 • CCX02 • CCX01 • CCX02 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (sym (cflip3.proved))) Eq.refl Eq.refl

step4 : SWAP01 • CCX02 • CCX01 • CCX02 • SWAP01 ≈ SWAP01 • CCX02 • CCX01 • SWAP01 • CCX12 • SWAP01 • SWAP01
step4 = by-assoc-and (under (SWAP01 • CCX02 • CCX01) (SWAP01) (axiom r014)) Eq.refl Eq.refl

step5 : SWAP01 • CCX02 • CCX01 • SWAP01 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • CCX12 • SWAP01 • CCX01 • SWAP01 • CCX12 • SWAP01 • SWAP01
step5 = by-assoc-and (under (SWAP01) (CCX01 • SWAP01 • CCX12 • SWAP01 • SWAP01) (axiom r014)) Eq.refl Eq.refl

step6 : SWAP01 • SWAP01 • CCX12 • SWAP01 • CCX01 • SWAP01 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • CCX12 • CCX01 • CCX12 • SWAP01 • SWAP01
step6 = by-assoc-and (under (SWAP01 • SWAP01 • CCX12) (CCX12 • SWAP01 • SWAP01) (sym (symmetry_CCX_c.proved))) Eq.refl Eq.refl

step7 : SWAP01 • SWAP01 • CCX12 • CCX01 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • CCX12 • CCX01 • CCX12
step7 = by-assoc-and (under (SWAP01 • SWAP01 • CCX12 • CCX01 • CCX12) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

step8 : SWAP01 • SWAP01 • CCX12 • CCX01 • CCX12 ≈ CCX12 • CCX01 • CCX12
step8 = by-assoc-and (under (ε) (CCX12 • CCX01 • CCX12) (elim_SWAP01.proved)) Eq.refl Eq.refl

proved : CCX01 • CCX12 • CCX01 ≈ CCX12 • CCX01 • CCX12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))
