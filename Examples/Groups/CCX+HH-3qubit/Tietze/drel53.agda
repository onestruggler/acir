{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel53 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; SWAP01 ; Z0 ; Z1 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r014 ; r034 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel52 as drel52
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01

step0 : Z1 • CCX12 ≈ Z1 • CCX12 • SWAP01 • SWAP01
step0 = by-assoc-and (under (Z1 • CCX12) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step1 : Z1 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • Z0 • SWAP01 • CCX12 • SWAP01 • SWAP01
step1 = by-assoc-and (under (ε) (CCX12 • SWAP01 • SWAP01) (axiom r034)) Eq.refl Eq.refl

step2 : SWAP01 • Z0 • SWAP01 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • Z0 • CCX02 • SWAP01
step2 = by-assoc-and (under (SWAP01 • Z0) (SWAP01) (sym (axiom r014))) Eq.refl Eq.refl

step3 : SWAP01 • Z0 • CCX02 • SWAP01 ≈ SWAP01 • CCX02 • Z0 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (drel52.proved)) Eq.refl Eq.refl

step4 : SWAP01 • CCX02 • Z0 • SWAP01 ≈ SWAP01 • SWAP01 • CCX12 • SWAP01 • Z0 • SWAP01
step4 = by-assoc-and (under (SWAP01) (Z0 • SWAP01) (axiom r014)) Eq.refl Eq.refl

step5 : SWAP01 • SWAP01 • CCX12 • SWAP01 • Z0 • SWAP01 ≈ SWAP01 • SWAP01 • CCX12 • Z1
step5 = by-assoc-and (under (SWAP01 • SWAP01 • CCX12) (ε) (sym (axiom r034))) Eq.refl Eq.refl

step6 : SWAP01 • SWAP01 • CCX12 • Z1 ≈ CCX12 • Z1
step6 = by-assoc-and (under (ε) (CCX12 • Z1) (elim_SWAP01.proved)) Eq.refl Eq.refl

proved : Z1 • CCX12 ≈ CCX12 • Z1
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
