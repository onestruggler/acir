{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel23 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; CZ02 ; CZ12 ; SWAP01 ; Z0 ; Z1 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r014 ; r019 ; r034 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel21 as drel21
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01

step0 : Z0 • CCX12 ≈ Z0 • CCX12 • SWAP01 • SWAP01
step0 = by-assoc-and (under (Z0 • CCX12) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step1 : Z0 • CCX12 • SWAP01 • SWAP01 ≈ Z0 • SWAP01 • SWAP01 • CCX12 • SWAP01 • SWAP01
step1 = by-assoc-and (under (Z0) (CCX12 • SWAP01 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step2 : Z0 • SWAP01 • SWAP01 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • SWAP01 • Z0 • SWAP01 • SWAP01 • CCX12 • SWAP01 • SWAP01
step2 = by-assoc-and (under (ε) (Z0 • SWAP01 • SWAP01 • CCX12 • SWAP01 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step3 : SWAP01 • SWAP01 • Z0 • SWAP01 • SWAP01 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • Z1 • SWAP01 • CCX12 • SWAP01 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01 • CCX12 • SWAP01 • SWAP01) (sym (axiom r034))) Eq.refl Eq.refl

step4 : SWAP01 • Z1 • SWAP01 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • Z1 • CCX02 • SWAP01
step4 = by-assoc-and (under (SWAP01 • Z1) (SWAP01) (sym (axiom r014))) Eq.refl Eq.refl

step5 : SWAP01 • Z1 • CCX02 • SWAP01 ≈ SWAP01 • CCX02 • CZ02 • Z1 • SWAP01
step5 = by-assoc-and (under (SWAP01) (SWAP01) (drel21.proved)) Eq.refl Eq.refl

step6 : SWAP01 • CCX02 • CZ02 • Z1 • SWAP01 ≈ SWAP01 • SWAP01 • CCX12 • SWAP01 • CZ02 • Z1 • SWAP01
step6 = by-assoc-and (under (SWAP01) (CZ02 • Z1 • SWAP01) (axiom r014)) Eq.refl Eq.refl

step7 : SWAP01 • SWAP01 • CCX12 • SWAP01 • CZ02 • Z1 • SWAP01 ≈ CCX12 • SWAP01 • CZ02 • Z1 • SWAP01
step7 = by-assoc-and (under (ε) (CCX12 • SWAP01 • CZ02 • Z1 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

step8 : CCX12 • SWAP01 • CZ02 • Z1 • SWAP01 ≈ CCX12 • SWAP01 • CZ02 • SWAP01 • Z0 • SWAP01 • SWAP01
step8 = by-assoc-and (under (CCX12 • SWAP01 • CZ02) (SWAP01) (axiom r034)) Eq.refl Eq.refl

step9 : CCX12 • SWAP01 • CZ02 • SWAP01 • Z0 • SWAP01 • SWAP01 ≈ CCX12 • SWAP01 • CZ02 • SWAP01 • Z0
step9 = by-assoc-and (under (CCX12 • SWAP01 • CZ02 • SWAP01 • Z0) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

step10 : CCX12 • SWAP01 • CZ02 • SWAP01 • Z0 ≈ CCX12 • CZ12 • Z0
step10 = by-assoc-and (under (CCX12) (Z0) (sym (axiom r019))) Eq.refl Eq.refl

proved : Z0 • CCX12 ≈ CCX12 • CZ12 • Z0
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (refl)))))))))))
