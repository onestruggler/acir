{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel38 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; CZ02 ; CZ12 ; SWAP01 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r014 ; r019 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel37 as drel37
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01

step0 : CZ12 • CCX12 ≈ CZ12 • CCX12 • SWAP01 • SWAP01
step0 = by-assoc-and (under (CZ12 • CCX12) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step1 : CZ12 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • CZ02 • SWAP01 • CCX12 • SWAP01 • SWAP01
step1 = by-assoc-and (under (ε) (CCX12 • SWAP01 • SWAP01) (axiom r019)) Eq.refl Eq.refl

step2 : SWAP01 • CZ02 • SWAP01 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • CZ02 • CCX02 • SWAP01
step2 = by-assoc-and (under (SWAP01 • CZ02) (SWAP01) (sym (axiom r014))) Eq.refl Eq.refl

step3 : SWAP01 • CZ02 • CCX02 • SWAP01 ≈ SWAP01 • CCX02 • CZ02 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (drel37.proved)) Eq.refl Eq.refl

step4 : SWAP01 • CCX02 • CZ02 • SWAP01 ≈ SWAP01 • SWAP01 • CCX12 • SWAP01 • CZ02 • SWAP01
step4 = by-assoc-and (under (SWAP01) (CZ02 • SWAP01) (axiom r014)) Eq.refl Eq.refl

step5 : SWAP01 • SWAP01 • CCX12 • SWAP01 • CZ02 • SWAP01 ≈ SWAP01 • SWAP01 • CCX12 • CZ12
step5 = by-assoc-and (under (SWAP01 • SWAP01 • CCX12) (ε) (sym (axiom r019))) Eq.refl Eq.refl

step6 : SWAP01 • SWAP01 • CCX12 • CZ12 ≈ CCX12 • CZ12
step6 = by-assoc-and (under (ε) (CCX12 • CZ12) (elim_SWAP01.proved)) Eq.refl Eq.refl

proved : CZ12 • CCX12 ≈ CCX12 • CZ12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
