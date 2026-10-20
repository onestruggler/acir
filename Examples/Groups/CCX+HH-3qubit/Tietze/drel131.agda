{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel131 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; CX20 ; CX21 ; SWAP01 ; X0 ; X1 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r014 ; r028 ; r031 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel127 as drel127
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01

step0 : X1 • CCX12 ≈ X1 • CCX12 • SWAP01 • SWAP01
step0 = by-assoc-and (under (X1 • CCX12) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step1 : X1 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • X0 • SWAP01 • CCX12 • SWAP01 • SWAP01
step1 = by-assoc-and (under (ε) (CCX12 • SWAP01 • SWAP01) (axiom r028)) Eq.refl Eq.refl

step2 : SWAP01 • X0 • SWAP01 • CCX12 • SWAP01 • SWAP01 ≈ SWAP01 • X0 • CCX02 • SWAP01
step2 = by-assoc-and (under (SWAP01 • X0) (SWAP01) (sym (axiom r014))) Eq.refl Eq.refl

step3 : SWAP01 • X0 • CCX02 • SWAP01 ≈ SWAP01 • CCX02 • CX21 • X0 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (drel127.proved)) Eq.refl Eq.refl

step4 : SWAP01 • CCX02 • CX21 • X0 • SWAP01 ≈ SWAP01 • SWAP01 • CCX12 • SWAP01 • CX21 • X0 • SWAP01
step4 = by-assoc-and (under (SWAP01) (CX21 • X0 • SWAP01) (axiom r014)) Eq.refl Eq.refl

step5 : SWAP01 • SWAP01 • CCX12 • SWAP01 • CX21 • X0 • SWAP01 ≈ CCX12 • SWAP01 • CX21 • X0 • SWAP01
step5 = by-assoc-and (under (ε) (CCX12 • SWAP01 • CX21 • X0 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

step6 : CCX12 • SWAP01 • CX21 • X0 • SWAP01 ≈ CCX12 • SWAP01 • SWAP01 • CX20 • SWAP01 • X0 • SWAP01
step6 = by-assoc-and (under (CCX12 • SWAP01) (X0 • SWAP01) (axiom r031)) Eq.refl Eq.refl

step7 : CCX12 • SWAP01 • SWAP01 • CX20 • SWAP01 • X0 • SWAP01 ≈ CCX12 • SWAP01 • SWAP01 • CX20 • X1
step7 = by-assoc-and (under (CCX12 • SWAP01 • SWAP01 • CX20) (ε) (sym (axiom r028))) Eq.refl Eq.refl

step8 : CCX12 • SWAP01 • SWAP01 • CX20 • X1 ≈ CCX12 • CX20 • X1
step8 = by-assoc-and (under (CCX12) (CX20 • X1) (elim_SWAP01.proved)) Eq.refl Eq.refl

proved : X1 • CCX12 ≈ CCX12 • CX20 • X1
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))
