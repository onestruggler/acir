{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_SWAP02 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX02 ; CX12 ; CX20 ; CX21 ; SWAP01 ; SWAP02 ; SWAP12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r008 ; r010 ; r030 ; r031 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01

step0 : SWAP02 ≈ CX02 • CX20 • CX02
step0 = by-assoc-and (under (ε) (ε) (axiom r010)) Eq.refl Eq.refl

step1 : CX02 • CX20 • CX02 ≈ CX02 • CX20 • CX02 • SWAP01 • SWAP01
step1 = by-assoc-and (under (CX02 • CX20 • CX02) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step2 : CX02 • CX20 • CX02 • SWAP01 • SWAP01 ≈ CX02 • CX20 • SWAP01 • SWAP01 • CX02 • SWAP01 • SWAP01
step2 = by-assoc-and (under (CX02 • CX20) (CX02 • SWAP01 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step3 : CX02 • CX20 • SWAP01 • SWAP01 • CX02 • SWAP01 • SWAP01 ≈ CX02 • CX20 • SWAP01 • CX12 • SWAP01
step3 = by-assoc-and (under (CX02 • CX20 • SWAP01) (SWAP01) (sym (axiom r030))) Eq.refl Eq.refl

step4 : CX02 • CX20 • SWAP01 • CX12 • SWAP01 ≈ CX02 • SWAP01 • SWAP01 • CX20 • SWAP01 • CX12 • SWAP01
step4 = by-assoc-and (under (CX02) (CX20 • SWAP01 • CX12 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step5 : CX02 • SWAP01 • SWAP01 • CX20 • SWAP01 • CX12 • SWAP01 ≈ CX02 • SWAP01 • CX21 • CX12 • SWAP01
step5 = by-assoc-and (under (CX02 • SWAP01) (CX12 • SWAP01) (sym (axiom r031))) Eq.refl Eq.refl

step6 : CX02 • SWAP01 • CX21 • CX12 • SWAP01 ≈ SWAP01 • SWAP01 • CX02 • SWAP01 • CX21 • CX12 • SWAP01
step6 = by-assoc-and (under (ε) (CX02 • SWAP01 • CX21 • CX12 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step7 : SWAP01 • SWAP01 • CX02 • SWAP01 • CX21 • CX12 • SWAP01 ≈ SWAP01 • CX12 • CX21 • CX12 • SWAP01
step7 = by-assoc-and (under (SWAP01) (CX21 • CX12 • SWAP01) (sym (axiom r030))) Eq.refl Eq.refl

step8 : SWAP01 • CX12 • CX21 • CX12 • SWAP01 ≈ SWAP01 • SWAP12 • SWAP01
step8 = by-assoc-and (under (SWAP01) (SWAP01) (sym (axiom r008))) Eq.refl Eq.refl

proved : SWAP02 ≈ SWAP01 • SWAP12 • SWAP01
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))
