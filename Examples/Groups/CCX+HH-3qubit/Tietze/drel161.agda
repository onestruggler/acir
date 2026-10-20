{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel161 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX10 ; K01 ; SWAP01 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r012 ; r013 ; r025 ; r035 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX10 as elim_CX10
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01

step0 : CX01 • CX10 ≈ CX10 • CX10 • CX01 • CX10
step0 = by-assoc-and (under (ε) (CX01 • CX10) (sym (elim_CX10.proved))) Eq.refl Eq.refl

step1 : CX10 • CX10 • CX01 • CX10 ≈ CX10 • CX10 • CX01 • K01 • CX01 • K01
step1 = by-assoc-and (under (CX10 • CX10 • CX01) (ε) (axiom r012)) Eq.refl Eq.refl

step2 : CX10 • CX10 • CX01 • K01 • CX01 • K01 ≈ CX10 • K01 • CX01 • K01 • CX01 • K01 • CX01 • K01
step2 = by-assoc-and (under (CX10) (CX01 • K01 • CX01 • K01) (axiom r012)) Eq.refl Eq.refl

step3 : CX10 • K01 • CX01 • K01 • CX01 • K01 • CX01 • K01 ≈ CX10 • K01 • CX01 • CX10 • CX01 • K01
step3 = by-assoc-and (under (CX10 • K01 • CX01) (CX01 • K01) (sym (axiom r012))) Eq.refl Eq.refl

step4 : CX10 • K01 • CX01 • CX10 • CX01 • K01 ≈ CX10 • K01 • SWAP01 • K01
step4 = by-assoc-and (under (CX10 • K01) (K01) (sym (axiom r013))) Eq.refl Eq.refl

step5 : CX10 • K01 • SWAP01 • K01 ≈ CX10 • SWAP01 • K01 • SWAP01 • SWAP01 • K01
step5 = by-assoc-and (under (CX10) (SWAP01 • K01) (axiom r035)) Eq.refl Eq.refl

step6 : CX10 • SWAP01 • K01 • SWAP01 • SWAP01 • K01 ≈ CX10 • SWAP01 • K01 • K01
step6 = by-assoc-and (under (CX10 • SWAP01 • K01) (K01) (elim_SWAP01.proved)) Eq.refl Eq.refl

step7 : CX10 • SWAP01 • K01 • K01 ≈ CX10 • SWAP01
step7 = by-assoc-and (under (CX10 • SWAP01) (ε) (axiom r025)) Eq.refl Eq.refl

proved : CX01 • CX10 ≈ CX10 • SWAP01
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (refl))))))))
