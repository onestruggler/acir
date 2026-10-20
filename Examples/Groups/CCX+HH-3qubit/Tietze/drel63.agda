{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel63 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CCX12 ; K01 ; K12 ; SWAP02 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r011 ; r032 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel128 as drel128
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CCX_f as symmetry_CCX_f

step0 : K01 • CCX12 ≈ SWAP02 • K12 • SWAP02 • CCX12
step0 = by-assoc-and (under (ε) (CCX12) (axiom r011)) Eq.refl Eq.refl

step1 : SWAP02 • K12 • SWAP02 • CCX12 ≈ SWAP02 • K12 • SWAP02 • CCX12 • SWAP02 • SWAP02
step1 = by-assoc-and (under (SWAP02 • K12 • SWAP02 • CCX12) (ε) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step2 : SWAP02 • K12 • SWAP02 • CCX12 • SWAP02 • SWAP02 ≈ SWAP02 • K12 • CCX01 • SWAP02
step2 = by-assoc-and (under (SWAP02 • K12) (SWAP02) (sym (axiom r032))) Eq.refl Eq.refl

step3 : SWAP02 • K12 • CCX01 • SWAP02 ≈ SWAP02 • CCX02 • K12 • SWAP02
step3 = by-assoc-and (under (SWAP02) (SWAP02) (drel128.proved)) Eq.refl Eq.refl

step4 : SWAP02 • CCX02 • K12 • SWAP02 ≈ SWAP02 • CCX02 • SWAP02 • SWAP02 • K12 • SWAP02
step4 = by-assoc-and (under (SWAP02 • CCX02) (K12 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step5 : SWAP02 • CCX02 • SWAP02 • SWAP02 • K12 • SWAP02 ≈ SWAP02 • CCX02 • SWAP02 • K01
step5 = by-assoc-and (under (SWAP02 • CCX02 • SWAP02) (ε) (sym (axiom r011))) Eq.refl Eq.refl

step6 : SWAP02 • CCX02 • SWAP02 • K01 ≈ CCX02 • K01
step6 = by-assoc-and (under (ε) (K01) (sym (symmetry_CCX_f.proved))) Eq.refl Eq.refl

proved : K01 • CCX12 ≈ CCX02 • K01
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
