{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel47 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX02 ; CZ01 ; CZ02 ; K12 ; SWAP12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r001 ; r009 ; r018 ; r023 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_K_a as symmetry_K_a

step0 : K12 • CZ02 ≈ K12 • SWAP12 • CZ01 • SWAP12
step0 = by-assoc-and (under (K12) (ε) (axiom r018)) Eq.refl Eq.refl

step1 : K12 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • SWAP12 • K12 • SWAP12 • CZ01 • SWAP12
step1 = by-assoc-and (under (ε) (K12 • SWAP12 • CZ01 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step2 : SWAP12 • SWAP12 • K12 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • K12 • CZ01 • SWAP12
step2 = by-assoc-and (under (SWAP12) (CZ01 • SWAP12) (sym (symmetry_K_a.proved))) Eq.refl Eq.refl

step3 : SWAP12 • K12 • CZ01 • SWAP12 ≈ SWAP12 • K12 • K12 • CX01 • K12 • SWAP12
step3 = by-assoc-and (under (SWAP12 • K12) (SWAP12) (axiom r001)) Eq.refl Eq.refl

step4 : SWAP12 • K12 • K12 • CX01 • K12 • SWAP12 ≈ SWAP12 • CX01 • K12 • SWAP12
step4 = by-assoc-and (under (SWAP12) (CX01 • K12 • SWAP12) (axiom r023)) Eq.refl Eq.refl

step5 : SWAP12 • CX01 • K12 • SWAP12 ≈ SWAP12 • CX01 • SWAP12 • SWAP12 • K12 • SWAP12
step5 = by-assoc-and (under (SWAP12 • CX01) (K12 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step6 : SWAP12 • CX01 • SWAP12 • SWAP12 • K12 • SWAP12 ≈ SWAP12 • CX01 • SWAP12 • K12
step6 = by-assoc-and (under (SWAP12 • CX01 • SWAP12) (ε) (sym (symmetry_K_a.proved))) Eq.refl Eq.refl

step7 : SWAP12 • CX01 • SWAP12 • K12 ≈ CX02 • K12
step7 = by-assoc-and (under (ε) (K12) (sym (axiom r009))) Eq.refl Eq.refl

proved : K12 • CZ02 ≈ CX02 • K12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (refl))))))))
