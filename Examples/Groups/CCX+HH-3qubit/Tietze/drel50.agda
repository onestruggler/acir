{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel50 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CZ01 ; K12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r022 ; r023 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel49 as drel49
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ01 as elim_CZ01

step0 : CZ01 • K12 ≈ CZ01 • K12 • CX01 • CX01
step0 = by-assoc-and (under (CZ01 • K12) (ε) (sym (axiom r022))) Eq.refl Eq.refl

step1 : CZ01 • K12 • CX01 • CX01 ≈ CZ01 • K12 • CX01 • K12 • K12 • CX01
step1 = by-assoc-and (under (CZ01 • K12 • CX01) (CX01) (sym (axiom r023))) Eq.refl Eq.refl

step2 : CZ01 • K12 • CX01 • K12 • K12 • CX01 ≈ CZ01 • K12 • K12 • CZ01 • K12 • CX01
step2 = by-assoc-and (under (CZ01 • K12) (K12 • CX01) (sym (drel49.proved))) Eq.refl Eq.refl

step3 : CZ01 • K12 • K12 • CZ01 • K12 • CX01 ≈ CZ01 • CZ01 • K12 • CX01
step3 = by-assoc-and (under (CZ01) (CZ01 • K12 • CX01) (axiom r023)) Eq.refl Eq.refl

step4 : CZ01 • CZ01 • K12 • CX01 ≈ K12 • CX01
step4 = by-assoc-and (under (ε) (K12 • CX01) (elim_CZ01.proved)) Eq.refl Eq.refl

proved : CZ01 • K12 ≈ K12 • CX01
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
