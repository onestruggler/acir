{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ01 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CZ01 ; K12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r001 ; r022 ; r023 ; refl ; trans ; under ; ε ; module Eq)
open K

step0 : CZ01 • CZ01 ≈ CZ01 • K12 • CX01 • K12
step0 = by-assoc-and (under (CZ01) (ε) (axiom r001)) Eq.refl Eq.refl

step1 : CZ01 • K12 • CX01 • K12 ≈ K12 • CX01 • K12 • K12 • CX01 • K12
step1 = by-assoc-and (under (ε) (K12 • CX01 • K12) (axiom r001)) Eq.refl Eq.refl

step2 : K12 • CX01 • K12 • K12 • CX01 • K12 ≈ K12 • CX01 • CX01 • K12
step2 = by-assoc-and (under (K12 • CX01) (CX01 • K12) (axiom r023)) Eq.refl Eq.refl

step3 : K12 • CX01 • CX01 • K12 ≈ K12 • K12
step3 = by-assoc-and (under (K12) (K12) (axiom r022)) Eq.refl Eq.refl

step4 : K12 • K12 ≈ ε
step4 = by-assoc-and (under (ε) (ε) (axiom r023)) Eq.refl Eq.refl

proved : CZ01 • CZ01 ≈ ε
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
