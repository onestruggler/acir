{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel49 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CZ01 ; K12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r001 ; r023 ; refl ; trans ; under ; ε ; module Eq)
open K

step0 : K12 • CZ01 ≈ K12 • K12 • CX01 • K12
step0 = by-assoc-and (under (K12) (ε) (axiom r001)) Eq.refl Eq.refl

step1 : K12 • K12 • CX01 • K12 ≈ CX01 • K12
step1 = by-assoc-and (under (ε) (CX01 • K12) (axiom r023)) Eq.refl Eq.refl

proved : K12 • CZ01 ≈ CX01 • K12
proved = trans step0 (trans step1 (refl))
