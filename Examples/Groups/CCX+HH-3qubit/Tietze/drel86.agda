{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel86 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; K12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r023 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel29 as drel29

step0 : K12 • CCX01 ≈ K12 • CCX01 • K12 • K12
step0 = by-assoc-and (under (K12 • CCX01) (ε) (sym (axiom r023))) Eq.refl Eq.refl

step1 : K12 • CCX01 • K12 • K12 ≈ K12 • K12 • CCX02 • K12
step1 = by-assoc-and (under (K12) (K12) (drel29.proved)) Eq.refl Eq.refl

step2 : K12 • K12 • CCX02 • K12 ≈ CCX02 • K12
step2 = by-assoc-and (under (ε) (CCX02 • K12) (axiom r023)) Eq.refl Eq.refl

proved : K12 • CCX01 ≈ CCX02 • K12
proved = trans step0 (trans step1 (trans step2 (refl)))
