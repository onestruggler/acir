{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel46 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX12 ; CX21 ; K12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r007 ; r023 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K

step0 : K12 • CX21 ≈ K12 • CX21 • K12 • K12
step0 = by-assoc-and (under (K12 • CX21) (ε) (sym (axiom r023))) Eq.refl Eq.refl

step1 : K12 • CX21 • K12 • K12 ≈ CX12 • K12
step1 = by-assoc-and (under (ε) (K12) (sym (axiom r007))) Eq.refl Eq.refl

proved : K12 • CX21 ≈ CX12 • K12
proved = trans step0 (trans step1 (refl))
