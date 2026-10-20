{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel48 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX02 ; CZ02 ; K12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r023 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel47 as drel47
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX02 as elim_CX02
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ02 as elim_CZ02

step0 : CZ02 • K12 ≈ CZ02 • K12 • CX02 • CX02
step0 = by-assoc-and (under (CZ02 • K12) (ε) (sym (elim_CX02.proved))) Eq.refl Eq.refl

step1 : CZ02 • K12 • CX02 • CX02 ≈ CZ02 • K12 • CX02 • K12 • K12 • CX02
step1 = by-assoc-and (under (CZ02 • K12 • CX02) (CX02) (sym (axiom r023))) Eq.refl Eq.refl

step2 : CZ02 • K12 • CX02 • K12 • K12 • CX02 ≈ CZ02 • K12 • K12 • CZ02 • K12 • CX02
step2 = by-assoc-and (under (CZ02 • K12) (K12 • CX02) (sym (drel47.proved))) Eq.refl Eq.refl

step3 : CZ02 • K12 • K12 • CZ02 • K12 • CX02 ≈ CZ02 • CZ02 • K12 • CX02
step3 = by-assoc-and (under (CZ02) (CZ02 • K12 • CX02) (axiom r023)) Eq.refl Eq.refl

step4 : CZ02 • CZ02 • K12 • CX02 ≈ K12 • CX02
step4 = by-assoc-and (under (ε) (K12 • CX02) (elim_CZ02.proved)) Eq.refl Eq.refl

proved : CZ02 • K12 ≈ K12 • CX02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
