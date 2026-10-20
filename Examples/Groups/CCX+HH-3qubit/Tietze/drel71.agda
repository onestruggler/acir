{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel71 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX02 ; CZ01 ; CZ02 ; K12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r023 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel47 as drel47
import Examples.Groups.CCX+HH-3qubit.Tietze.drel48 as drel48
import Examples.Groups.CCX+HH-3qubit.Tietze.drel49 as drel49
import Examples.Groups.CCX+HH-3qubit.Tietze.drel50 as drel50
import Examples.Groups.CCX+HH-3qubit.Tietze.drel9 as drel9

step0 : CZ01 • CZ02 ≈ K12 • K12 • CZ01 • CZ02
step0 = by-assoc-and (under (ε) (CZ01 • CZ02) (sym (axiom r023))) Eq.refl Eq.refl

step1 : K12 • K12 • CZ01 • CZ02 ≈ K12 • CX01 • K12 • CZ02
step1 = by-assoc-and (under (K12) (CZ02) (drel49.proved)) Eq.refl Eq.refl

step2 : K12 • CX01 • K12 • CZ02 ≈ K12 • CX01 • CX02 • K12
step2 = by-assoc-and (under (K12 • CX01) (ε) (drel47.proved)) Eq.refl Eq.refl

step3 : K12 • CX01 • CX02 • K12 ≈ K12 • CX02 • CX01 • K12
step3 = by-assoc-and (under (K12) (K12) (drel9.proved)) Eq.refl Eq.refl

step4 : K12 • CX02 • CX01 • K12 ≈ CZ02 • K12 • CX01 • K12
step4 = by-assoc-and (under (ε) (CX01 • K12) (sym (drel48.proved))) Eq.refl Eq.refl

step5 : CZ02 • K12 • CX01 • K12 ≈ CZ02 • CZ01 • K12 • K12
step5 = by-assoc-and (under (CZ02) (K12) (sym (drel50.proved))) Eq.refl Eq.refl

step6 : CZ02 • CZ01 • K12 • K12 ≈ CZ02 • CZ01
step6 = by-assoc-and (under (CZ02 • CZ01) (ε) (axiom r023)) Eq.refl Eq.refl

proved : CZ01 • CZ02 ≈ CZ02 • CZ01
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
