{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel104 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CZ01 ; Z0 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r022 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel168 as drel168
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ01 as elim_CZ01
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_Z0 as elim_Z0

step0 : CX01 • Z0 • CZ01 ≈ CX01 • Z0 • CZ01 • CX01 • CX01
step0 = by-assoc-and (under (CX01 • Z0 • CZ01) (ε) (sym (axiom r022))) Eq.refl Eq.refl

step1 : CX01 • Z0 • CZ01 • CX01 • CX01 ≈ CX01 • Z0 • CZ01 • CX01 • CZ01 • CZ01 • CX01
step1 = by-assoc-and (under (CX01 • Z0 • CZ01 • CX01) (CX01) (sym (elim_CZ01.proved))) Eq.refl Eq.refl

step2 : CX01 • Z0 • CZ01 • CX01 • CZ01 • CZ01 • CX01 ≈ CX01 • Z0 • CZ01 • CZ01 • Z0 • CX01 • CZ01 • CX01
step2 = by-assoc-and (under (CX01 • Z0 • CZ01) (CZ01 • CX01) (drel168.proved)) Eq.refl Eq.refl

step3 : CX01 • Z0 • CZ01 • CZ01 • Z0 • CX01 • CZ01 • CX01 ≈ CX01 • Z0 • Z0 • CX01 • CZ01 • CX01
step3 = by-assoc-and (under (CX01 • Z0) (Z0 • CX01 • CZ01 • CX01) (elim_CZ01.proved)) Eq.refl Eq.refl

step4 : CX01 • Z0 • Z0 • CX01 • CZ01 • CX01 ≈ CX01 • CX01 • CZ01 • CX01
step4 = by-assoc-and (under (CX01) (CX01 • CZ01 • CX01) (elim_Z0.proved)) Eq.refl Eq.refl

step5 : CX01 • CX01 • CZ01 • CX01 ≈ CZ01 • CX01
step5 = by-assoc-and (under (ε) (CZ01 • CX01) (axiom r022)) Eq.refl Eq.refl

proved : CX01 • Z0 • CZ01 ≈ CZ01 • CX01
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
