{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel168 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CZ01 ; Z0 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r003 ; r022 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ01 as elim_CZ01

step0 : CX01 • CZ01 ≈ CX01 • CZ01 • CX01 • CX01
step0 = by-assoc-and (under (CX01 • CZ01) (ε) (sym (axiom r022))) Eq.refl Eq.refl

step1 : CX01 • CZ01 • CX01 • CX01 ≈ CZ01 • CZ01 • CX01 • CZ01 • CX01 • CX01
step1 = by-assoc-and (under (ε) (CX01 • CZ01 • CX01 • CX01) (sym (elim_CZ01.proved))) Eq.refl Eq.refl

step2 : CZ01 • CZ01 • CX01 • CZ01 • CX01 • CX01 ≈ CZ01 • Z0 • CX01
step2 = by-assoc-and (under (CZ01) (CX01) (sym (axiom r003))) Eq.refl Eq.refl

proved : CX01 • CZ01 ≈ CZ01 • Z0 • CX01
proved = trans step0 (trans step1 (trans step2 (refl)))
