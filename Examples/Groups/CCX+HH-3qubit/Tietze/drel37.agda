{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel37 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX02 ; CZ01 ; CZ02 ; SWAP12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r018 ; r033 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel36 as drel36
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12

step0 : CZ02 • CCX02 ≈ SWAP12 • CZ01 • SWAP12 • CCX02
step0 = by-assoc-and (under (ε) (CCX02) (axiom r018)) Eq.refl Eq.refl

step1 : SWAP12 • CZ01 • SWAP12 • CCX02 ≈ SWAP12 • CZ01 • SWAP12 • CCX02 • SWAP12 • SWAP12
step1 = by-assoc-and (under (SWAP12 • CZ01 • SWAP12 • CCX02) (ε) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step2 : SWAP12 • CZ01 • SWAP12 • CCX02 • SWAP12 • SWAP12 ≈ SWAP12 • CZ01 • CCX01 • SWAP12
step2 = by-assoc-and (under (SWAP12 • CZ01) (SWAP12) (sym (axiom r033))) Eq.refl Eq.refl

step3 : SWAP12 • CZ01 • CCX01 • SWAP12 ≈ SWAP12 • CCX01 • CZ01 • SWAP12
step3 = by-assoc-and (under (SWAP12) (SWAP12) (drel36.proved)) Eq.refl Eq.refl

step4 : SWAP12 • CCX01 • CZ01 • SWAP12 ≈ SWAP12 • SWAP12 • CCX02 • SWAP12 • CZ01 • SWAP12
step4 = by-assoc-and (under (SWAP12) (CZ01 • SWAP12) (axiom r033)) Eq.refl Eq.refl

step5 : SWAP12 • SWAP12 • CCX02 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • SWAP12 • CCX02 • CZ02
step5 = by-assoc-and (under (SWAP12 • SWAP12 • CCX02) (ε) (sym (axiom r018))) Eq.refl Eq.refl

step6 : SWAP12 • SWAP12 • CCX02 • CZ02 ≈ CCX02 • CZ02
step6 = by-assoc-and (under (ε) (CCX02 • CZ02) (elim_SWAP12.proved)) Eq.refl Eq.refl

proved : CZ02 • CCX02 ≈ CCX02 • CZ02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
