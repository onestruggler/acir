{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel163 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX02 ; CZ01 ; CZ02 ; SWAP12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r009 ; r018 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel166 as drel166
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12

step0 : CX02 • CZ01 ≈ CX02 • CZ01 • SWAP12 • SWAP12
step0 = by-assoc-and (under (CX02 • CZ01) (ε) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step1 : CX02 • CZ01 • SWAP12 • SWAP12 ≈ SWAP12 • CX01 • SWAP12 • CZ01 • SWAP12 • SWAP12
step1 = by-assoc-and (under (ε) (CZ01 • SWAP12 • SWAP12) (axiom r009)) Eq.refl Eq.refl

step2 : SWAP12 • CX01 • SWAP12 • CZ01 • SWAP12 • SWAP12 ≈ SWAP12 • CX01 • CZ02 • SWAP12
step2 = by-assoc-and (under (SWAP12 • CX01) (SWAP12) (sym (axiom r018))) Eq.refl Eq.refl

step3 : SWAP12 • CX01 • CZ02 • SWAP12 ≈ SWAP12 • CZ02 • CX01 • SWAP12
step3 = by-assoc-and (under (SWAP12) (SWAP12) (drel166.proved)) Eq.refl Eq.refl

step4 : SWAP12 • CZ02 • CX01 • SWAP12 ≈ SWAP12 • SWAP12 • CZ01 • SWAP12 • CX01 • SWAP12
step4 = by-assoc-and (under (SWAP12) (CX01 • SWAP12) (axiom r018)) Eq.refl Eq.refl

step5 : SWAP12 • SWAP12 • CZ01 • SWAP12 • CX01 • SWAP12 ≈ SWAP12 • SWAP12 • CZ01 • CX02
step5 = by-assoc-and (under (SWAP12 • SWAP12 • CZ01) (ε) (sym (axiom r009))) Eq.refl Eq.refl

step6 : SWAP12 • SWAP12 • CZ01 • CX02 ≈ CZ01 • CX02
step6 = by-assoc-and (under (ε) (CZ01 • CX02) (elim_SWAP12.proved)) Eq.refl Eq.refl

proved : CX02 • CZ01 ≈ CZ01 • CX02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
