{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ02 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CZ01 ; CZ02 ; SWAP12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r018 ; refl ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ01 as elim_CZ01
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12

step0 : CZ02 • CZ02 ≈ CZ02 • SWAP12 • CZ01 • SWAP12
step0 = by-assoc-and (under (CZ02) (ε) (axiom r018)) Eq.refl Eq.refl

step1 : CZ02 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • CZ01 • SWAP12 • SWAP12 • CZ01 • SWAP12
step1 = by-assoc-and (under (ε) (SWAP12 • CZ01 • SWAP12) (axiom r018)) Eq.refl Eq.refl

step2 : SWAP12 • CZ01 • SWAP12 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • CZ01 • CZ01 • SWAP12
step2 = by-assoc-and (under (SWAP12 • CZ01) (CZ01 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

step3 : SWAP12 • CZ01 • CZ01 • SWAP12 ≈ SWAP12 • SWAP12
step3 = by-assoc-and (under (SWAP12) (SWAP12) (elim_CZ01.proved)) Eq.refl Eq.refl

step4 : SWAP12 • SWAP12 ≈ ε
step4 = by-assoc-and (under (ε) (ε) (elim_SWAP12.proved)) Eq.refl Eq.refl

proved : CZ02 • CZ02 ≈ ε
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
