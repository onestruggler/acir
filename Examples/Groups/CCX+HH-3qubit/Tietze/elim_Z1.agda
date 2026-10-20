{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.elim_Z1 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (SWAP01 ; Z0 ; Z1 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r034 ; refl ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_Z0 as elim_Z0

step0 : Z1 • Z1 ≈ Z1 • SWAP01 • Z0 • SWAP01
step0 = by-assoc-and (under (Z1) (ε) (axiom r034)) Eq.refl Eq.refl

step1 : Z1 • SWAP01 • Z0 • SWAP01 ≈ SWAP01 • Z0 • SWAP01 • SWAP01 • Z0 • SWAP01
step1 = by-assoc-and (under (ε) (SWAP01 • Z0 • SWAP01) (axiom r034)) Eq.refl Eq.refl

step2 : SWAP01 • Z0 • SWAP01 • SWAP01 • Z0 • SWAP01 ≈ SWAP01 • Z0 • Z0 • SWAP01
step2 = by-assoc-and (under (SWAP01 • Z0) (Z0 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

step3 : SWAP01 • Z0 • Z0 • SWAP01 ≈ SWAP01 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (elim_Z0.proved)) Eq.refl Eq.refl

step4 : SWAP01 • SWAP01 ≈ ε
step4 = by-assoc-and (under (ε) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

proved : Z1 • Z1 ≈ ε
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
