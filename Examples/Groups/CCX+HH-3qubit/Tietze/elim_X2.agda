{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.elim_X2 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (SWAP02 ; X0 ; X2 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r015 ; r021 ; refl ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02

step0 : X2 • X2 ≈ X2 • SWAP02 • X0 • SWAP02
step0 = by-assoc-and (under (X2) (ε) (axiom r015)) Eq.refl Eq.refl

step1 : X2 • SWAP02 • X0 • SWAP02 ≈ SWAP02 • X0 • SWAP02 • SWAP02 • X0 • SWAP02
step1 = by-assoc-and (under (ε) (SWAP02 • X0 • SWAP02) (axiom r015)) Eq.refl Eq.refl

step2 : SWAP02 • X0 • SWAP02 • SWAP02 • X0 • SWAP02 ≈ SWAP02 • X0 • X0 • SWAP02
step2 = by-assoc-and (under (SWAP02 • X0) (X0 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

step3 : SWAP02 • X0 • X0 • SWAP02 ≈ SWAP02 • SWAP02
step3 = by-assoc-and (under (SWAP02) (SWAP02) (axiom r021)) Eq.refl Eq.refl

step4 : SWAP02 • SWAP02 ≈ ε
step4 = by-assoc-and (under (ε) (ε) (elim_SWAP02.proved)) Eq.refl Eq.refl

proved : X2 • X2 ≈ ε
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
