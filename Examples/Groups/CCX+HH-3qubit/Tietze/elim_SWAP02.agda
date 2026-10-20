{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX02 ; CX20 ; SWAP02 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r010 ; refl ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX02 as elim_CX02
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX20 as elim_CX20

step0 : SWAP02 • SWAP02 ≈ SWAP02 • CX02 • CX20 • CX02
step0 = by-assoc-and (under (SWAP02) (ε) (axiom r010)) Eq.refl Eq.refl

step1 : SWAP02 • CX02 • CX20 • CX02 ≈ CX02 • CX20 • CX02 • CX02 • CX20 • CX02
step1 = by-assoc-and (under (ε) (CX02 • CX20 • CX02) (axiom r010)) Eq.refl Eq.refl

step2 : CX02 • CX20 • CX02 • CX02 • CX20 • CX02 ≈ CX02 • CX20 • CX20 • CX02
step2 = by-assoc-and (under (CX02 • CX20) (CX20 • CX02) (elim_CX02.proved)) Eq.refl Eq.refl

step3 : CX02 • CX20 • CX20 • CX02 ≈ CX02 • CX02
step3 = by-assoc-and (under (CX02) (CX02) (elim_CX20.proved)) Eq.refl Eq.refl

step4 : CX02 • CX02 ≈ ε
step4 = by-assoc-and (under (ε) (ε) (elim_CX02.proved)) Eq.refl Eq.refl

proved : SWAP02 • SWAP02 ≈ ε
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
