{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.elim_CCX1 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; SWAP01 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r014 ; r024 ; refl ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01

step0 : CCX02 • CCX02 ≈ CCX02 • SWAP01 • CCX12 • SWAP01
step0 = by-assoc-and (under (CCX02) (ε) (axiom r014)) Eq.refl Eq.refl

step1 : CCX02 • SWAP01 • CCX12 • SWAP01 ≈ SWAP01 • CCX12 • SWAP01 • SWAP01 • CCX12 • SWAP01
step1 = by-assoc-and (under (ε) (SWAP01 • CCX12 • SWAP01) (axiom r014)) Eq.refl Eq.refl

step2 : SWAP01 • CCX12 • SWAP01 • SWAP01 • CCX12 • SWAP01 ≈ SWAP01 • CCX12 • CCX12 • SWAP01
step2 = by-assoc-and (under (SWAP01 • CCX12) (CCX12 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

step3 : SWAP01 • CCX12 • CCX12 • SWAP01 ≈ SWAP01 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (axiom r024)) Eq.refl Eq.refl

step4 : SWAP01 • SWAP01 ≈ ε
step4 = by-assoc-and (under (ε) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

proved : CCX02 • CCX02 ≈ ε
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
