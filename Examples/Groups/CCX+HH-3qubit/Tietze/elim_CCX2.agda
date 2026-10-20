{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.elim_CCX2 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX01 ; CCX12 ; SWAP02 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r024 ; r032 ; refl ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02

step0 : CCX01 • CCX01 ≈ CCX01 • SWAP02 • CCX12 • SWAP02
step0 = by-assoc-and (under (CCX01) (ε) (axiom r032)) Eq.refl Eq.refl

step1 : CCX01 • SWAP02 • CCX12 • SWAP02 ≈ SWAP02 • CCX12 • SWAP02 • SWAP02 • CCX12 • SWAP02
step1 = by-assoc-and (under (ε) (SWAP02 • CCX12 • SWAP02) (axiom r032)) Eq.refl Eq.refl

step2 : SWAP02 • CCX12 • SWAP02 • SWAP02 • CCX12 • SWAP02 ≈ SWAP02 • CCX12 • CCX12 • SWAP02
step2 = by-assoc-and (under (SWAP02 • CCX12) (CCX12 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

step3 : SWAP02 • CCX12 • CCX12 • SWAP02 ≈ SWAP02 • SWAP02
step3 = by-assoc-and (under (SWAP02) (SWAP02) (axiom r024)) Eq.refl Eq.refl

step4 : SWAP02 • SWAP02 ≈ ε
step4 = by-assoc-and (under (ε) (ε) (elim_SWAP02.proved)) Eq.refl Eq.refl

proved : CCX01 • CCX01 ≈ ε
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
