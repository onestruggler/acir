{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel26 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02

step0 : X2 • CCX01 ≈ X2 • SWAP02 • CCX12 • SWAP02
step0 = by-assoc-and (under (X2) (ε) (axiom r032)) Eq.refl Eq.refl

step1 : X2 • SWAP02 • CCX12 • SWAP02 ≈ SWAP02 • X0 • SWAP02 • SWAP02 • CCX12 • SWAP02
step1 = by-assoc-and (under (ε) (SWAP02 • CCX12 • SWAP02) (axiom r015)) Eq.refl Eq.refl

step2 : SWAP02 • X0 • SWAP02 • SWAP02 • CCX12 • SWAP02 ≈ SWAP02 • X0 • CCX12 • SWAP02
step2 = by-assoc-and (under (SWAP02 • X0) (CCX12 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

step3 : SWAP02 • X0 • CCX12 • SWAP02 ≈ SWAP02 • CCX12 • X0 • SWAP02
step3 = by-assoc-and (under (SWAP02) (SWAP02) (axiom r037)) Eq.refl Eq.refl

step4 : SWAP02 • CCX12 • X0 • SWAP02 ≈ SWAP02 • CCX12 • SWAP02 • SWAP02 • X0 • SWAP02
step4 = by-assoc-and (under (SWAP02 • CCX12) (X0 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step5 : SWAP02 • CCX12 • SWAP02 • SWAP02 • X0 • SWAP02 ≈ CCX01 • SWAP02 • X0 • SWAP02
step5 = by-assoc-and (under (ε) (SWAP02 • X0 • SWAP02) (sym (axiom r032))) Eq.refl Eq.refl

step6 : CCX01 • SWAP02 • X0 • SWAP02 ≈ CCX01 • X2
step6 = by-assoc-and (under (CCX01) (ε) (sym (axiom r015))) Eq.refl Eq.refl

proved : X2 • CCX01 ≈ CCX01 • X2
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
