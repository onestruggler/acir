{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel25 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01

step0 : X1 • CCX02 ≈ X1 • SWAP01 • CCX12 • SWAP01
step0 = by-assoc-and (under (X1) (ε) (axiom r014)) Eq.refl Eq.refl

step1 : X1 • SWAP01 • CCX12 • SWAP01 ≈ SWAP01 • X0 • SWAP01 • SWAP01 • CCX12 • SWAP01
step1 = by-assoc-and (under (ε) (SWAP01 • CCX12 • SWAP01) (axiom r028)) Eq.refl Eq.refl

step2 : SWAP01 • X0 • SWAP01 • SWAP01 • CCX12 • SWAP01 ≈ SWAP01 • X0 • CCX12 • SWAP01
step2 = by-assoc-and (under (SWAP01 • X0) (CCX12 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

step3 : SWAP01 • X0 • CCX12 • SWAP01 ≈ SWAP01 • CCX12 • X0 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (axiom r037)) Eq.refl Eq.refl

step4 : SWAP01 • CCX12 • X0 • SWAP01 ≈ SWAP01 • CCX12 • SWAP01 • SWAP01 • X0 • SWAP01
step4 = by-assoc-and (under (SWAP01 • CCX12) (X0 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step5 : SWAP01 • CCX12 • SWAP01 • SWAP01 • X0 • SWAP01 ≈ CCX02 • SWAP01 • X0 • SWAP01
step5 = by-assoc-and (under (ε) (SWAP01 • X0 • SWAP01) (sym (axiom r014))) Eq.refl Eq.refl

step6 : CCX02 • SWAP01 • X0 • SWAP01 ≈ CCX02 • X1
step6 = by-assoc-and (under (CCX02) (ε) (sym (axiom r028))) Eq.refl Eq.refl

proved : X1 • CCX02 ≈ CCX02 • X1
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
