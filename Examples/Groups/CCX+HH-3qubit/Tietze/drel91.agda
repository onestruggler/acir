{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel91 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel94 as drel94
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02

step0 : CCX01 • CX02 ≈ SWAP02 • CCX12 • SWAP02 • CX02
step0 = by-assoc-and (under (ε) (CX02) (axiom r032)) Eq.refl Eq.refl

step1 : SWAP02 • CCX12 • SWAP02 • CX02 ≈ SWAP02 • CCX12 • SWAP02 • CX02 • SWAP02 • SWAP02
step1 = by-assoc-and (under (SWAP02 • CCX12 • SWAP02 • CX02) (ε) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step2 : SWAP02 • CCX12 • SWAP02 • CX02 • SWAP02 • SWAP02 ≈ SWAP02 • CCX12 • CX20 • SWAP02
step2 = by-assoc-and (under (SWAP02 • CCX12) (SWAP02) (sym (axiom r029))) Eq.refl Eq.refl

step3 : SWAP02 • CCX12 • CX20 • SWAP02 ≈ SWAP02 • CX20 • CCX12 • SWAP02
step3 = by-assoc-and (under (SWAP02) (SWAP02) (drel94.proved)) Eq.refl Eq.refl

step4 : SWAP02 • CX20 • CCX12 • SWAP02 ≈ SWAP02 • SWAP02 • CX02 • SWAP02 • CCX12 • SWAP02
step4 = by-assoc-and (under (SWAP02) (CCX12 • SWAP02) (axiom r029)) Eq.refl Eq.refl

step5 : SWAP02 • SWAP02 • CX02 • SWAP02 • CCX12 • SWAP02 ≈ SWAP02 • SWAP02 • CX02 • CCX01
step5 = by-assoc-and (under (SWAP02 • SWAP02 • CX02) (ε) (sym (axiom r032))) Eq.refl Eq.refl

step6 : SWAP02 • SWAP02 • CX02 • CCX01 ≈ CX02 • CCX01
step6 = by-assoc-and (under (ε) (CX02 • CCX01) (elim_SWAP02.proved)) Eq.refl Eq.refl

proved : CCX01 • CX02 ≈ CX02 • CCX01
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
