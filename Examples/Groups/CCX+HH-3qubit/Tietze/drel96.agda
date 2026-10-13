{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel96 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_SWAP_c as bifunct_X_SWAP_c
import Examples.Groups.CCX+HH-3qubit.Tietze.drel131 as drel131
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02

step0 : X1 • CCX01 ≈ X1 • SWAP02 • CCX12 • SWAP02
step0 = by-assoc-and (under (X1) (ε) (axiom r032)) Eq.refl Eq.refl

step1 : X1 • SWAP02 • CCX12 • SWAP02 ≈ SWAP02 • X1 • CCX12 • SWAP02
step1 = by-assoc-and (under (ε) (CCX12 • SWAP02) (bifunct_X_SWAP_c.proved)) Eq.refl Eq.refl

step2 : SWAP02 • X1 • CCX12 • SWAP02 ≈ SWAP02 • CCX12 • CX20 • X1 • SWAP02
step2 = by-assoc-and (under (SWAP02) (SWAP02) (drel131.proved)) Eq.refl Eq.refl

step3 : SWAP02 • CCX12 • CX20 • X1 • SWAP02 ≈ SWAP02 • CCX12 • CX20 • SWAP02 • X1
step3 = by-assoc-and (under (SWAP02 • CCX12 • CX20) (ε) (bifunct_X_SWAP_c.proved)) Eq.refl Eq.refl

step4 : SWAP02 • CCX12 • CX20 • SWAP02 • X1 ≈ SWAP02 • CCX12 • SWAP02 • CX02 • SWAP02 • SWAP02 • X1
step4 = by-assoc-and (under (SWAP02 • CCX12) (SWAP02 • X1) (axiom r029)) Eq.refl Eq.refl

step5 : SWAP02 • CCX12 • SWAP02 • CX02 • SWAP02 • SWAP02 • X1 ≈ SWAP02 • CCX12 • SWAP02 • CX02 • X1
step5 = by-assoc-and (under (SWAP02 • CCX12 • SWAP02 • CX02) (X1) (elim_SWAP02.proved)) Eq.refl Eq.refl

step6 : SWAP02 • CCX12 • SWAP02 • CX02 • X1 ≈ CCX01 • CX02 • X1
step6 = by-assoc-and (under (ε) (CX02 • X1) (sym (axiom r032))) Eq.refl Eq.refl

proved : X1 • CCX01 ≈ CCX01 • CX02 • X1
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
