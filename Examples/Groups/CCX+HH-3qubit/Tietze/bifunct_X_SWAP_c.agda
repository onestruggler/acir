{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_SWAP_c where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_CX_e as bifunct_X_CX_e
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_CX_f as bifunct_X_CX_f

step0 : X1 • SWAP02 ≈ X1 • CX02 • CX20 • CX02
step0 = by-assoc-and (under (X1) (ε) (axiom r010)) Eq.refl Eq.refl

step1 : X1 • CX02 • CX20 • CX02 ≈ CX02 • X1 • CX20 • CX02
step1 = by-assoc-and (under (ε) (CX20 • CX02) (sym (bifunct_X_CX_e.proved))) Eq.refl Eq.refl

step2 : CX02 • X1 • CX20 • CX02 ≈ CX02 • CX20 • X1 • CX02
step2 = by-assoc-and (under (CX02) (CX02) (sym (bifunct_X_CX_f.proved))) Eq.refl Eq.refl

step3 : CX02 • CX20 • X1 • CX02 ≈ CX02 • CX20 • CX02 • X1
step3 = by-assoc-and (under (CX02 • CX20) (ε) (sym (bifunct_X_CX_e.proved))) Eq.refl Eq.refl

step4 : CX02 • CX20 • CX02 • X1 ≈ SWAP02 • X1
step4 = by-assoc-and (under (ε) (X1) (sym (axiom r010))) Eq.refl Eq.refl

proved : X1 • SWAP02 ≈ SWAP02 • X1
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
