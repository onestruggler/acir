{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_b where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (SWAP12 ; X0 ; X1 ; X2 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Proofs.X0X1 as X0X1
import Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_X_SWAP_a as bifunct_X_SWAP_a
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_X_c as symmetry_X_c

step0 : X0 • X2 ≈ X0 • SWAP12 • X1 • SWAP12
step0 = by-assoc-and (under (X0) (ε) (symmetry_X_c.proved)) Eq.refl Eq.refl

step1 : X0 • SWAP12 • X1 • SWAP12 ≈ SWAP12 • X0 • X1 • SWAP12
step1 = by-assoc-and (under (ε) (X1 • SWAP12) (bifunct_X_SWAP_a.proved)) Eq.refl Eq.refl

step2 : SWAP12 • X0 • X1 • SWAP12 ≈ SWAP12 • X1 • X0 • SWAP12
step2 = by-assoc-and (under (SWAP12) (SWAP12) (X0X1.proved)) Eq.refl Eq.refl

step3 : SWAP12 • X1 • X0 • SWAP12 ≈ SWAP12 • X1 • SWAP12 • X0
step3 = by-assoc-and (under (SWAP12 • X1) (ε) (bifunct_X_SWAP_a.proved)) Eq.refl Eq.refl

step4 : SWAP12 • X1 • SWAP12 • X0 ≈ X2 • X0
step4 = by-assoc-and (under (ε) (X0) (sym (symmetry_X_c.proved))) Eq.refl Eq.refl

proved : X0 • X2 ≈ X2 • X0
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
