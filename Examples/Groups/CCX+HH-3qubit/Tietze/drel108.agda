{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel108 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX12 ; CZ01 ; CZ02 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel139 as drel139
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX12 as elim_CX12
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ01 as elim_CZ01
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ02 as elim_CZ02

step0 : CZ02 • CX12 ≈ CX12 • CX12 • CZ02 • CX12
step0 = by-assoc-and (under (ε) (CZ02 • CX12) (sym (elim_CX12.proved))) Eq.refl Eq.refl

step1 : CX12 • CX12 • CZ02 • CX12 ≈ CX12 • CZ01 • CZ01 • CX12 • CZ02 • CX12
step1 = by-assoc-and (under (CX12) (CX12 • CZ02 • CX12) (sym (elim_CZ01.proved))) Eq.refl Eq.refl

step2 : CX12 • CZ01 • CZ01 • CX12 • CZ02 • CX12 ≈ CX12 • CZ01 • CZ02 • CZ02 • CZ01 • CX12 • CZ02 • CX12
step2 = by-assoc-and (under (CX12 • CZ01) (CZ01 • CX12 • CZ02 • CX12) (sym (elim_CZ02.proved))) Eq.refl Eq.refl

step3 : CX12 • CZ01 • CZ02 • CZ02 • CZ01 • CX12 • CZ02 • CX12 ≈ CX12 • CZ01 • CZ02 • CX12 • CZ02 • CZ02 • CX12
step3 = by-assoc-and (under (CX12 • CZ01 • CZ02) (CZ02 • CX12) (sym (drel139.proved))) Eq.refl Eq.refl

step4 : CX12 • CZ01 • CZ02 • CX12 • CZ02 • CZ02 • CX12 ≈ CX12 • CZ01 • CZ02 • CX12 • CX12
step4 = by-assoc-and (under (CX12 • CZ01 • CZ02 • CX12) (CX12) (elim_CZ02.proved)) Eq.refl Eq.refl

step5 : CX12 • CZ01 • CZ02 • CX12 • CX12 ≈ CX12 • CZ01 • CZ02
step5 = by-assoc-and (under (CX12 • CZ01 • CZ02) (ε) (elim_CX12.proved)) Eq.refl Eq.refl

proved : CZ02 • CX12 ≈ CX12 • CZ01 • CZ02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
