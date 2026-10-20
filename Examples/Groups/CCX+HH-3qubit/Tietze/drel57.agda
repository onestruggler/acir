{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel57 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX12 ; CZ02 ; CZ12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r024 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel150 as drel150
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ02 as elim_CZ02
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ12 as elim_CZ12

step0 : CCX12 • CZ02 ≈ CCX12 • CZ02 • CCX12 • CCX12
step0 = by-assoc-and (under (CCX12 • CZ02) (ε) (sym (axiom r024))) Eq.refl Eq.refl

step1 : CCX12 • CZ02 • CCX12 • CCX12 ≈ CCX12 • CZ02 • CCX12 • CZ12 • CZ12 • CCX12
step1 = by-assoc-and (under (CCX12 • CZ02 • CCX12) (CCX12) (sym (elim_CZ12.proved))) Eq.refl Eq.refl

step2 : CCX12 • CZ02 • CCX12 • CZ12 • CZ12 • CCX12 ≈ CCX12 • CZ02 • CCX12 • CZ12 • CZ02 • CZ02 • CZ12 • CCX12
step2 = by-assoc-and (under (CCX12 • CZ02 • CCX12 • CZ12) (CZ12 • CCX12) (sym (elim_CZ02.proved))) Eq.refl Eq.refl

step3 : CCX12 • CZ02 • CCX12 • CZ12 • CZ02 • CZ02 • CZ12 • CCX12 ≈ CCX12 • CZ02 • CZ02 • CCX12 • CZ02 • CZ12 • CCX12
step3 = by-assoc-and (under (CCX12 • CZ02) (CZ02 • CZ12 • CCX12) (sym (drel150.proved))) Eq.refl Eq.refl

step4 : CCX12 • CZ02 • CZ02 • CCX12 • CZ02 • CZ12 • CCX12 ≈ CCX12 • CCX12 • CZ02 • CZ12 • CCX12
step4 = by-assoc-and (under (CCX12) (CCX12 • CZ02 • CZ12 • CCX12) (elim_CZ02.proved)) Eq.refl Eq.refl

step5 : CCX12 • CCX12 • CZ02 • CZ12 • CCX12 ≈ CZ02 • CZ12 • CCX12
step5 = by-assoc-and (under (ε) (CZ02 • CZ12 • CCX12) (axiom r024)) Eq.refl Eq.refl

proved : CCX12 • CZ02 ≈ CZ02 • CZ12 • CCX12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
