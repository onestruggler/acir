{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel115 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX12 ; CZ01 ; CZ12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r024 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel159 as drel159
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ01 as elim_CZ01
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ12 as elim_CZ12

step0 : CZ01 • CZ12 • CCX12 ≈ CZ01 • CZ12 • CCX12 • CZ01 • CZ01
step0 = by-assoc-and (under (CZ01 • CZ12 • CCX12) (ε) (sym (elim_CZ01.proved))) Eq.refl Eq.refl

step1 : CZ01 • CZ12 • CCX12 • CZ01 • CZ01 ≈ CZ01 • CZ12 • CCX12 • CZ01 • CCX12 • CCX12 • CZ01
step1 = by-assoc-and (under (CZ01 • CZ12 • CCX12 • CZ01) (CZ01) (sym (axiom r024))) Eq.refl Eq.refl

step2 : CZ01 • CZ12 • CCX12 • CZ01 • CCX12 • CCX12 • CZ01 ≈ CZ01 • CZ12 • CCX12 • CCX12 • CZ12 • CZ01 • CCX12 • CZ01
step2 = by-assoc-and (under (CZ01 • CZ12 • CCX12) (CCX12 • CZ01) (drel159.proved)) Eq.refl Eq.refl

step3 : CZ01 • CZ12 • CCX12 • CCX12 • CZ12 • CZ01 • CCX12 • CZ01 ≈ CZ01 • CZ12 • CZ12 • CZ01 • CCX12 • CZ01
step3 = by-assoc-and (under (CZ01 • CZ12) (CZ12 • CZ01 • CCX12 • CZ01) (axiom r024)) Eq.refl Eq.refl

step4 : CZ01 • CZ12 • CZ12 • CZ01 • CCX12 • CZ01 ≈ CZ01 • CZ01 • CCX12 • CZ01
step4 = by-assoc-and (under (CZ01) (CZ01 • CCX12 • CZ01) (elim_CZ12.proved)) Eq.refl Eq.refl

step5 : CZ01 • CZ01 • CCX12 • CZ01 ≈ CCX12 • CZ01
step5 = by-assoc-and (under (ε) (CCX12 • CZ01) (elim_CZ01.proved)) Eq.refl Eq.refl

proved : CZ01 • CZ12 • CCX12 ≈ CCX12 • CZ01
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
