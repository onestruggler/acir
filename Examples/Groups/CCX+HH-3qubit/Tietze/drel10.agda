{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel10 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX10 ; CX12 ; CX20 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel135 as drel135
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX10 as elim_CX10
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX12 as elim_CX12
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX20 as elim_CX20

step0 : CX10 • CX12 ≈ CX10 • CX12 • CX20 • CX20
step0 = by-assoc-and (under (CX10 • CX12) (ε) (sym (elim_CX20.proved))) Eq.refl Eq.refl

step1 : CX10 • CX12 • CX20 • CX20 ≈ CX10 • CX12 • CX20 • CX12 • CX12 • CX20
step1 = by-assoc-and (under (CX10 • CX12 • CX20) (CX20) (sym (elim_CX12.proved))) Eq.refl Eq.refl

step2 : CX10 • CX12 • CX20 • CX12 • CX12 • CX20 ≈ CX10 • CX12 • CX20 • CX12 • CX20 • CX20 • CX12 • CX20
step2 = by-assoc-and (under (CX10 • CX12 • CX20 • CX12) (CX12 • CX20) (sym (elim_CX20.proved))) Eq.refl Eq.refl

step3 : CX10 • CX12 • CX20 • CX12 • CX20 • CX20 • CX12 • CX20 ≈ CX10 • CX12 • CX20 • CX20 • CX12 • CX10 • CX20 • CX12 • CX20
step3 = by-assoc-and (under (CX10 • CX12 • CX20) (CX20 • CX12 • CX20) (drel135.proved)) Eq.refl Eq.refl

step4 : CX10 • CX12 • CX20 • CX20 • CX12 • CX10 • CX20 • CX12 • CX20 ≈ CX10 • CX12 • CX12 • CX10 • CX20 • CX12 • CX20
step4 = by-assoc-and (under (CX10 • CX12) (CX12 • CX10 • CX20 • CX12 • CX20) (elim_CX20.proved)) Eq.refl Eq.refl

step5 : CX10 • CX12 • CX12 • CX10 • CX20 • CX12 • CX20 ≈ CX10 • CX10 • CX20 • CX12 • CX20
step5 = by-assoc-and (under (CX10) (CX10 • CX20 • CX12 • CX20) (elim_CX12.proved)) Eq.refl Eq.refl

step6 : CX10 • CX10 • CX20 • CX12 • CX20 ≈ CX20 • CX12 • CX20
step6 = by-assoc-and (under (ε) (CX20 • CX12 • CX20) (elim_CX10.proved)) Eq.refl Eq.refl

step7 : CX20 • CX12 • CX20 ≈ CX20 • CX20 • CX12 • CX10
step7 = by-assoc-and (under (CX20) (ε) (drel135.proved)) Eq.refl Eq.refl

step8 : CX20 • CX20 • CX12 • CX10 ≈ CX12 • CX10
step8 = by-assoc-and (under (ε) (CX12 • CX10) (elim_CX20.proved)) Eq.refl Eq.refl

proved : CX10 • CX12 ≈ CX12 • CX10
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))
