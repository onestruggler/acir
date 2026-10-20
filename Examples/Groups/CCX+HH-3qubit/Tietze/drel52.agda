{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel52 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; K01 ; X0 ; Z0 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r025 ; r037 ; r041 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel85 as drel85

step0 : Z0 • CCX02 ≈ K01 • K01 • Z0 • CCX02
step0 = by-assoc-and (under (ε) (Z0 • CCX02) (sym (axiom r025))) Eq.refl Eq.refl

step1 : K01 • K01 • Z0 • CCX02 ≈ K01 • X0 • K01 • CCX02
step1 = by-assoc-and (under (K01) (CCX02) (axiom r041)) Eq.refl Eq.refl

step2 : K01 • X0 • K01 • CCX02 ≈ K01 • X0 • CCX12 • K01
step2 = by-assoc-and (under (K01 • X0) (ε) (sym (drel85.proved))) Eq.refl Eq.refl

step3 : K01 • X0 • CCX12 • K01 ≈ K01 • CCX12 • X0 • K01
step3 = by-assoc-and (under (K01) (K01) (axiom r037)) Eq.refl Eq.refl

step4 : K01 • CCX12 • X0 • K01 ≈ K01 • CCX12 • K01 • Z0
step4 = by-assoc-and (under (K01 • CCX12) (ε) (sym (axiom r041))) Eq.refl Eq.refl

step5 : K01 • CCX12 • K01 • Z0 ≈ K01 • K01 • CCX02 • Z0
step5 = by-assoc-and (under (K01) (Z0) (drel85.proved)) Eq.refl Eq.refl

step6 : K01 • K01 • CCX02 • Z0 ≈ CCX02 • Z0
step6 = by-assoc-and (under (ε) (CCX02 • Z0) (axiom r025)) Eq.refl Eq.refl

proved : Z0 • CCX02 ≈ CCX02 • Z0
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
