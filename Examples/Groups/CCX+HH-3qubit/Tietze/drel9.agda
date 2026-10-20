{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel9 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX02 ; CX21 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel110 as drel110
import Examples.Groups.CCX+HH-3qubit.Tietze.drel134 as drel134
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX02 as elim_CX02
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX21 as elim_CX21

step0 : CX01 • CX02 ≈ CX21 • CX21 • CX01 • CX02
step0 = by-assoc-and (under (ε) (CX01 • CX02) (sym (elim_CX21.proved))) Eq.refl Eq.refl

step1 : CX21 • CX21 • CX01 • CX02 ≈ CX21 • CX02 • CX02 • CX21 • CX01 • CX02
step1 = by-assoc-and (under (CX21) (CX21 • CX01 • CX02) (sym (elim_CX02.proved))) Eq.refl Eq.refl

step2 : CX21 • CX02 • CX02 • CX21 • CX01 • CX02 ≈ CX21 • CX02 • CX21 • CX02 • CX02
step2 = by-assoc-and (under (CX21 • CX02) (CX02) (sym (drel110.proved))) Eq.refl Eq.refl

step3 : CX21 • CX02 • CX21 • CX02 • CX02 ≈ CX21 • CX02 • CX21
step3 = by-assoc-and (under (CX21 • CX02 • CX21) (ε) (elim_CX02.proved)) Eq.refl Eq.refl

step4 : CX21 • CX02 • CX21 ≈ CX21 • CX21 • CX02 • CX01
step4 = by-assoc-and (under (CX21) (ε) (drel134.proved)) Eq.refl Eq.refl

step5 : CX21 • CX21 • CX02 • CX01 ≈ CX02 • CX01
step5 = by-assoc-and (under (ε) (CX02 • CX01) (elim_CX21.proved)) Eq.refl Eq.refl

proved : CX01 • CX02 ≈ CX02 • CX01
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
