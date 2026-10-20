{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel117 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CZ01 ; CZ02 ; _•_ ; _≈_ ; by-assoc-and ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel152 as drel152
import Examples.Groups.CCX+HH-3qubit.Tietze.drel71 as drel71
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CCX1 as elim_CCX1
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ01 as elim_CZ01
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ02 as elim_CZ02

step0 : CZ01 • CZ02 • CCX02 ≈ CZ02 • CZ01 • CCX02
step0 = by-assoc-and (under (ε) (CCX02) (drel71.proved)) Eq.refl Eq.refl

step1 : CZ02 • CZ01 • CCX02 ≈ CZ02 • CZ01 • CCX02 • CZ01 • CZ01
step1 = by-assoc-and (under (CZ02 • CZ01 • CCX02) (ε) (sym (elim_CZ01.proved))) Eq.refl Eq.refl

step2 : CZ02 • CZ01 • CCX02 • CZ01 • CZ01 ≈ CZ02 • CZ01 • CCX02 • CZ01 • CCX02 • CCX02 • CZ01
step2 = by-assoc-and (under (CZ02 • CZ01 • CCX02 • CZ01) (CZ01) (sym (elim_CCX1.proved))) Eq.refl Eq.refl

step3 : CZ02 • CZ01 • CCX02 • CZ01 • CCX02 • CCX02 • CZ01 ≈ CZ02 • CZ01 • CCX02 • CCX02 • CZ01 • CZ02 • CCX02 • CZ01
step3 = by-assoc-and (under (CZ02 • CZ01 • CCX02) (CCX02 • CZ01) (drel152.proved)) Eq.refl Eq.refl

step4 : CZ02 • CZ01 • CCX02 • CCX02 • CZ01 • CZ02 • CCX02 • CZ01 ≈ CZ02 • CZ01 • CZ01 • CZ02 • CCX02 • CZ01
step4 = by-assoc-and (under (CZ02 • CZ01) (CZ01 • CZ02 • CCX02 • CZ01) (elim_CCX1.proved)) Eq.refl Eq.refl

step5 : CZ02 • CZ01 • CZ01 • CZ02 • CCX02 • CZ01 ≈ CZ02 • CZ02 • CCX02 • CZ01
step5 = by-assoc-and (under (CZ02) (CZ02 • CCX02 • CZ01) (elim_CZ01.proved)) Eq.refl Eq.refl

step6 : CZ02 • CZ02 • CCX02 • CZ01 ≈ CCX02 • CZ01
step6 = by-assoc-and (under (ε) (CCX02 • CZ01) (elim_CZ02.proved)) Eq.refl Eq.refl

proved : CZ01 • CZ02 • CCX02 ≈ CCX02 • CZ01
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
