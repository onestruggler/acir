{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel138 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CX01 ; CX02 ; CX20 ; CZ01 ; CZ02 ; CZ12 ; SWAP02 ; SWAP12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r009 ; r018 ; r029 ; r043 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CZ_d as symmetry_CZ_d
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CZ_e as symmetry_CZ_e

step0 : CX20 • CZ01 ≈ SWAP02 • CX02 • SWAP02 • CZ01
step0 = by-assoc-and (under (ε) (CZ01) (axiom r029)) Eq.refl Eq.refl

step1 : SWAP02 • CX02 • SWAP02 • CZ01 ≈ SWAP02 • SWAP12 • CX01 • SWAP12 • SWAP02 • CZ01
step1 = by-assoc-and (under (SWAP02) (SWAP02 • CZ01) (axiom r009)) Eq.refl Eq.refl

step2 : SWAP02 • SWAP12 • CX01 • SWAP12 • SWAP02 • CZ01 ≈ SWAP02 • SWAP12 • CX01 • SWAP12 • SWAP02 • CZ01 • SWAP02 • SWAP02
step2 = by-assoc-and (under (SWAP02 • SWAP12 • CX01 • SWAP12 • SWAP02 • CZ01) (ε) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step3 : SWAP02 • SWAP12 • CX01 • SWAP12 • SWAP02 • CZ01 • SWAP02 • SWAP02 ≈ SWAP02 • SWAP12 • CX01 • SWAP12 • SWAP02 • CZ01 • SWAP02 • SWAP12 • SWAP12 • SWAP02
step3 = by-assoc-and (under (SWAP02 • SWAP12 • CX01 • SWAP12 • SWAP02 • CZ01 • SWAP02) (SWAP02) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step4 : SWAP02 • SWAP12 • CX01 • SWAP12 • SWAP02 • CZ01 • SWAP02 • SWAP12 • SWAP12 • SWAP02 ≈ SWAP02 • SWAP12 • CX01 • SWAP12 • CZ12 • SWAP12 • SWAP12 • SWAP02
step4 = by-assoc-and (under (SWAP02 • SWAP12 • CX01 • SWAP12) (SWAP12 • SWAP12 • SWAP02) (sym (symmetry_CZ_d.proved))) Eq.refl Eq.refl

step5 : SWAP02 • SWAP12 • CX01 • SWAP12 • CZ12 • SWAP12 • SWAP12 • SWAP02 ≈ SWAP02 • SWAP12 • CX01 • CZ12 • SWAP12 • SWAP02
step5 = by-assoc-and (under (SWAP02 • SWAP12 • CX01) (SWAP12 • SWAP02) (sym (symmetry_CZ_e.proved))) Eq.refl Eq.refl

step6 : SWAP02 • SWAP12 • CX01 • CZ12 • SWAP12 • SWAP02 ≈ SWAP02 • SWAP12 • CZ12 • CZ02 • CX01 • SWAP12 • SWAP02
step6 = by-assoc-and (under (SWAP02 • SWAP12) (SWAP12 • SWAP02) (axiom r043)) Eq.refl Eq.refl

step7 : SWAP02 • SWAP12 • CZ12 • CZ02 • CX01 • SWAP12 • SWAP02 ≈ SWAP02 • SWAP12 • CZ12 • SWAP12 • CZ01 • SWAP12 • CX01 • SWAP12 • SWAP02
step7 = by-assoc-and (under (SWAP02 • SWAP12 • CZ12) (CX01 • SWAP12 • SWAP02) (axiom r018)) Eq.refl Eq.refl

step8 : SWAP02 • SWAP12 • CZ12 • SWAP12 • CZ01 • SWAP12 • CX01 • SWAP12 • SWAP02 ≈ SWAP02 • SWAP12 • CZ12 • SWAP12 • CZ01 • CX02 • SWAP02
step8 = by-assoc-and (under (SWAP02 • SWAP12 • CZ12 • SWAP12 • CZ01) (SWAP02) (sym (axiom r009))) Eq.refl Eq.refl

step9 : SWAP02 • SWAP12 • CZ12 • SWAP12 • CZ01 • CX02 • SWAP02 ≈ SWAP02 • CZ12 • CZ01 • CX02 • SWAP02
step9 = by-assoc-and (under (SWAP02) (CZ01 • CX02 • SWAP02) (sym (symmetry_CZ_e.proved))) Eq.refl Eq.refl

step10 : SWAP02 • CZ12 • CZ01 • CX02 • SWAP02 ≈ SWAP02 • CZ12 • CZ01 • SWAP02 • SWAP02 • CX02 • SWAP02
step10 = by-assoc-and (under (SWAP02 • CZ12 • CZ01) (CX02 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step11 : SWAP02 • CZ12 • CZ01 • SWAP02 • SWAP02 • CX02 • SWAP02 ≈ SWAP02 • CZ12 • CZ01 • SWAP02 • CX20
step11 = by-assoc-and (under (SWAP02 • CZ12 • CZ01 • SWAP02) (ε) (sym (axiom r029))) Eq.refl Eq.refl

step12 : SWAP02 • CZ12 • CZ01 • SWAP02 • CX20 ≈ SWAP02 • SWAP02 • CZ01 • SWAP02 • CZ01 • SWAP02 • CX20
step12 = by-assoc-and (under (SWAP02) (CZ01 • SWAP02 • CX20) (symmetry_CZ_d.proved)) Eq.refl Eq.refl

step13 : SWAP02 • SWAP02 • CZ01 • SWAP02 • CZ01 • SWAP02 • CX20 ≈ CZ01 • SWAP02 • CZ01 • SWAP02 • CX20
step13 = by-assoc-and (under (ε) (CZ01 • SWAP02 • CZ01 • SWAP02 • CX20) (elim_SWAP02.proved)) Eq.refl Eq.refl

step14 : CZ01 • SWAP02 • CZ01 • SWAP02 • CX20 ≈ CZ01 • CZ12 • CX20
step14 = by-assoc-and (under (CZ01) (CX20) (sym (symmetry_CZ_d.proved))) Eq.refl Eq.refl

proved : CX20 • CZ01 ≈ CZ01 • CZ12 • CX20
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (trans step11 (trans step12 (trans step13 (trans step14 (refl)))))))))))))))
