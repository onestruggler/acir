{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel150 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX12 ; CZ01 ; CZ02 ; CZ12 ; SWAP12 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r018 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel159 as drel159
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CCX_g as symmetry_CCX_g
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CZ_e as symmetry_CZ_e

step0 : CZ02 • CCX12 ≈ CZ02 • SWAP12 • CCX12 • SWAP12
step0 = by-assoc-and (under (CZ02) (ε) (symmetry_CCX_g.proved)) Eq.refl Eq.refl

step1 : CZ02 • SWAP12 • CCX12 • SWAP12 ≈ SWAP12 • CZ01 • SWAP12 • SWAP12 • CCX12 • SWAP12
step1 = by-assoc-and (under (ε) (SWAP12 • CCX12 • SWAP12) (axiom r018)) Eq.refl Eq.refl

step2 : SWAP12 • CZ01 • SWAP12 • SWAP12 • CCX12 • SWAP12 ≈ SWAP12 • CZ01 • CCX12 • SWAP12
step2 = by-assoc-and (under (SWAP12 • CZ01) (CCX12 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

step3 : SWAP12 • CZ01 • CCX12 • SWAP12 ≈ SWAP12 • CCX12 • CZ12 • CZ01 • SWAP12
step3 = by-assoc-and (under (SWAP12) (SWAP12) (drel159.proved)) Eq.refl Eq.refl

step4 : SWAP12 • CCX12 • CZ12 • CZ01 • SWAP12 ≈ SWAP12 • CCX12 • SWAP12 • CZ12 • SWAP12 • CZ01 • SWAP12
step4 = by-assoc-and (under (SWAP12 • CCX12) (CZ01 • SWAP12) (symmetry_CZ_e.proved)) Eq.refl Eq.refl

step5 : SWAP12 • CCX12 • SWAP12 • CZ12 • SWAP12 • CZ01 • SWAP12 ≈ SWAP12 • CCX12 • SWAP12 • CZ12 • CZ02
step5 = by-assoc-and (under (SWAP12 • CCX12 • SWAP12 • CZ12) (ε) (sym (axiom r018))) Eq.refl Eq.refl

step6 : SWAP12 • CCX12 • SWAP12 • CZ12 • CZ02 ≈ CCX12 • CZ12 • CZ02
step6 = by-assoc-and (under (ε) (CZ12 • CZ02) (sym (symmetry_CCX_g.proved))) Eq.refl Eq.refl

proved : CZ02 • CCX12 ≈ CCX12 • CZ12 • CZ02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
