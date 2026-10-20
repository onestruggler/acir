{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel152 where

import Examples.Groups.CCX+HH-3qubit.Kit as K using (CCX02 ; CCX12 ; CZ01 ; CZ02 ; CZ12 ; SWAP01 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; r014 ; r019 ; refl ; sym ; trans ; under ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.Tietze.drel159 as drel159
import Examples.Groups.CCX+HH-3qubit.Tietze.drel71 as drel71
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CZ_b as symmetry_CZ_b

step0 : CZ01 • CCX02 ≈ CZ01 • SWAP01 • CCX12 • SWAP01
step0 = by-assoc-and (under (CZ01) (ε) (axiom r014)) Eq.refl Eq.refl

step1 : CZ01 • SWAP01 • CCX12 • SWAP01 ≈ SWAP01 • CZ01 • SWAP01 • SWAP01 • CCX12 • SWAP01
step1 = by-assoc-and (under (ε) (SWAP01 • CCX12 • SWAP01) (symmetry_CZ_b.proved)) Eq.refl Eq.refl

step2 : SWAP01 • CZ01 • SWAP01 • SWAP01 • CCX12 • SWAP01 ≈ SWAP01 • CZ01 • CCX12 • SWAP01
step2 = by-assoc-and (under (SWAP01 • CZ01) (CCX12 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

step3 : SWAP01 • CZ01 • CCX12 • SWAP01 ≈ SWAP01 • CCX12 • CZ12 • CZ01 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (drel159.proved)) Eq.refl Eq.refl

step4 : SWAP01 • CCX12 • CZ12 • CZ01 • SWAP01 ≈ SWAP01 • CCX12 • SWAP01 • CZ02 • SWAP01 • CZ01 • SWAP01
step4 = by-assoc-and (under (SWAP01 • CCX12) (CZ01 • SWAP01) (axiom r019)) Eq.refl Eq.refl

step5 : SWAP01 • CCX12 • SWAP01 • CZ02 • SWAP01 • CZ01 • SWAP01 ≈ SWAP01 • CCX12 • SWAP01 • CZ02 • CZ01
step5 = by-assoc-and (under (SWAP01 • CCX12 • SWAP01 • CZ02) (ε) (sym (symmetry_CZ_b.proved))) Eq.refl Eq.refl

step6 : SWAP01 • CCX12 • SWAP01 • CZ02 • CZ01 ≈ CCX02 • CZ02 • CZ01
step6 = by-assoc-and (under (ε) (CZ02 • CZ01) (sym (axiom r014))) Eq.refl Eq.refl

step7 : CCX02 • CZ02 • CZ01 ≈ CCX02 • CZ01 • CZ02
step7 = by-assoc-and (under (CCX02) (ε) (sym (drel71.proved))) Eq.refl Eq.refl

proved : CZ01 • CCX02 ≈ CCX02 • CZ01 • CZ02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (refl))))))))
