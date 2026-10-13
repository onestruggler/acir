{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel93 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel94 as drel94
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_h as symmetry_CX_h

step0 : CCX02 • CX21 ≈ CCX02 • CX21 • SWAP01 • SWAP01
step0 = by-assoc-and (under (CCX02 • CX21) (ε) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step1 : CCX02 • CX21 • SWAP01 • SWAP01 ≈ SWAP01 • CCX12 • SWAP01 • CX21 • SWAP01 • SWAP01
step1 = by-assoc-and (under (ε) (CX21 • SWAP01 • SWAP01) (axiom r014)) Eq.refl Eq.refl

step2 : SWAP01 • CCX12 • SWAP01 • CX21 • SWAP01 • SWAP01 ≈ SWAP01 • CCX12 • CX20 • SWAP01
step2 = by-assoc-and (under (SWAP01 • CCX12) (SWAP01) (sym (symmetry_CX_h.proved))) Eq.refl Eq.refl

step3 : SWAP01 • CCX12 • CX20 • SWAP01 ≈ SWAP01 • CX20 • CCX12 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (drel94.proved)) Eq.refl Eq.refl

step4 : SWAP01 • CX20 • CCX12 • SWAP01 ≈ SWAP01 • SWAP01 • CX21 • SWAP01 • CCX12 • SWAP01
step4 = by-assoc-and (under (SWAP01) (CCX12 • SWAP01) (symmetry_CX_h.proved)) Eq.refl Eq.refl

step5 : SWAP01 • SWAP01 • CX21 • SWAP01 • CCX12 • SWAP01 ≈ CX21 • SWAP01 • CCX12 • SWAP01
step5 = by-assoc-and (under (ε) (CX21 • SWAP01 • CCX12 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

step6 : CX21 • SWAP01 • CCX12 • SWAP01 ≈ CX21 • CCX02
step6 = by-assoc-and (under (CX21) (ε) (sym (axiom r014))) Eq.refl Eq.refl

proved : CCX02 • CX21 ≈ CX21 • CCX02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
