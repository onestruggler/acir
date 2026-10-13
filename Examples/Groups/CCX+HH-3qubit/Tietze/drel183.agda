{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel183 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel9 as drel9
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CX_i as symmetry_CX_i

step0 : CX21 • CX20 ≈ CX21 • SWAP02 • CX02 • SWAP02
step0 = by-assoc-and (under (CX21) (ε) (axiom r029)) Eq.refl Eq.refl

step1 : CX21 • SWAP02 • CX02 • SWAP02 ≈ SWAP02 • CX01 • SWAP02 • SWAP02 • CX02 • SWAP02
step1 = by-assoc-and (under (ε) (SWAP02 • CX02 • SWAP02) (symmetry_CX_i.proved)) Eq.refl Eq.refl

step2 : SWAP02 • CX01 • SWAP02 • SWAP02 • CX02 • SWAP02 ≈ SWAP02 • CX01 • CX02 • SWAP02
step2 = by-assoc-and (under (SWAP02 • CX01) (CX02 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

step3 : SWAP02 • CX01 • CX02 • SWAP02 ≈ SWAP02 • CX02 • CX01 • SWAP02
step3 = by-assoc-and (under (SWAP02) (SWAP02) (drel9.proved)) Eq.refl Eq.refl

step4 : SWAP02 • CX02 • CX01 • SWAP02 ≈ SWAP02 • CX02 • SWAP02 • SWAP02 • CX01 • SWAP02
step4 = by-assoc-and (under (SWAP02 • CX02) (CX01 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step5 : SWAP02 • CX02 • SWAP02 • SWAP02 • CX01 • SWAP02 ≈ SWAP02 • CX02 • SWAP02 • CX21
step5 = by-assoc-and (under (SWAP02 • CX02 • SWAP02) (ε) (sym (symmetry_CX_i.proved))) Eq.refl Eq.refl

step6 : SWAP02 • CX02 • SWAP02 • CX21 ≈ CX20 • CX21
step6 = by-assoc-and (under (ε) (CX21) (sym (axiom r029))) Eq.refl Eq.refl

proved : CX21 • CX20 ≈ CX20 • CX21
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
