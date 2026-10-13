{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel40 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel51 as drel51
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CCX_c as symmetry_CCX_c

step0 : Z0 • CCX01 ≈ Z0 • SWAP01 • CCX01 • SWAP01
step0 = by-assoc-and (under (Z0) (ε) (symmetry_CCX_c.proved)) Eq.refl Eq.refl

step1 : Z0 • SWAP01 • CCX01 • SWAP01 ≈ SWAP01 • SWAP01 • Z0 • SWAP01 • CCX01 • SWAP01
step1 = by-assoc-and (under (ε) (Z0 • SWAP01 • CCX01 • SWAP01) (sym (elim_SWAP01.proved))) Eq.refl Eq.refl

step2 : SWAP01 • SWAP01 • Z0 • SWAP01 • CCX01 • SWAP01 ≈ SWAP01 • Z1 • CCX01 • SWAP01
step2 = by-assoc-and (under (SWAP01) (CCX01 • SWAP01) (sym (axiom r034))) Eq.refl Eq.refl

step3 : SWAP01 • Z1 • CCX01 • SWAP01 ≈ SWAP01 • CCX01 • Z1 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (drel51.proved)) Eq.refl Eq.refl

step4 : SWAP01 • CCX01 • Z1 • SWAP01 ≈ SWAP01 • CCX01 • SWAP01 • Z0 • SWAP01 • SWAP01
step4 = by-assoc-and (under (SWAP01 • CCX01) (SWAP01) (axiom r034)) Eq.refl Eq.refl

step5 : SWAP01 • CCX01 • SWAP01 • Z0 • SWAP01 • SWAP01 ≈ SWAP01 • CCX01 • SWAP01 • Z0
step5 = by-assoc-and (under (SWAP01 • CCX01 • SWAP01 • Z0) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

step6 : SWAP01 • CCX01 • SWAP01 • Z0 ≈ CCX01 • Z0
step6 = by-assoc-and (under (ε) (Z0) (sym (symmetry_CCX_c.proved))) Eq.refl Eq.refl

proved : Z0 • CCX01 ≈ CCX01 • Z0
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
