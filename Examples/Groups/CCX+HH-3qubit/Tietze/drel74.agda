{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel74 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel48 as drel48
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP02 as elim_SWAP02
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CZ_a as symmetry_CZ_a

step0 : K01 • CX20 ≈ K01 • SWAP02 • CX02 • SWAP02
step0 = by-assoc-and (under (K01) (ε) (axiom r029)) Eq.refl Eq.refl

step1 : K01 • SWAP02 • CX02 • SWAP02 ≈ SWAP02 • K12 • SWAP02 • SWAP02 • CX02 • SWAP02
step1 = by-assoc-and (under (ε) (SWAP02 • CX02 • SWAP02) (axiom r011)) Eq.refl Eq.refl

step2 : SWAP02 • K12 • SWAP02 • SWAP02 • CX02 • SWAP02 ≈ SWAP02 • K12 • CX02 • SWAP02
step2 = by-assoc-and (under (SWAP02 • K12) (CX02 • SWAP02) (elim_SWAP02.proved)) Eq.refl Eq.refl

step3 : SWAP02 • K12 • CX02 • SWAP02 ≈ SWAP02 • CZ02 • K12 • SWAP02
step3 = by-assoc-and (under (SWAP02) (SWAP02) (sym (drel48.proved))) Eq.refl Eq.refl

step4 : SWAP02 • CZ02 • K12 • SWAP02 ≈ SWAP02 • CZ02 • SWAP02 • SWAP02 • K12 • SWAP02
step4 = by-assoc-and (under (SWAP02 • CZ02) (K12 • SWAP02) (sym (elim_SWAP02.proved))) Eq.refl Eq.refl

step5 : SWAP02 • CZ02 • SWAP02 • SWAP02 • K12 • SWAP02 ≈ SWAP02 • CZ02 • SWAP02 • K01
step5 = by-assoc-and (under (SWAP02 • CZ02 • SWAP02) (ε) (sym (axiom r011))) Eq.refl Eq.refl

step6 : SWAP02 • CZ02 • SWAP02 • K01 ≈ CZ02 • K01
step6 = by-assoc-and (under (ε) (K01) (sym (symmetry_CZ_a.proved))) Eq.refl Eq.refl

proved : K01 • CX20 ≈ CZ02 • K01
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
