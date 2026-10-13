{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CZ_d where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CZ_b as symmetry_CZ_b
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_SWAP02 as symmetry_SWAP02

step0 : CZ12 ≈ SWAP01 • CZ02 • SWAP01
step0 = by-assoc-and (under (ε) (ε) (axiom r019)) Eq.refl Eq.refl

step1 : SWAP01 • CZ02 • SWAP01 ≈ SWAP01 • SWAP12 • CZ01 • SWAP12 • SWAP01
step1 = by-assoc-and (under (SWAP01) (SWAP01) (axiom r018)) Eq.refl Eq.refl

step2 : SWAP01 • SWAP12 • CZ01 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • SWAP01 • CZ01 • SWAP01 • SWAP12 • SWAP01
step2 = by-assoc-and (under (SWAP01 • SWAP12) (SWAP12 • SWAP01) (symmetry_CZ_b.proved)) Eq.refl Eq.refl

step3 : SWAP01 • SWAP12 • SWAP01 • CZ01 • SWAP01 • SWAP12 • SWAP01 ≈ SWAP01 • SWAP12 • SWAP01 • CZ01 • SWAP02
step3 = by-assoc-and (under (SWAP01 • SWAP12 • SWAP01 • CZ01) (ε) (sym (symmetry_SWAP02.proved))) Eq.refl Eq.refl

step4 : SWAP01 • SWAP12 • SWAP01 • CZ01 • SWAP02 ≈ SWAP02 • CZ01 • SWAP02
step4 = by-assoc-and (under (ε) (CZ01 • SWAP02) (sym (symmetry_SWAP02.proved))) Eq.refl Eq.refl

proved : CZ12 ≈ SWAP02 • CZ01 • SWAP02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
