{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel164 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP12 as elim_SWAP12
import Examples.Groups.CCX+HH-3qubit.Tietze.symmetry_CZ_e as symmetry_CZ_e

step0 : CZ02 • CZ12 ≈ CZ02 • SWAP12 • CZ12 • SWAP12
step0 = by-assoc-and (under (CZ02) (ε) (symmetry_CZ_e.proved)) Eq.refl Eq.refl

step1 : CZ02 • SWAP12 • CZ12 • SWAP12 ≈ SWAP12 • CZ01 • SWAP12 • SWAP12 • CZ12 • SWAP12
step1 = by-assoc-and (under (ε) (SWAP12 • CZ12 • SWAP12) (axiom r018)) Eq.refl Eq.refl

step2 : SWAP12 • CZ01 • SWAP12 • SWAP12 • CZ12 • SWAP12 ≈ SWAP12 • CZ01 • CZ12 • SWAP12
step2 = by-assoc-and (under (SWAP12 • CZ01) (CZ12 • SWAP12) (elim_SWAP12.proved)) Eq.refl Eq.refl

step3 : SWAP12 • CZ01 • CZ12 • SWAP12 ≈ SWAP12 • CZ12 • CZ01 • SWAP12
step3 = by-assoc-and (under (SWAP12) (SWAP12) (axiom r040)) Eq.refl Eq.refl

step4 : SWAP12 • CZ12 • CZ01 • SWAP12 ≈ SWAP12 • CZ12 • SWAP12 • SWAP12 • CZ01 • SWAP12
step4 = by-assoc-and (under (SWAP12 • CZ12) (CZ01 • SWAP12) (sym (elim_SWAP12.proved))) Eq.refl Eq.refl

step5 : SWAP12 • CZ12 • SWAP12 • SWAP12 • CZ01 • SWAP12 ≈ CZ12 • SWAP12 • CZ01 • SWAP12
step5 = by-assoc-and (under (ε) (SWAP12 • CZ01 • SWAP12) (sym (symmetry_CZ_e.proved))) Eq.refl Eq.refl

step6 : CZ12 • SWAP12 • CZ01 • SWAP12 ≈ CZ12 • CZ02
step6 = by-assoc-and (under (CZ12) (ε) (sym (axiom r018))) Eq.refl Eq.refl

proved : CZ02 • CZ12 ≈ CZ12 • CZ02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (refl)))))))
