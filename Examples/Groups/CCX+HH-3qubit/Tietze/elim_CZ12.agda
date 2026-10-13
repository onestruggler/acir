{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ12 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ02 as elim_CZ02
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_SWAP01 as elim_SWAP01

step0 : CZ12 • CZ12 ≈ CZ12 • SWAP01 • CZ02 • SWAP01
step0 = by-assoc-and (under (CZ12) (ε) (axiom r019)) Eq.refl Eq.refl

step1 : CZ12 • SWAP01 • CZ02 • SWAP01 ≈ SWAP01 • CZ02 • SWAP01 • SWAP01 • CZ02 • SWAP01
step1 = by-assoc-and (under (ε) (SWAP01 • CZ02 • SWAP01) (axiom r019)) Eq.refl Eq.refl

step2 : SWAP01 • CZ02 • SWAP01 • SWAP01 • CZ02 • SWAP01 ≈ SWAP01 • CZ02 • CZ02 • SWAP01
step2 = by-assoc-and (under (SWAP01 • CZ02) (CZ02 • SWAP01) (elim_SWAP01.proved)) Eq.refl Eq.refl

step3 : SWAP01 • CZ02 • CZ02 • SWAP01 ≈ SWAP01 • SWAP01
step3 = by-assoc-and (under (SWAP01) (SWAP01) (elim_CZ02.proved)) Eq.refl Eq.refl

step4 : SWAP01 • SWAP01 ≈ ε
step4 = by-assoc-and (under (ε) (ε) (elim_SWAP01.proved)) Eq.refl Eq.refl

proved : CZ12 • CZ12 ≈ ε
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (refl)))))
