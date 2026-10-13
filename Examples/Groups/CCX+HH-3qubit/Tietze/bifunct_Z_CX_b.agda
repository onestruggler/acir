{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.bifunct_Z_CX_b where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel112 as drel112
import Examples.Groups.CCX+HH-3qubit.Tietze.drel163 as drel163
import Examples.Groups.CCX+HH-3qubit.Tietze.drel165 as drel165
import Examples.Groups.CCX+HH-3qubit.Tietze.drel9 as drel9
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX02 as elim_CX02

step0 : Z0 • CX12 ≈ CZ01 • CX01 • CZ01 • CX01 • CX12
step0 = by-assoc-and (under (ε) (CX12) (axiom r003)) Eq.refl Eq.refl

step1 : CZ01 • CX01 • CZ01 • CX01 • CX12 ≈ CZ01 • CX01 • CZ01 • CX12 • CX01 • CX02
step1 = by-assoc-and (under (CZ01 • CX01 • CZ01) (ε) (drel112.proved)) Eq.refl Eq.refl

step2 : CZ01 • CX01 • CZ01 • CX12 • CX01 • CX02 ≈ CZ01 • CX01 • CX12 • CZ01 • CX01 • CX02
step2 = by-assoc-and (under (CZ01 • CX01) (CX01 • CX02) (sym (drel165.proved))) Eq.refl Eq.refl

step3 : CZ01 • CX01 • CX12 • CZ01 • CX01 • CX02 ≈ CZ01 • CX12 • CX01 • CX02 • CZ01 • CX01 • CX02
step3 = by-assoc-and (under (CZ01) (CZ01 • CX01 • CX02) (drel112.proved)) Eq.refl Eq.refl

step4 : CZ01 • CX12 • CX01 • CX02 • CZ01 • CX01 • CX02 ≈ CX12 • CZ01 • CX01 • CX02 • CZ01 • CX01 • CX02
step4 = by-assoc-and (under (ε) (CX01 • CX02 • CZ01 • CX01 • CX02) (sym (drel165.proved))) Eq.refl Eq.refl

step5 : CX12 • CZ01 • CX01 • CX02 • CZ01 • CX01 • CX02 ≈ CX12 • CZ01 • CX01 • CZ01 • CX02 • CX01 • CX02
step5 = by-assoc-and (under (CX12 • CZ01 • CX01) (CX01 • CX02) (drel163.proved)) Eq.refl Eq.refl

step6 : CX12 • CZ01 • CX01 • CZ01 • CX02 • CX01 • CX02 ≈ CX12 • CZ01 • CX01 • CZ01 • CX01 • CX02 • CX02
step6 = by-assoc-and (under (CX12 • CZ01 • CX01 • CZ01) (CX02) (sym (drel9.proved))) Eq.refl Eq.refl

step7 : CX12 • CZ01 • CX01 • CZ01 • CX01 • CX02 • CX02 ≈ CX12 • CZ01 • CX01 • CZ01 • CX01
step7 = by-assoc-and (under (CX12 • CZ01 • CX01 • CZ01 • CX01) (ε) (elim_CX02.proved)) Eq.refl Eq.refl

step8 : CX12 • CZ01 • CX01 • CZ01 • CX01 ≈ CX12 • Z0
step8 = by-assoc-and (under (CX12) (ε) (sym (axiom r003))) Eq.refl Eq.refl

proved : Z0 • CX12 ≈ CX12 • Z0
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (refl)))))))))
