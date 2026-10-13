{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel187 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel170 as drel170
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CCX2 as elim_CCX2
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ01 as elim_CZ01
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ12 as elim_CZ12

step0 : CZ12 • CZ01 • CCX01 ≈ CCX01 • CCX01 • CZ12 • CZ01 • CCX01
step0 = by-assoc-and (under (ε) (CZ12 • CZ01 • CCX01) (sym (elim_CCX2.proved))) Eq.refl Eq.refl

step1 : CCX01 • CCX01 • CZ12 • CZ01 • CCX01 ≈ CCX01 • CZ12 • CZ12 • CCX01 • CZ12 • CZ01 • CCX01
step1 = by-assoc-and (under (CCX01) (CCX01 • CZ12 • CZ01 • CCX01) (sym (elim_CZ12.proved))) Eq.refl Eq.refl

step2 : CCX01 • CZ12 • CZ12 • CCX01 • CZ12 • CZ01 • CCX01 ≈ CCX01 • CZ12 • CCX01 • CZ01 • CZ12 • CZ12 • CZ01 • CCX01
step2 = by-assoc-and (under (CCX01 • CZ12) (CZ12 • CZ01 • CCX01) (drel170.proved)) Eq.refl Eq.refl

step3 : CCX01 • CZ12 • CCX01 • CZ01 • CZ12 • CZ12 • CZ01 • CCX01 ≈ CCX01 • CZ12 • CCX01 • CZ01 • CZ01 • CCX01
step3 = by-assoc-and (under (CCX01 • CZ12 • CCX01 • CZ01) (CZ01 • CCX01) (elim_CZ12.proved)) Eq.refl Eq.refl

step4 : CCX01 • CZ12 • CCX01 • CZ01 • CZ01 • CCX01 ≈ CCX01 • CZ12 • CCX01 • CCX01
step4 = by-assoc-and (under (CCX01 • CZ12 • CCX01) (CCX01) (elim_CZ01.proved)) Eq.refl Eq.refl

step5 : CCX01 • CZ12 • CCX01 • CCX01 ≈ CCX01 • CZ12
step5 = by-assoc-and (under (CCX01 • CZ12) (ε) (elim_CCX2.proved)) Eq.refl Eq.refl

proved : CZ12 • CZ01 • CCX01 ≈ CCX01 • CZ12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
