{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel114 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel151 as drel151
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CCX2 as elim_CCX2
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ01 as elim_CZ01
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ02 as elim_CZ02

step0 : CZ02 • CZ01 • CCX01 ≈ CZ02 • CZ01 • CCX01 • CZ02 • CZ02
step0 = by-assoc-and (under (CZ02 • CZ01 • CCX01) (ε) (sym (elim_CZ02.proved))) Eq.refl Eq.refl

step1 : CZ02 • CZ01 • CCX01 • CZ02 • CZ02 ≈ CZ02 • CZ01 • CCX01 • CZ02 • CCX01 • CCX01 • CZ02
step1 = by-assoc-and (under (CZ02 • CZ01 • CCX01 • CZ02) (CZ02) (sym (elim_CCX2.proved))) Eq.refl Eq.refl

step2 : CZ02 • CZ01 • CCX01 • CZ02 • CCX01 • CCX01 • CZ02 ≈ CZ02 • CZ01 • CCX01 • CCX01 • CZ01 • CZ02 • CCX01 • CZ02
step2 = by-assoc-and (under (CZ02 • CZ01 • CCX01) (CCX01 • CZ02) (drel151.proved)) Eq.refl Eq.refl

step3 : CZ02 • CZ01 • CCX01 • CCX01 • CZ01 • CZ02 • CCX01 • CZ02 ≈ CZ02 • CZ01 • CZ01 • CZ02 • CCX01 • CZ02
step3 = by-assoc-and (under (CZ02 • CZ01) (CZ01 • CZ02 • CCX01 • CZ02) (elim_CCX2.proved)) Eq.refl Eq.refl

step4 : CZ02 • CZ01 • CZ01 • CZ02 • CCX01 • CZ02 ≈ CZ02 • CZ02 • CCX01 • CZ02
step4 = by-assoc-and (under (CZ02) (CZ02 • CCX01 • CZ02) (elim_CZ01.proved)) Eq.refl Eq.refl

step5 : CZ02 • CZ02 • CCX01 • CZ02 ≈ CCX01 • CZ02
step5 = by-assoc-and (under (ε) (CCX01 • CZ02) (elim_CZ02.proved)) Eq.refl Eq.refl

proved : CZ02 • CZ01 • CCX01 ≈ CCX01 • CZ02
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
