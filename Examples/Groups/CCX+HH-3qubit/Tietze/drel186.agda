{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel186 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel172 as drel172
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CX02 as elim_CX02
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ01 as elim_CZ01
import Examples.Groups.CCX+HH-3qubit.Tietze.elim_CZ12 as elim_CZ12

step0 : CZ12 • CZ01 • CX02 ≈ CX02 • CX02 • CZ12 • CZ01 • CX02
step0 = by-assoc-and (under (ε) (CZ12 • CZ01 • CX02) (sym (elim_CX02.proved))) Eq.refl Eq.refl

step1 : CX02 • CX02 • CZ12 • CZ01 • CX02 ≈ CX02 • CZ12 • CZ12 • CX02 • CZ12 • CZ01 • CX02
step1 = by-assoc-and (under (CX02) (CX02 • CZ12 • CZ01 • CX02) (sym (elim_CZ12.proved))) Eq.refl Eq.refl

step2 : CX02 • CZ12 • CZ12 • CX02 • CZ12 • CZ01 • CX02 ≈ CX02 • CZ12 • CX02 • CZ01 • CZ12 • CZ12 • CZ01 • CX02
step2 = by-assoc-and (under (CX02 • CZ12) (CZ12 • CZ01 • CX02) (drel172.proved)) Eq.refl Eq.refl

step3 : CX02 • CZ12 • CX02 • CZ01 • CZ12 • CZ12 • CZ01 • CX02 ≈ CX02 • CZ12 • CX02 • CZ01 • CZ01 • CX02
step3 = by-assoc-and (under (CX02 • CZ12 • CX02 • CZ01) (CZ01 • CX02) (elim_CZ12.proved)) Eq.refl Eq.refl

step4 : CX02 • CZ12 • CX02 • CZ01 • CZ01 • CX02 ≈ CX02 • CZ12 • CX02 • CX02
step4 = by-assoc-and (under (CX02 • CZ12 • CX02) (CX02) (elim_CZ01.proved)) Eq.refl Eq.refl

step5 : CX02 • CZ12 • CX02 • CX02 ≈ CX02 • CZ12
step5 = by-assoc-and (under (CX02 • CZ12) (ε) (elim_CX02.proved)) Eq.refl Eq.refl

proved : CZ12 • CZ01 • CX02 ≈ CX02 • CZ12
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (refl))))))
