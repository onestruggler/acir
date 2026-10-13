{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Tietze.drel159 where

import Relation.Binary.PropositionalEquality as Eq
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.Engine
import Examples.Groups.CCX+HH-3qubit.Tietze.drel29 as drel29
import Examples.Groups.CCX+HH-3qubit.Tietze.drel30 as drel30
import Examples.Groups.CCX+HH-3qubit.Tietze.drel49 as drel49
import Examples.Groups.CCX+HH-3qubit.Tietze.drel63 as drel63
import Examples.Groups.CCX+HH-3qubit.Tietze.drel85 as drel85
import Examples.Groups.CCX+HH-3qubit.Tietze.drel86 as drel86
import Examples.Groups.CCX+HH-3qubit.Tietze.drel89 as drel89
import Examples.Groups.CCX+HH-3qubit.Tietze.drel90 as drel90

step0 : CZ01 • CCX12 ≈ K12 • K12 • CZ01 • CCX12
step0 = by-assoc-and (under (ε) (CZ01 • CCX12) (sym (axiom r023))) Eq.refl Eq.refl

step1 : K12 • K12 • CZ01 • CCX12 ≈ K12 • K01 • K01 • K12 • CZ01 • CCX12
step1 = by-assoc-and (under (K12) (K12 • CZ01 • CCX12) (sym (axiom r025))) Eq.refl Eq.refl

step2 : K12 • K01 • K01 • K12 • CZ01 • CCX12 ≈ K12 • K01 • K01 • CX01 • K12 • CCX12
step2 = by-assoc-and (under (K12 • K01 • K01) (CCX12) (drel49.proved)) Eq.refl Eq.refl

step3 : K12 • K01 • K01 • CX01 • K12 • CCX12 ≈ K12 • K01 • K01 • CX01 • K01 • K01 • K12 • CCX12
step3 = by-assoc-and (under (K12 • K01 • K01 • CX01) (K12 • CCX12) (sym (axiom r025))) Eq.refl Eq.refl

step4 : K12 • K01 • K01 • CX01 • K01 • K01 • K12 • CCX12 ≈ K12 • K01 • CX10 • K01 • K12 • CCX12
step4 = by-assoc-and (under (K12 • K01) (K01 • K12 • CCX12) (sym (axiom r012))) Eq.refl Eq.refl

step5 : K12 • K01 • CX10 • K01 • K12 • CCX12 ≈ K12 • K01 • CX10 • K12 • K01 • CCX12
step5 = by-assoc-and (under (K12 • K01 • CX10) (CCX12) (axiom r039)) Eq.refl Eq.refl

step6 : K12 • K01 • CX10 • K12 • K01 • CCX12 ≈ K12 • K01 • CX10 • K12 • CCX02 • K01
step6 = by-assoc-and (under (K12 • K01 • CX10 • K12) (ε) (drel63.proved)) Eq.refl Eq.refl

step7 : K12 • K01 • CX10 • K12 • CCX02 • K01 ≈ K12 • K01 • CX10 • CCX01 • K12 • K01
step7 = by-assoc-and (under (K12 • K01 • CX10) (K01) (sym (drel29.proved))) Eq.refl Eq.refl

step8 : K12 • K01 • CX10 • CCX01 • K12 • K01 ≈ K12 • K01 • CCX01 • CX12 • CX10 • K12 • K01
step8 = by-assoc-and (under (K12 • K01) (K12 • K01) (drel90.proved)) Eq.refl Eq.refl

step9 : K12 • K01 • CCX01 • CX12 • CX10 • K12 • K01 ≈ K12 • K01 • CCX01 • CX12 • CX10 • K01 • K12
step9 = by-assoc-and (under (K12 • K01 • CCX01 • CX12 • CX10) (ε) (sym (axiom r039))) Eq.refl Eq.refl

step10 : K12 • K01 • CCX01 • CX12 • CX10 • K01 • K12 ≈ K12 • K01 • CCX01 • CX12 • K01 • CX01 • K01 • K01 • K12
step10 = by-assoc-and (under (K12 • K01 • CCX01 • CX12) (K01 • K12) (axiom r012)) Eq.refl Eq.refl

step11 : K12 • K01 • CCX01 • CX12 • K01 • CX01 • K01 • K01 • K12 ≈ K12 • K01 • CCX01 • CX12 • K01 • CX01 • K12
step11 = by-assoc-and (under (K12 • K01 • CCX01 • CX12 • K01 • CX01) (K12) (axiom r025)) Eq.refl Eq.refl

step12 : K12 • K01 • CCX01 • CX12 • K01 • CX01 • K12 ≈ K12 • K01 • CCX01 • CX12 • K01 • K12 • K12 • CX01 • K12
step12 = by-assoc-and (under (K12 • K01 • CCX01 • CX12 • K01) (CX01 • K12) (sym (axiom r023))) Eq.refl Eq.refl

step13 : K12 • K01 • CCX01 • CX12 • K01 • K12 • K12 • CX01 • K12 ≈ K12 • K01 • CCX01 • CX12 • K01 • K12 • CZ01
step13 = by-assoc-and (under (K12 • K01 • CCX01 • CX12 • K01 • K12) (ε) (sym (axiom r001))) Eq.refl Eq.refl

step14 : K12 • K01 • CCX01 • CX12 • K01 • K12 • CZ01 ≈ K01 • K12 • CCX01 • CX12 • K01 • K12 • CZ01
step14 = by-assoc-and (under (ε) (CCX01 • CX12 • K01 • K12 • CZ01) (sym (axiom r039))) Eq.refl Eq.refl

step15 : K01 • K12 • CCX01 • CX12 • K01 • K12 • CZ01 ≈ K01 • CCX02 • K12 • CX12 • K01 • K12 • CZ01
step15 = by-assoc-and (under (K01) (CX12 • K01 • K12 • CZ01) (drel86.proved)) Eq.refl Eq.refl

step16 : K01 • CCX02 • K12 • CX12 • K01 • K12 • CZ01 ≈ K01 • CCX02 • K12 • CX12 • K12 • K01 • CZ01
step16 = by-assoc-and (under (K01 • CCX02 • K12 • CX12) (CZ01) (axiom r039)) Eq.refl Eq.refl

step17 : K01 • CCX02 • K12 • CX12 • K12 • K01 • CZ01 ≈ CCX12 • K01 • K12 • CX12 • K12 • K01 • CZ01
step17 = by-assoc-and (under (ε) (K12 • CX12 • K12 • K01 • CZ01) (sym (drel85.proved))) Eq.refl Eq.refl

step18 : CCX12 • K01 • K12 • CX12 • K12 • K01 • CZ01 ≈ CCX12 • K01 • CX21 • K12 • K12 • K01 • CZ01
step18 = by-assoc-and (under (CCX12 • K01) (K12 • K01 • CZ01) (sym (drel30.proved))) Eq.refl Eq.refl

step19 : CCX12 • K01 • CX21 • K12 • K12 • K01 • CZ01 ≈ CCX12 • K01 • CX21 • K01 • CZ01
step19 = by-assoc-and (under (CCX12 • K01 • CX21) (K01 • CZ01) (axiom r023)) Eq.refl Eq.refl

step20 : CCX12 • K01 • CX21 • K01 • CZ01 ≈ CCX12 • CZ12 • K01 • K01 • CZ01
step20 = by-assoc-and (under (CCX12) (K01 • CZ01) (sym (drel89.proved))) Eq.refl Eq.refl

step21 : CCX12 • CZ12 • K01 • K01 • CZ01 ≈ CCX12 • CZ12 • CZ01
step21 = by-assoc-and (under (CCX12 • CZ12) (CZ01) (axiom r025)) Eq.refl Eq.refl

proved : CZ01 • CCX12 ≈ CCX12 • CZ12 • CZ01
proved = trans step0 (trans step1 (trans step2 (trans step3 (trans step4 (trans step5 (trans step6 (trans step7 (trans step8 (trans step9 (trans step10 (trans step11 (trans step12 (trans step13 (trans step14 (trans step15 (trans step16 (trans step17 (trans step18 (trans step19 (trans step20 (trans step21 (refl))))))))))))))))))))))
