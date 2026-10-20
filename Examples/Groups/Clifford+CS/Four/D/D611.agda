{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D611 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.TopWeakening using (low-comm)
open import Examples.Groups.Clifford+CS.Idle using (low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00003 ; wn00005 ; wn00007 ; wn00008 ; wn00009 ; wn00010 ; wn00012 ; wn00014 ; wn00015 ; wn00016 ; wn00020 ; wn00021 ; wn00022 ; wn00023 ; wn00024 ; wn00025 ; wn00026 ; wn00027 ; wn00029 ; wn00030 ; wn00031 ; wn00033 ; wn00043 ; wn00046 ; wn00047 ; wn00048 ; wn00049 ; wn00050 ; wn00051 ; wn00052 ; wn00074 ; wn00076 ; wn00127 ; wn00173 ; wn00175)
open import Examples.Groups.Clifford+CS.Four.Wins.W02 using (wn00253 ; wn00271 ; wn00272)
open import Examples.Groups.Clifford+CS.Four.Wins.W27 using (wn01377)
open import Examples.Groups.Clifford+CS.Four.Wins.W28 using (wn01464 ; wn01465 ; wn01476 ; wn01477 ; wn01478 ; wn01479 ; wn01482 ; wn01490 ; wn01493 ; wn01499)
open import Examples.Groups.Clifford+CS.Four.Wins.W34 using (wn01671 ; wn01672 ; wn01673 ; wn01678 ; wn01681 ; wn01682)
open import Examples.Groups.Clifford+CS.Four.Wins.W35 using (wn01727 ; wn01728 ; wn01732)
open import Examples.Groups.Clifford+CS.Four.Wins.W37 using (wn01806 ; wn01807 ; wn01808 ; wn01812 ; wn01813 ; wn01814 ; wn01815 ; wn01816 ; wn01817 ; wn01818 ; wn01819 ; wn01820 ; wn01821 ; wn01822)
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)
open import Examples.Groups.Clifford+CS.Four.D.D012 using (lem-pass-CCZ123-vs-CS13 ; lem-pass-CCZ123-vs-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D370 using (lem-pass-CZ12-vs-CS13 ; lem-pass-CZ12-vs-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D374 using (lem-pass-CZ13-vs-CS13 ; lem-pass-CZ13-vs-CSd13 ; lem-pass-Z1-vs-CS13 ; lem-pass-Z1-vs-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D513 using (lem-pass-CCZ123-vs-CCZ023)
open import Examples.Groups.Clifford+CS.Four.D.D522 using (lem-pass-CCZ023-vs-CZ13)
open import Examples.Groups.Clifford+CS.Four.D.D539 using (lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D541 using (lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D544 using (lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D588 using (lem-T-CZ03-T-at1023 ; lem-pass-X1-CS10-X1-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 ; lem-pass-X1-CSd10-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 ; lem-pass-X1-CSd10-X1-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3 ; lem-pass-X2-CK21-X2-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 ; lem-pass-X2-CKd21-X2-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 ; lem-pass-X2-CS20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 ; lem-pass-X2-CSd20-X2-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3 ; lem-pass-X3-CKd30-X3-vs-X1-X2-TOFF012-CS03-TOFF012-CSd03-X1-X2)

-- pass [X2 CSd20 X2] [X1 X3 CS03 TOFF012 CSd03 TOFF012 X1 X3]: 27 steps
lem-pass-X2-CSd20-X2-vs-X1-X3-CS03-TOFF012-CSd03-TOFF012-X1-X3 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X1 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd20-X2-vs-X1-X3-CS03-TOFF012-CSd03-TOFF012-X1-X3 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X2 ∷ CS02⁻ ∷ X2 ∷ X1 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ Sw01 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ Sw01 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ [])
  b0 = at 0 4 (X1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) wn01681 ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 3 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 2 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 1 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 2 4 (X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) wn01499 ▸
       at 1 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸ done

  b1 : Chain (X1 ∷ X3 ∷ Sw01 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ Sw01 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X3 ∷ [])
  b1 = at 2 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 3 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 4 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 5 2 [] wn00031 ▸
       at 2 3 (X2 ∷ CS02⁻ ∷ X2 ∷ []) wn01482 ▸
       at 2 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 6 3 (X2 ∷ CS02⁻ ∷ X2 ∷ []) wn01482 ▸
       at 6 4 (X1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) wn01681 ▸ done

  b2 : Chain (X1 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X3 ∷ []) (X1 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ X2 ∷ Sw01 ∷ CS12⁻ ∷ X2 ∷ Sw01 ∷ [])
  b2 = at 11 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 10 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 9 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 8 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 7 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 8 4 (X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) wn01499 ▸
       at 7 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 8 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸ done

  b3 : Chain (X1 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ X2 ∷ Sw01 ∷ CS12⁻ ∷ X2 ∷ Sw01 ∷ []) (X1 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  b3 = at 9 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 10 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 11 2 [] wn00031 ▸ done

-- pass [X2 CS20 X2] [X1 X3 CS03 TOFF012 CSd03 TOFF012 X1 X3]: 27 steps
lem-pass-X2-CS20-X2-vs-X1-X3-CS03-TOFF012-CSd03-TOFF012-X1-X3 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ X1 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS20-X2-vs-X1-X3-CS03-TOFF012-CSd03-TOFF012-X1-X3 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (X2 ∷ CS02 ∷ X2 ∷ X1 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ Sw01 ∷ X2 ∷ CS12 ∷ X2 ∷ Sw01 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ [])
  b0 = at 0 4 (X1 ∷ X2 ∷ CS02 ∷ X2 ∷ []) wn01682 ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 3 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 2 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 1 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 2 4 (X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) wn01493 ▸
       at 1 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸ done

  b1 : Chain (X1 ∷ X3 ∷ Sw01 ∷ X2 ∷ CS12 ∷ X2 ∷ Sw01 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ CS02 ∷ X2 ∷ X3 ∷ [])
  b1 = at 2 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 3 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 4 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 5 2 [] wn00031 ▸
       at 2 3 (X2 ∷ CS02 ∷ X2 ∷ []) wn01490 ▸
       at 2 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 6 3 (X2 ∷ CS02 ∷ X2 ∷ []) wn01490 ▸
       at 6 4 (X1 ∷ X2 ∷ CS02 ∷ X2 ∷ []) wn01682 ▸ done

  b2 : Chain (X1 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ CS02 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ X2 ∷ Sw01 ∷ CS12 ∷ X2 ∷ Sw01 ∷ [])
  b2 = at 11 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 10 2 (Sw01 ∷ X3 ∷ []) (sym (low-comm (Swap) ((X ↑)))) ▸
       at 9 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 8 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 7 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 8 4 (X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) wn01493 ▸
       at 7 2 (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑))) ▸
       at 8 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸ done

  b3 : Chain (X1 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ X2 ∷ Sw01 ∷ CS12 ∷ X2 ∷ Sw01 ∷ []) (X1 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ X2 ∷ CS02 ∷ X2 ∷ [])
  b3 = at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 10 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 11 2 [] wn00031 ▸ done

-- pass [X1 CSd10 X1] [X2 X3 Sd0 CS03 TOFF012 CSd03 TOFF012 S0 X2 X3]: 7 steps
lem-pass-X1-CSd10-X1-vs-X2-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2-X3 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-X2-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2-X3 = run b0
  where
  b0 : Chain (X1 ∷ CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  b0 = at 0 4 (X2 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) wn01678 ▸
       at 1 4 (X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) wn01671 ▸
       at 2 4 (S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) wn01672 ▸
       at 3 7 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012) ▸
       at 7 4 (S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) wn01673 ▸
       at 8 4 (X2 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) wn01678 ▸
       at 9 4 (X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) wn01671 ▸ done

-- pass [CKd21] [X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2 X3]: 5 steps
lem-pass-CKd21-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : ⟪ (CK21⁻ ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ CK21⁻ ∷ []) ⟫ʷ
lem-pass-CKd21-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = run b0
  where
  b0 : Chain (CK21⁻ ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ CK21⁻ ∷ [])
  b0 = at 0 2 (X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) wn01478 ▸
       at 17 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 1 17 (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3) ▸
       at 15 4 (X2 ∷ CK21⁻ ∷ []) wn01479 ▸
       at 14 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done

-- pass [CK21] [X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2 X3]: 5 steps
lem-pass-CK21-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : ⟪ (CK21 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ CK21 ∷ []) ⟫ʷ
lem-pass-CK21-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = run b0
  where
  b0 : Chain (CK21 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ CK21 ∷ [])
  b0 = at 0 2 (X2 ∷ X2 ∷ CK21 ∷ X2 ∷ []) wn01476 ▸
       at 17 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 1 17 (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3) ▸
       at 15 4 (X2 ∷ CK21 ∷ []) wn01477 ▸
       at 14 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done

-- CA CSd20 Gad(t=0, W=(3,), d=1, e=1): 7 steps
lem-CA-CSd20-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡1⟩ : ⟪ (CS02⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-CA-CSd20-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡1⟩ = run b0
  where
  b0 : Chain (CS02⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ CS02⁻ ∷ [])
  b0 = at 0 1 (S0⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) wn01812 ▸
       at 1 9 (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3) ▸
       at 0 2 (X3 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑ ↑))) ▸
       at 1 1 (S0⁻ ∷ []) wn01813 ▸
       at 6 0 (S0 ∷ S0⁻ ∷ []) wn01732 ▸
       at 7 2 (X3 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑ ↑))) ▸
       at 8 4 (CS02⁻ ∷ []) wn01814 ▸ done

-- CA CS20 Gad(t=0, W=(3,), d=Sd, e=1): 7 steps
lem-CA-CS20-Gad⟨t≡0-W≡⟨3⟩-d≡Sd-e≡1⟩ : ⟪ (CS02 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS02 ∷ []) ⟫ʷ
lem-CA-CS20-Gad⟨t≡0-W≡⟨3⟩-d≡Sd-e≡1⟩ = run b0
  where
  b0 : Chain (CS02 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ []) (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS02 ∷ [])
  b0 = at 0 1 (S0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) wn01815 ▸
       at 1 11 (X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3) ▸
       at 0 2 (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑))) ▸
       at 1 2 [] wn01728 ▸
       at 5 1 (S0 ∷ []) wn01727 ▸
       at 5 2 (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑))) ▸
       at 6 4 (CS02 ∷ []) wn01816 ▸ done

-- CA CSd10 Gad(t=0, W=(3,), d=1, e=1): 7 steps
lem-CA-CSd10-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡1⟩ : ⟪ (CS01⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CA-CSd10-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡1⟩ = run b0
  where
  b0 : Chain (CS01⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ CS01⁻ ∷ [])
  b0 = at 0 1 (S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) wn01817 ▸
       at 1 9 (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3) ▸
       at 0 2 (X3 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑ ↑))) ▸
       at 1 1 (S0⁻ ∷ []) wn01813 ▸
       at 6 0 (S0 ∷ S0⁻ ∷ []) wn01732 ▸
       at 7 2 (X3 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑ ↑))) ▸
       at 8 4 (CS01⁻ ∷ []) wn01818 ▸ done

-- CA CS10 Gad(t=0, W=(3,), d=Sd, e=1): 7 steps
lem-CA-CS10-Gad⟨t≡0-W≡⟨3⟩-d≡Sd-e≡1⟩ : ⟪ (CS01 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS01 ∷ []) ⟫ʷ
lem-CA-CS10-Gad⟨t≡0-W≡⟨3⟩-d≡Sd-e≡1⟩ = run b0
  where
  b0 : Chain (CS01 ∷ X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ []) (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS01 ∷ [])
  b0 = at 0 1 (S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) wn01819 ▸
       at 1 11 (X3 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3) ▸
       at 0 2 (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑))) ▸
       at 1 2 [] wn01728 ▸
       at 5 1 (S0 ∷ []) wn01727 ▸
       at 5 2 (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑))) ▸
       at 6 4 (CS01 ∷ []) wn01820 ▸ done

-- pass [Z1 CZ12 CZ13 CCZ123] [TOFF102 CS13 TOFF102 CSd13]: 526 steps
lem-pass-Z1-CZ12-CZ13-CCZ123-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-Z1-CZ12-CZ13-CCZ123-vs-TOFF102-CS13-TOFF102-CSd13 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (trans (run b62) (trans (run b63) (trans (run b64) (run b65)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ CCZ123 ∷ K1 ∷ CS12 ∷ CX01 ∷ Sw01 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b0 = at 3 0 (Toff102 ∷ Toff102 ∷ []) wn01377 ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 6 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 12 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 11 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 10 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 9 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸ done

  b1 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ CCZ123 ∷ K1 ∷ CS12 ∷ CX01 ∷ Sw01 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ Toff012 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b1 = at 8 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 7 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 6 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 7 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸
       at 7 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b2 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ Toff012 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Toff012 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b2 = at 10 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ CX02 ∷ []) wn00253 ▸
       at 7 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 6 2 (Sw01 ∷ CX02 ∷ []) wn00253 ▸
       at 5 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b3 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Toff012 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b3 = at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b4 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw01 ∷ CS12 ∷ K0 ∷ ι1 ∷ CCZ023 ∷ Toff012 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b4 = at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 7 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 10 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 9 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸ done

  b5 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ Sw01 ∷ CS12 ∷ K0 ∷ ι1 ∷ CCZ023 ∷ Toff012 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CCZ023 ∷ Toff012 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b5 = at 8 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 7 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 6 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 5 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 4 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 5 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸
       at 5 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸ done

  b6 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CCZ023 ∷ Toff012 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CCZ023 ∷ K0 ∷ CS12 ∷ CX01 ∷ Sw12 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b6 = at 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 13 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 12 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00014 ▸
       at 11 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 12 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸ done

  b7 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CCZ023 ∷ K0 ∷ CS12 ∷ CX01 ∷ Sw12 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b7 = at 9 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 10 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸
       at 7 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 8 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00046 ▸
       at 8 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b8 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b8 = at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b9 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b9 = at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00031 ▸
       at 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 12 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 10 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 11 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b10 = at 11 2 [] wn00014 ▸
       at 8 2 (Sw12 ∷ CS13⁻ ∷ []) wn00047 ▸
       at 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00014 ▸
       at 6 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸ done

  b11 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b11 = at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 8 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 8 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸ done

  b12 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw12 ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ CCZ013 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b12 = at 7 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 11 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 10 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00014 ▸
       at 9 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 10 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw12 ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ CCZ013 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b13 = at 8 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸
       at 7 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 8 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸
       at 5 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 6 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00046 ▸
       at 6 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz) ▸ done

  b14 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw12 ∷ CCZ013 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b14 = at 6 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b15 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS03 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b15 = at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 5 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 8 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 6 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 10 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸ done

  b16 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS03 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b16 = at 8 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 11 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 12 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 9 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b17 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b17 = at 7 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b18 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CCZ023 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ Sw12 ∷ CS13 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b18 = at 6 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 6 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 7 2 (CX21 ∷ Sw12 ∷ []) wn00050 ▸
       at 8 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 9 2 (CX21 ∷ Sw12 ∷ []) wn00050 ▸ done

  b19 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CCZ023 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ Sw12 ∷ CS13 ∷ Sw12 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b19 = at 10 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 6 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00052 ▸
       at 6 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00014 ▸
       at 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b20 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ Sw01 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ CCZ123 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b20 = at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00031 ▸ done

  b21 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ CCZ123 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b21 = at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b22 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CCZ123 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b22 = at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 4 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b23 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CCZ123 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b23 = at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b24 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b24 = at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸ done

  b25 : Chain (Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ Z1 ∷ CZ02 ∷ CZ02 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ CCZ123 ∷ CCZ023 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b25 = at 6 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00031 ▸
       at 2 0 (Toff102 ∷ Toff102 ∷ []) wn01377 ▸
       at 3 3 (CCZ023 ∷ CZ13 ∷ []) (lem-T-CZ03-T-at1023) ▸
       at 1 2 (Toff102 ∷ CZ02 ∷ CZ12 ∷ []) wn01806 ▸
       at 0 2 (Toff102 ∷ Z1 ∷ CZ02 ∷ []) wn01807 ▸
       at 5 2 (CZ13 ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-CZ13) ▸ done

  b26 : Chain (Toff102 ∷ Z1 ∷ CZ02 ∷ CZ02 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ CCZ123 ∷ CCZ023 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b26 = at 7 2 (CCZ023 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CCZ023) ▸
       at 2 2 [] wn01808 ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 6 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 7 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b27 : Chain (Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b27 = at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00031 ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b28 : Chain (Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b28 = at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 7 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 6 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 5 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸ done

  b29 : Chain (Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b29 = at 6 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 6 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 5 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 6 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b30 : Chain (Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b30 = at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 9 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00031 ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b31 : Chain (Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b31 = at 9 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 6 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 5 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 4 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 5 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸ done

  b32 : Chain (Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ CCZ123 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b32 = at 5 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00033 ▸
       at 4 2 [] wn00031 ▸
       at 4 2 (CS13 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CS13) ▸
       at 3 2 (CS13 ∷ CZ13 ∷ []) (lem-pass-CZ13-vs-CS13) ▸
       at 2 2 (CS13 ∷ CZ12 ∷ []) (lem-pass-CZ12-vs-CS13) ▸
       at 1 2 (CS13 ∷ Z1 ∷ []) (lem-pass-Z1-vs-CS13) ▸
       at 5 0 (Toff102 ∷ Toff102 ∷ []) wn01377 ▸ done

  b33 : Chain (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ CCZ123 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ CCZ123 ∷ K1 ∷ CS12 ∷ Sw01 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b33 = at 9 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 8 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 14 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 13 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 12 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 11 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 10 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸ done

  b34 : Chain (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ CCZ123 ∷ K1 ∷ CS12 ∷ Sw01 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ Sw01 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b34 = at 9 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 8 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 9 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸
       at 9 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 12 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸ done

  b35 : Chain (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw23 ∷ Sw01 ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ Sw01 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Toff012 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b35 = at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ CX02 ∷ []) wn00253 ▸
       at 9 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 8 2 (Sw01 ∷ CX02 ∷ []) wn00253 ▸
       at 7 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 8 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 9 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b36 : Chain (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Toff012 ∷ Sw01 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b36 = at 10 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 11 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 12 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 14 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 15 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b37 : Chain (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw01 ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CCZ023 ∷ Toff012 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b37 = at 9 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 9 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 8 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw01 ∷ ι1 ∷ []) wn00127 ▸
       at 12 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 11 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 10 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸ done

  b38 : Chain (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw01 ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ CCZ023 ∷ Toff012 ∷ Sw01 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CCZ023 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b38 = at 9 2 (Sw01 ∷ CS02⁻ ∷ []) wn00009 ▸
       at 8 2 (Sw01 ∷ CX10 ∷ []) wn00008 ▸
       at 7 2 (Sw01 ∷ CS02 ∷ []) wn00010 ▸
       at 6 2 (Sw01 ∷ K0 ∷ []) wn00271 ▸
       at 7 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00272 ▸
       at 7 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b39 : Chain (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CCZ023 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CCZ023 ∷ K0 ∷ CS12 ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b39 = at 16 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 15 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 14 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 [] wn00014 ▸
       at 13 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 14 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸
       at 11 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸ done

  b40 : Chain (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CCZ023 ∷ K0 ∷ CS12 ∷ Sw12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b40 = at 12 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸
       at 9 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 10 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00046 ▸
       at 10 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b41 : Chain (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CS23 ∷ Sw01 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b41 = at 9 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 10 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 11 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b42 : Chain (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ Sw12 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw12 ∷ CX01 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b42 = at 13 2 [] wn00031 ▸
       at 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 14 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 12 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 13 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] wn00014 ▸ done

  b43 : Chain (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw12 ∷ CX01 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b43 = at 10 2 (Sw12 ∷ CS13⁻ ∷ []) wn00047 ▸
       at 9 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00014 ▸
       at 8 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b44 : Chain (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ Sw23 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ Sw12 ∷ CCZ013 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b44 = at 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 13 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 10 5 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) wn00043 ▸
       at 10 5 (CCZ012 ∷ []) (by-assoc Eq.refl) ▸
       at 9 3 (CCZ013 ∷ []) (by-assoc Eq.refl) ▸ done

  b45 : Chain (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Toff012 ∷ Sw12 ∷ CCZ013 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ K0 ∷ CS12 ∷ CX01 ∷ Sw12 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ CCZ013 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b45 = at 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap)) ▸
       at 13 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 12 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00014 ▸
       at 11 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 12 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw12 ∷ CS12⁻ ∷ []) wn00015 ▸ done

  b46 : Chain (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ K0 ∷ CS12 ∷ CX01 ∷ Sw12 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ CCZ013 ∷ Toff012 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b46 = at 9 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 10 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw12 ∷ CS12 ∷ []) wn00016 ▸
       at 7 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 8 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00046 ▸
       at 8 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 8 3 (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz) ▸
       at 8 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b47 : Chain (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b47 = at 9 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b48 : Chain (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw12 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw12 ∷ CS03 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b48 = at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] wn00003 ▸
       at 7 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 10 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 8 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 12 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 10 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b49 : Chain (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw12 ∷ CS03 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b49 = at 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 13 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 14 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 11 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 8 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 9 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b50 : Chain (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b50 = at 10 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 11 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸ done

  b51 : Chain (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ CCZ123 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CCZ023 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b51 = at 8 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CS13 ∷ Sw12 ∷ []) wn00049 ▸
       at 9 2 (CX21 ∷ Sw12 ∷ []) wn00050 ▸
       at 10 2 (CS13⁻ ∷ Sw12 ∷ []) wn00051 ▸
       at 11 2 (CX21 ∷ Sw12 ∷ []) wn00050 ▸
       at 12 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸ done

  b52 : Chain (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CCZ023 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Sw12 ∷ Sw12 ∷ Sw01 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b52 = at 8 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00052 ▸
       at 8 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00014 ▸
       at 7 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b53 : Chain (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ Sw01 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ Sw01 ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ CCZ123 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b53 = at 10 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00031 ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸ done

  b54 : Chain (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CS23 ∷ Sw01 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ CCZ123 ∷ Sw01 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b54 = at 7 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b55 : Chain (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CCZ123 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b55 = at 6 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 6 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b56 : Chain (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CCZ123 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b56 = at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 8 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 9 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 10 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸ done

  b57 : Chain (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CCZ123 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ Sw01 ∷ CX02 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS13⁻ ∷ [])
  b57 = at 11 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 8 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸ done

  b58 : Chain (Toff102 ∷ CS13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Toff102 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ Z1 ∷ CZ02 ∷ CZ02 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ CCZ023 ∷ CCZ123 ∷ CS13⁻ ∷ [])
  b58 = at 7 3 (CCZ023 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00031 ▸
       at 4 0 (Toff102 ∷ Toff102 ∷ []) wn01377 ▸
       at 5 3 (CCZ023 ∷ CZ13 ∷ []) (lem-T-CZ03-T-at1023) ▸
       at 3 2 (Toff102 ∷ CZ02 ∷ CZ12 ∷ []) wn01806 ▸
       at 2 2 (Toff102 ∷ Z1 ∷ CZ02 ∷ []) wn01807 ▸
       at 7 2 (CZ13 ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-CZ13) ▸
       at 9 2 (CCZ023 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CCZ023) ▸ done

  b59 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ Z1 ∷ CZ02 ∷ CZ02 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ CCZ023 ∷ CCZ123 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ CS13⁻ ∷ [])
  b59 = at 4 2 [] wn01808 ▸
       at 8 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 7 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸ done

  b60 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CCZ123 ∷ CS13⁻ ∷ [])
  b60 = at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00031 ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b61 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CCZ123 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CCZ123 ∷ CS13⁻ ∷ [])
  b61 = at 12 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 9 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 8 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 7 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 8 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸ done

  b62 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ023 ∷ Sw01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Sw01 ∷ CCZ123 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ CS13⁻ ∷ [])
  b62 = at 8 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸
       at 6 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 7 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 8 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 9 2 (CX02 ∷ Sw01 ∷ []) wn00030 ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b63 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ CS13⁻ ∷ [])
  b63 = at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00031 ▸
       at 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸ done

  b64 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Sw01 ∷ CCZ123 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ CS13⁻ ∷ [])
  b64 = at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 8 2 (Sw01 ∷ CS23⁻ ∷ []) (sym (low-comm (Swap) ((CS • CS • CS)))) ▸
       at 7 2 (Sw01 ∷ CX12 ∷ []) wn00074 ▸
       at 6 2 (Sw01 ∷ CS23 ∷ []) (sym (low-comm (Swap) (CS))) ▸
       at 7 5 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) wn00026 ▸
       at 7 5 (CCZ123 ∷ []) (by-assoc Eq.refl) ▸ done

  b65 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ Sw01 ∷ CCZ123 ∷ CCZ123 ∷ Sw01 ∷ CCZ123 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ [])
  b65 = at 7 2 [] wn00033 ▸
       at 6 2 [] wn00031 ▸
       at 6 2 (CS13⁻ ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CSd13) ▸
       at 5 2 (CS13⁻ ∷ CZ13 ∷ []) (lem-pass-CZ13-vs-CSd13) ▸
       at 4 2 (CS13⁻ ∷ CZ12 ∷ []) (lem-pass-CZ12-vs-CSd13) ▸
       at 3 2 (CS13⁻ ∷ Z1 ∷ []) (lem-pass-Z1-vs-CSd13) ▸ done

-- pass [CKd30] [X1 X2 X3 TOFF012 CS03 TOFF012 CSd03 X1 X2 X3]: 27 steps
lem-pass-CKd30-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : ⟪ (CK30⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ []) ⟫ʷ
lem-pass-CKd30-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (CK30⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X3 ∷ Sw23 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b0 = at 2 2 (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X)) ▸
       at 1 2 (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑))) ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 0 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 2 (X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) wn01464 ▸
       at 0 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸ done

  b1 : Chain (X3 ∷ Sw23 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X3 ∷ X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ [])
  b1 = at 1 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 4 2 [] wn00003 ▸
       at 1 11 (X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-X1-X2-TOFF012-CS03-TOFF012-CSd03-X1-X2) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 12 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸ done

  b2 : Chain (X3 ∷ X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ []) (X3 ∷ X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ Sw23 ∷ Sw23 ∷ [])
  b2 = at 11 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 10 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 9 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 10 4 (X2 ∷ CK20⁻ ∷ []) wn01465 ▸
       at 9 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (X3 ∷ X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ Sw23 ∷ Sw23 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ [])
  b3 = at 11 2 [] wn00003 ▸
       at 0 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 1 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done

-- pass [CSd10] [X1 X2 X3 TOFF012 CS03 TOFF012 CSd03 X1 X2 X3]: 7 steps
lem-pass-CSd10-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : ⟪ (CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-pass-CSd10-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = run b0
  where
  b0 : Chain (CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS01⁻ ∷ [])
  b0 = at 0 2 (X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) wn01821 ▸
       at 10 2 (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X)) ▸
       at 11 2 (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑))) ▸
       at 1 11 (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3) ▸
       at 9 4 (X1 ∷ CS01⁻ ∷ []) wn01822 ▸
       at 8 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 7 2 (X1 ∷ X2 ∷ []) (sym (low-comm ((X ↑)) (X))) ▸ done
