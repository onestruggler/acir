{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D499 where

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
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00005 ; wn00007 ; wn00027 ; wn00029 ; wn00031 ; wn00048 ; wn00065 ; wn00076 ; wn00198)
open import Examples.Groups.Clifford+CS.Four.Wins.W02 using (wn00317 ; wn00329 ; wn00330)
open import Examples.Groups.Clifford+CS.Four.Wins.W10 using (wn00772)
open import Examples.Groups.Clifford+CS.Four.Wins.W20 using (wn01052 ; wn01053)
open import Examples.Groups.Clifford+CS.Four.Wins.W21 using (wn01106)
open import Examples.Groups.Clifford+CS.Four.Wins.W24 using (wn01228)
open import Examples.Groups.Clifford+CS.Four.Wins.W25 using (wn01268 ; wn01269 ; wn01271 ; wn01272)
open import Examples.Groups.Clifford+CS.Four.Wins.W26 using (wn01313 ; wn01314 ; wn01315)

-- pass [CS03 CS03 CK03 CS03 CK03 CK03 CX01 CK13 S1 CK13 S1 CS13 CS13 CS13 CK13 S1 CS13 CS13 CS13 CS13 CS13 CS13 CX01 CS13 CS13 CK13 CS13 CK13 CK13] [CSd02]: 185 steps
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-CSd02 : ⟪ (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-CSd02 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (run b23)))))))))))))))))))))))
  where
  b0 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CS02⁻ ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ CK23 ∷ Sw12 ∷ CK13 ∷ [])
  b0 = at 29 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 28 2 (Sw12 ∷ CK23 ∷ []) wn01052 ▸
       at 29 2 (CS01⁻ ∷ CK23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CK₀₁))) ▸
       at 30 2 (Sw12 ∷ CK13 ∷ []) wn01053 ▸
       at 28 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 28 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 27 2 (Sw12 ∷ CK23 ∷ []) wn01052 ▸
       at 28 2 (CS01⁻ ∷ CK23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CK₀₁))) ▸ done

  b1 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ CK23 ∷ Sw12 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b1 = at 29 2 (Sw12 ∷ CK13 ∷ []) wn01053 ▸
       at 27 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 27 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 27 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 28 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 26 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 26 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b2 = at 25 2 (Sw12 ∷ CK23 ∷ []) wn01052 ▸
       at 26 2 (CS01⁻ ∷ CK23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CK₀₁))) ▸
       at 27 2 (Sw12 ∷ CK13 ∷ []) wn01053 ▸
       at 25 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 25 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 24 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 25 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 26 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸ done

  b3 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b3 = at 24 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 24 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 24 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 25 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 23 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 22 2 (CS02⁻ ∷ CX01 ∷ []) wn01268 ▸
       at 22 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b4 = at 21 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 22 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 23 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 21 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 21 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 21 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 22 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸ done

  b5 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ Sw12 ∷ CS23 ∷ CS01⁻ ∷ Sw12 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b5 = at 20 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 20 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 20 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 21 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 19 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 19 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸ done

  b6 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ Sw12 ∷ CS23 ∷ CS01⁻ ∷ Sw12 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS02⁻ ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b6 = at 19 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 20 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 18 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 18 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 18 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 19 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 17 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS02⁻ ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw12 ∷ CK23 ∷ CS01⁻ ∷ Sw12 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b7 = at 17 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 17 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 18 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 16 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (CS02⁻ ∷ S1 ∷ []) wn01269 ▸
       at 15 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw12 ∷ CK23 ∷ []) wn01052 ▸ done

  b8 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw12 ∷ CK23 ∷ CS01⁻ ∷ Sw12 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS02⁻ ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b8 = at 15 2 (CS01⁻ ∷ CK23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CK₀₁))) ▸
       at 16 2 (Sw12 ∷ CK13 ∷ []) wn01053 ▸
       at 14 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 14 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 14 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 15 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 13 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b9 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS02⁻ ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ Sw12 ∷ CS01⁻ ∷ CS23 ∷ Sw12 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b9 = at 13 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 13 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸
       at 14 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 12 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 12 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 12 2 (CS01⁻ ∷ CS23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CS))) ▸ done

  b10 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ Sw12 ∷ CS01⁻ ∷ CS23 ∷ Sw12 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CS02⁻ ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b10 = at 13 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 11 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CS02⁻ ∷ S1 ∷ []) wn01269 ▸
       at 10 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw12 ∷ CK23 ∷ []) wn01052 ▸
       at 10 2 (CS01⁻ ∷ CK23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CK₀₁))) ▸
       at 11 2 (Sw12 ∷ CK13 ∷ []) wn01053 ▸
       at 9 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CS02⁻ ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CS02⁻ ∷ Sw01 ∷ Sw01 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b11 = at 8 2 (CS02⁻ ∷ S1 ∷ []) wn01269 ▸
       at 8 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw12 ∷ CK23 ∷ []) wn01052 ▸
       at 8 2 (CS01⁻ ∷ CK23 ∷ []) (sym (low-comm ((CS • CS • CS)) (CK₀₁))) ▸
       at 9 2 (Sw12 ∷ CK13 ∷ []) wn01053 ▸
       at 7 3 (CS02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS02⁻ ∷ CX01 ∷ []) wn01268 ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b12 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CS02⁻ ∷ Sw01 ∷ Sw01 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CS02⁻ ∷ Sw01 ∷ CK13 ∷ Sw01 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b12 = at 6 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 5 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 2 (Sw01 ∷ CK12 ∷ []) wn00772 ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CS12⁻ ∷ CK13 ∷ []) wn01313 ▸
       at 5 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸ done

  b13 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CS02⁻ ∷ Sw01 ∷ CK13 ∷ Sw01 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ Sw01 ∷ CS12⁻ ∷ Sw01 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b13 = at 7 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CK02 ∷ Sw01 ∷ []) wn00329 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00031 ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 5 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸ done

  b14 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ Sw01 ∷ CS12⁻ ∷ Sw01 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS02⁻ ∷ Sw01 ∷ Sw23 ∷ CK12 ∷ Sw23 ∷ Sw01 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b14 = at 4 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 2 (Sw01 ∷ CK12 ∷ []) wn00772 ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (CS12⁻ ∷ CK13 ∷ []) wn01313 ▸
       at 4 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 6 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b15 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS02⁻ ∷ Sw01 ∷ Sw23 ∷ CK12 ∷ Sw23 ∷ Sw01 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CS12⁻ ∷ Sw01 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b15 = at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CK02 ∷ Sw01 ∷ []) wn00329 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00031 ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b16 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CS12⁻ ∷ Sw01 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS02⁻ ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b16 = at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (CS12⁻ ∷ CS13 ∷ []) wn00198 ▸
       at 3 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b17 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS02⁻ ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ Sw23 ∷ CK02 ∷ Sw01 ∷ Sw23 ∷ CS12⁻ ∷ Sw01 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b17 = at 5 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00031 ▸
       at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 2 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b18 : Chain (CS03 ∷ CS03 ∷ Sw23 ∷ CK02 ∷ Sw01 ∷ Sw23 ∷ CS12⁻ ∷ Sw01 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CS02⁻ ∷ Sw23 ∷ CK02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b18 = at 3 2 (Sw01 ∷ CK12 ∷ []) wn00772 ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (CS12⁻ ∷ CK13 ∷ []) wn01313 ▸
       at 2 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 4 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CK02 ∷ Sw01 ∷ []) wn00329 ▸ done

  b19 : Chain (CS03 ∷ CS03 ∷ CS02⁻ ∷ Sw23 ∷ CK02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ CS12⁻ ∷ Sw01 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b19 = at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00031 ▸
       at 3 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 2 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸ done

  b20 : Chain (CS03 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ CS12⁻ ∷ Sw01 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS02⁻ ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b20 = at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (CS12⁻ ∷ CS13 ∷ []) wn00198 ▸
       at 1 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b21 : Chain (CS03 ∷ CS02⁻ ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS12⁻ ∷ Sw01 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b21 = at 2 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00031 ▸
       at 2 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 1 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 0 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b22 : Chain (Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS12⁻ ∷ Sw01 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS02⁻ ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b22 = at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (CS12⁻ ∷ CS13 ∷ []) wn00198 ▸
       at 0 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b23 : Chain (CS02⁻ ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS02⁻ ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b23 = at 2 2 [] wn00031 ▸ done

-- pass [CS03 CS03 CK03 CS03 CK03 CK03 CX01 CK13 S1 CK13 S1 CS13 CS13 CS13 CK13 S1 CS13 CS13 CS13 CS13 CS13 CS13 CX01 CS13 CS13 CK13 CS13 CK13 CK13] [X0 CKd02 X0]: 251 steps
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-X0-CKd02-X0 : ⟪ (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02⁻ ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-X0-CKd02-X0 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (run b31)))))))))))))))))))))))))))))))
  where
  b0 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ X0 ∷ CK13 ∷ CK02⁻ ∷ X0 ∷ CK13 ∷ [])
  b0 = at 28 2 (X0 ∷ CK13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CK₀₁ • Swap ↑)))) ▸
       at 30 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 29 2 (Sw12 ∷ CK23 ∷ []) wn01052 ▸
       at 30 2 (CK01⁻ ∷ CK23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CK₀₁))) ▸
       at 31 2 (Sw12 ∷ CK13 ∷ []) wn01053 ▸
       at 29 3 (CK02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 30 2 (X0 ∷ CK13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CK₀₁ • Swap ↑)))) ▸
       at 27 2 (X0 ∷ CK13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CK₀₁ • Swap ↑)))) ▸ done

  b1 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ X0 ∷ CK13 ∷ CK02⁻ ∷ X0 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ X0 ∷ CS13 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ X0 ∷ CK13 ∷ CK13 ∷ [])
  b1 = at 29 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 28 2 (Sw12 ∷ CK23 ∷ []) wn01052 ▸
       at 29 2 (CK01⁻ ∷ CK23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CK₀₁))) ▸
       at 30 2 (Sw12 ∷ CK13 ∷ []) wn01053 ▸
       at 28 3 (CK02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 29 2 (X0 ∷ CK13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CK₀₁ • Swap ↑)))) ▸
       at 26 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 28 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ X0 ∷ CS13 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ X0 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ X0 ∷ Sw12 ∷ CK23 ∷ CK01⁻ ∷ Sw12 ∷ X0 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b2 = at 27 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 28 2 (CK01⁻ ∷ CS23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CS))) ▸
       at 29 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 27 3 (CK02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 28 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 25 2 (X0 ∷ CK13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CK₀₁ • Swap ↑)))) ▸
       at 27 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 (Sw12 ∷ CK23 ∷ []) wn01052 ▸ done

  b3 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ X0 ∷ Sw12 ∷ CK23 ∷ CK01⁻ ∷ Sw12 ∷ X0 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ X0 ∷ Sw12 ∷ CK01⁻ ∷ CS23 ∷ Sw12 ∷ X0 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b3 = at 27 2 (CK01⁻ ∷ CK23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CK₀₁))) ▸
       at 28 2 (Sw12 ∷ CK13 ∷ []) wn01053 ▸
       at 26 3 (CK02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 27 2 (X0 ∷ CK13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CK₀₁ • Swap ↑)))) ▸
       at 24 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 26 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 25 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 26 2 (CK01⁻ ∷ CS23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CS))) ▸ done

  b4 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ X0 ∷ Sw12 ∷ CK01⁻ ∷ CS23 ∷ Sw12 ∷ X0 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ X0 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ CS13 ∷ X0 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b4 = at 27 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 25 3 (CK02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 23 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 25 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 24 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 25 2 (CK01⁻ ∷ CS23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CS))) ▸
       at 26 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸ done

  b5 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ X0 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ CS13 ∷ X0 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ CS13 ∷ X0 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b5 = at 24 3 (CK02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 25 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 22 4 (X0 ∷ CK02⁻ ∷ X0 ∷ CX01 ∷ []) wn01271 ▸
       at 21 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 23 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 22 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 23 2 (CK01⁻ ∷ CS23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CS))) ▸
       at 24 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸ done

  b6 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ CS13 ∷ X0 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CK02⁻ ∷ CS13 ∷ X0 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b6 = at 22 3 (CK02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 20 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 22 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 22 2 (CK01⁻ ∷ CS23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CS))) ▸
       at 23 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 21 3 (CK02⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b7 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CK02⁻ ∷ CS13 ∷ X0 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b7 = at 22 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 19 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 21 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 21 2 (CK01⁻ ∷ CS23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CS))) ▸
       at 22 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 20 3 (CK02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸ done

  b8 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ X0 ∷ CS13 ∷ CK02⁻ ∷ X0 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b8 = at 18 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 20 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 20 2 (CK01⁻ ∷ CS23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CS))) ▸
       at 21 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 19 3 (CK02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 17 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸ done

  b9 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ X0 ∷ CS13 ∷ CK02⁻ ∷ X0 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ X0 ∷ CS13 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ X0 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b9 = at 19 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 19 2 (CK01⁻ ∷ CS23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CS))) ▸
       at 20 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 18 3 (CK02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 16 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 18 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ X0 ∷ CS13 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ X0 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b10 = at 17 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 18 2 (CK01⁻ ∷ CS23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CS))) ▸
       at 19 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 17 3 (CK02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 15 2 (X0 ∷ S1 ∷ []) (sym (low₁-comm (X) (S))) ▸
       at 16 2 (CK02⁻ ∷ S1 ∷ []) wn01272 ▸
       at 17 2 (X0 ∷ S1 ∷ []) (sym (low₁-comm (X) (S))) ▸ done

  b11 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ X0 ∷ CS13 ∷ CK02⁻ ∷ X0 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b11 = at 14 2 (X0 ∷ CK13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CK₀₁ • Swap ↑)))) ▸
       at 16 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw12 ∷ CK23 ∷ []) wn01052 ▸
       at 16 2 (CK01⁻ ∷ CK23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CK₀₁))) ▸
       at 17 2 (Sw12 ∷ CK13 ∷ []) wn01053 ▸
       at 15 3 (CK02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (X0 ∷ CK13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CK₀₁ • Swap ↑)))) ▸
       at 13 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸ done

  b12 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ X0 ∷ CS13 ∷ CK02⁻ ∷ X0 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ X0 ∷ CS13 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ X0 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b12 = at 15 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 15 2 (CK01⁻ ∷ CS23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CS))) ▸
       at 16 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 14 3 (CK02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 12 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 14 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ X0 ∷ CS13 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ X0 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ X0 ∷ Sw12 ∷ CS23 ∷ CK01⁻ ∷ Sw12 ∷ X0 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b13 = at 13 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 14 2 (CK01⁻ ∷ CS23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CS))) ▸
       at 15 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 13 3 (CK02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 11 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 13 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸ done

  b14 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ X0 ∷ Sw12 ∷ CS23 ∷ CK01⁻ ∷ Sw12 ∷ X0 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ X0 ∷ CK13 ∷ CK02⁻ ∷ X0 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b14 = at 13 2 (CK01⁻ ∷ CS23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CS))) ▸
       at 14 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 12 3 (CK02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (X0 ∷ CS13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))) ▸
       at 10 2 (X0 ∷ S1 ∷ []) (sym (low₁-comm (X) (S))) ▸
       at 11 2 (CK02⁻ ∷ S1 ∷ []) wn01272 ▸
       at 12 2 (X0 ∷ S1 ∷ []) (sym (low₁-comm (X) (S))) ▸
       at 9 2 (X0 ∷ CK13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CK₀₁ • Swap ↑)))) ▸ done

  b15 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ X0 ∷ CK13 ∷ CK02⁻ ∷ X0 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ X0 ∷ CK02⁻ ∷ S1 ∷ X0 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b15 = at 11 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw12 ∷ CK23 ∷ []) wn01052 ▸
       at 11 2 (CK01⁻ ∷ CK23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CK₀₁))) ▸
       at 12 2 (Sw12 ∷ CK13 ∷ []) wn01053 ▸
       at 10 3 (CK02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (X0 ∷ CK13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CK₀₁ • Swap ↑)))) ▸
       at 8 2 (X0 ∷ S1 ∷ []) (sym (low₁-comm (X) (S))) ▸
       at 9 2 (CK02⁻ ∷ S1 ∷ []) wn01272 ▸ done

  b16 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ X0 ∷ CK02⁻ ∷ S1 ∷ X0 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b16 = at 10 2 (X0 ∷ S1 ∷ []) (sym (low₁-comm (X) (S))) ▸
       at 7 2 (X0 ∷ CK13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CK₀₁ • Swap ↑)))) ▸
       at 9 1 (Sw12 ∷ CK01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw12 ∷ CK23 ∷ []) wn01052 ▸
       at 9 2 (CK01⁻ ∷ CK23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CK₀₁))) ▸
       at 10 2 (Sw12 ∷ CK13 ∷ []) wn01053 ▸
       at 8 3 (CK02⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (X0 ∷ CK13 ∷ []) (sym (low₁-comm (X) ((Swap ↑ • CK₀₁ • Swap ↑)))) ▸ done

  b17 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ Sw23 ∷ Sw01 ∷ CK12 ∷ Sw23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ Sw01 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b17 = at 6 4 (X0 ∷ CK02⁻ ∷ X0 ∷ CX01 ∷ []) wn01271 ▸
       at 9 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 8 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 7 2 (Sw01 ∷ CK12⁻ ∷ []) wn01228 ▸
       at 6 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 5 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 2 (Sw01 ∷ CK12 ∷ []) wn00772 ▸ done

  b18 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ Sw23 ∷ Sw01 ∷ CK12 ∷ Sw23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ Sw01 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ Sw01 ∷ CK12 ∷ Sw23 ∷ Sw01 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b18 = at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 4 (X1 ∷ CK12⁻ ∷ X1 ∷ CK13 ∷ []) wn01314 ▸
       at 5 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 6 2 (CK02⁻ ∷ Sw01 ∷ []) wn00330 ▸
       at 7 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 9 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b19 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ Sw01 ∷ CK12 ∷ Sw23 ∷ Sw01 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ Sw01 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ Sw01 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b19 = at 9 2 (CK02 ∷ Sw01 ∷ []) wn00329 ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00031 ▸
       at 8 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 7 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 6 2 (Sw01 ∷ CK12⁻ ∷ []) wn01228 ▸
       at 5 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸ done

  b20 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ Sw01 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ Sw01 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ X0 ∷ CK02⁻ ∷ Sw01 ∷ X1 ∷ CK13 ∷ Sw01 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b20 = at 4 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 2 (Sw01 ∷ CK12 ∷ []) wn00772 ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 4 (X1 ∷ CK12⁻ ∷ X1 ∷ CK13 ∷ []) wn01314 ▸
       at 4 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 5 2 (CK02⁻ ∷ Sw01 ∷ []) wn00330 ▸ done

  b21 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ X0 ∷ CK02⁻ ∷ Sw01 ∷ X1 ∷ CK13 ∷ Sw01 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw01 ∷ Sw01 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b21 = at 6 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 8 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CK02 ∷ Sw01 ∷ []) wn00329 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00031 ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b22 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw01 ∷ Sw01 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ Sw01 ∷ CS13 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ Sw01 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b22 = at 6 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 5 2 (Sw01 ∷ CK12⁻ ∷ []) wn01228 ▸
       at 4 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b23 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ Sw01 ∷ CS13 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ Sw01 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b23 = at 4 4 (X1 ∷ CK12⁻ ∷ X1 ∷ CS13 ∷ []) wn01315 ▸
       at 3 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 4 2 (CK02⁻ ∷ Sw01 ∷ []) wn00330 ▸
       at 5 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b24 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ Sw23 ∷ CK02 ∷ Sw01 ∷ Sw23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ Sw01 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b24 = at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00031 ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 5 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 4 2 (Sw01 ∷ CK12⁻ ∷ []) wn01228 ▸
       at 3 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 2 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b25 : Chain (CS03 ∷ CS03 ∷ Sw23 ∷ CK02 ∷ Sw01 ∷ Sw23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ Sw01 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw01 ∷ Sw23 ∷ CK12 ∷ Sw23 ∷ Sw01 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b25 = at 3 2 (Sw01 ∷ CK12 ∷ []) wn00772 ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 4 (X1 ∷ CK12⁻ ∷ X1 ∷ CK13 ∷ []) wn01314 ▸
       at 2 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 3 2 (CK02⁻ ∷ Sw01 ∷ []) wn00330 ▸
       at 4 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 6 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b26 : Chain (CS03 ∷ CS03 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw01 ∷ Sw23 ∷ CK12 ∷ Sw23 ∷ Sw01 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ CS03 ∷ X0 ∷ Sw01 ∷ CK12⁻ ∷ X1 ∷ Sw01 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b26 = at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CK02 ∷ Sw01 ∷ []) wn00329 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00031 ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 3 2 (Sw01 ∷ CK12⁻ ∷ []) wn01228 ▸ done

  b27 : Chain (CS03 ∷ CS03 ∷ X0 ∷ Sw01 ∷ CK12⁻ ∷ X1 ∷ Sw01 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ X0 ∷ Sw01 ∷ CK12⁻ ∷ X1 ∷ CS13 ∷ Sw01 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b27 = at 2 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 1 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 2 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 2 4 (X1 ∷ CK12⁻ ∷ X1 ∷ CS13 ∷ []) wn01315 ▸
       at 1 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸ done

  b28 : Chain (CS03 ∷ X0 ∷ Sw01 ∷ CK12⁻ ∷ X1 ∷ CS13 ∷ Sw01 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS03 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b28 = at 2 2 (CK02⁻ ∷ Sw01 ∷ []) wn00330 ▸
       at 3 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00031 ▸ done

  b29 : Chain (CS03 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ Sw01 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b29 = at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 2 2 (Sw01 ∷ CK12⁻ ∷ []) wn01228 ▸
       at 1 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 1 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 0 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b30 : Chain (Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ Sw01 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b30 = at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 1 4 (X1 ∷ CK12⁻ ∷ X1 ∷ CS13 ∷ []) wn01315 ▸
       at 0 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 1 2 (CK02⁻ ∷ Sw01 ∷ []) wn00330 ▸
       at 2 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸ done

  b31 : Chain (X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (X0 ∷ CK02⁻ ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b31 = at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00031 ▸ done
