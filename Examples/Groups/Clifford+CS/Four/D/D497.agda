{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D497 where

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
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00003 ; wn00107 ; wn00108 ; wn00190)
open import Examples.Groups.Clifford+CS.Four.Wins.W25 using (wn01257 ; wn01258 ; wn01260 ; wn01261)
open import Examples.Groups.Clifford+CS.Four.Wins.W26 using (wn01310)

-- pass [CS03 CS03 CK03 CS03 CK03 CK03 CX01 CK13 S1 CK13 S1 CS13 CS13 CS13 CK13 S1 CS13 CS13 CS13 CS13 CS13 CS13 CX01 CS13 CS13 CK13 CS13 CK13 CK13] [CZ12]: 391 steps
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-CZ12 : ⟪ (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-CZ12 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (run b48))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CZ12 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CK12 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ CZ12 ∷ [])
  b0 = at 29 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 28 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 30 2 [] wn00003 ▸
       at 27 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 29 2 [] wn00003 ▸
       at 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 28 2 [] wn00003 ▸
       at 25 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CK12 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ CZ12 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ CZ12 ∷ [])
  b1 = at 27 2 [] wn00003 ▸
       at 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 [] wn00003 ▸
       at 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 25 2 [] wn00003 ▸
       at 22 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 [] wn00003 ▸ done

  b2 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ CZ12 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ CZ12 ∷ [])
  b2 = at 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 22 2 [] wn00003 ▸
       at 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 [] wn00003 ▸
       at 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 [] wn00003 ▸
       at 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 [] wn00003 ▸ done

  b3 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ CZ12 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ CZ12 ∷ [])
  b3 = at 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 [] wn00003 ▸
       at 15 2 (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap)) ▸
       at 14 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 [] wn00003 ▸
       at 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] wn00003 ▸
       at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ CZ12 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ Sw23 ∷ CK12 ∷ Sw23 ∷ Sw23 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ CZ12 ∷ [])
  b4 = at 14 2 [] wn00003 ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] wn00003 ▸
       at 10 2 (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap)) ▸
       at 9 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 8 2 (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap)) ▸
       at 7 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ Sw23 ∷ CK12 ∷ Sw23 ∷ Sw23 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ CZ12 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ Sw23 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ CZ12 ∷ [])
  b5 = at 9 2 [] wn00003 ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 4 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸ done

  b6 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ Sw23 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ CZ12 ∷ []) (Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX10 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX10 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ CZ12 ∷ [])
  b6 = at 2 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 29 (CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX10 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX10 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ []) wn01257 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b7 : Chain (Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX10 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX10 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ CZ12 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ Sw23 ∷ CK12 ∷ Sw23 ∷ Sw23 ∷ CK12 ∷ CX10 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX10 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ CZ12 ∷ [])
  b7 = at 0 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b8 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ Sw23 ∷ CK12 ∷ Sw23 ∷ Sw23 ∷ CK12 ∷ CX10 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX10 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ CZ12 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ Sw23 ∷ CK02 ∷ Sw23 ∷ Sw23 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX10 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ CZ12 ∷ [])
  b8 = at 4 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b9 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ Sw23 ∷ CK02 ∷ Sw23 ∷ Sw23 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX10 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ CZ12 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX10 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ CZ12 ∷ [])
  b9 = at 9 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 13 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX10 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ CZ12 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX10 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ CZ12 ∷ [])
  b10 = at 16 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 14 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 18 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 16 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 19 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 17 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 20 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b11 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX10 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ CZ12 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ CZ12 ∷ [])
  b11 = at 18 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 21 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 19 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 22 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 20 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 23 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 21 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 22 2 (CX10 ∷ Sw23 ∷ []) (sym (low-comm (CX₁₀) (Swap))) ▸ done

  b12 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ CZ12 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ Sw23 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ CZ12 ∷ [])
  b12 = at 25 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 23 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 26 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 24 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 27 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 25 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 28 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 26 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ Sw23 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ CZ12 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ CZ13 ∷ Sw23 ∷ [])
  b13 = at 29 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 27 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 30 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 28 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 29 2 [] wn00003 ▸
       at 28 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 34 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 32 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸ done

  b14 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ CZ13 ∷ Sw23 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw23 ∷ CK03 ∷ [])
  b14 = at 31 2 (CZ23 ∷ Sw12 ∷ []) wn00107 ▸
       at 30 2 (CZ23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CZ)) ▸
       at 29 2 (CZ13 ∷ Sw12 ∷ []) wn00108 ▸
       at 29 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 28 2 [] wn00003 ▸
       at 29 5 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 27 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 33 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b15 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw23 ∷ CK03 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CZ12 ∷ CK03 ∷ CK03 ∷ [])
  b15 = at 31 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 30 2 (CZ23 ∷ Sw12 ∷ []) wn00107 ▸
       at 29 2 (CZ23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CZ)) ▸
       at 28 2 (CZ13 ∷ Sw12 ∷ []) wn00108 ▸
       at 28 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 27 2 [] wn00003 ▸
       at 28 5 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b16 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CZ12 ∷ CK03 ∷ CK03 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CZ12 ∷ CS03 ∷ CK03 ∷ CK03 ∷ [])
  b16 = at 32 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 30 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 29 2 (CZ23 ∷ Sw12 ∷ []) wn00107 ▸
       at 28 2 (CZ23 ∷ CS01 ∷ []) (low-comm (CS) (CZ)) ▸
       at 27 2 (CZ13 ∷ Sw12 ∷ []) wn00108 ▸
       at 27 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 [] wn00003 ▸
       at 27 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b17 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CZ12 ∷ CS03 ∷ CK03 ∷ CK03 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CZ12 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ CS03 ∷ CK03 ∷ CK03 ∷ [])
  b17 = at 25 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 31 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 29 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 28 2 (CZ23 ∷ Sw12 ∷ []) wn00107 ▸
       at 27 2 (CZ23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CZ)) ▸
       at 26 2 (CZ13 ∷ Sw12 ∷ []) wn00108 ▸
       at 26 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 25 2 [] wn00003 ▸ done

  b18 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CZ12 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ CS03 ∷ CK03 ∷ CK03 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ [])
  b18 = at 26 5 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 30 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 28 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 27 2 (CZ23 ∷ Sw12 ∷ []) wn00107 ▸
       at 26 2 (CZ23 ∷ CS01 ∷ []) (low-comm (CS) (CZ)) ▸
       at 25 2 (CZ13 ∷ Sw12 ∷ []) wn00108 ▸
       at 25 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b19 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ Sw23 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ Sw23 ∷ CZ13 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ [])
  b19 = at 24 2 [] wn00003 ▸
       at 25 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 29 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 27 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 (CZ23 ∷ Sw12 ∷ []) wn00107 ▸
       at 25 2 (CZ23 ∷ CS01 ∷ []) (low-comm (CS) (CZ)) ▸
       at 24 2 (CZ13 ∷ Sw12 ∷ []) wn00108 ▸ done

  b20 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ Sw23 ∷ CZ13 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ CZ23 ∷ Sw12 ∷ Sw23 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ [])
  b20 = at 24 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 [] wn00003 ▸
       at 24 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 22 2 (CZ12 ∷ CX10 ∷ []) wn01258 ▸
       at 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 27 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 25 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 24 2 (CZ23 ∷ Sw12 ∷ []) wn00107 ▸ done

  b21 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ CZ23 ∷ Sw12 ∷ Sw23 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ CZ13 ∷ Sw23 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ [])
  b21 = at 23 2 (CZ23 ∷ CS01 ∷ []) (low-comm (CS) (CZ)) ▸
       at 22 2 (CZ13 ∷ Sw12 ∷ []) wn00108 ▸
       at 22 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 [] wn00003 ▸
       at 22 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 26 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 24 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸ done

  b22 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ CZ13 ∷ Sw23 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ [])
  b22 = at 23 2 (CZ23 ∷ Sw12 ∷ []) wn00107 ▸
       at 22 2 (CZ23 ∷ CS01 ∷ []) (low-comm (CS) (CZ)) ▸
       at 21 2 (CZ13 ∷ Sw12 ∷ []) wn00108 ▸
       at 21 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 [] wn00003 ▸
       at 21 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 25 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b23 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CZ12 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ [])
  b23 = at 23 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 22 2 (CZ23 ∷ Sw12 ∷ []) wn00107 ▸
       at 21 2 (CZ23 ∷ CS01 ∷ []) (low-comm (CS) (CZ)) ▸
       at 20 2 (CZ13 ∷ Sw12 ∷ []) wn00108 ▸
       at 20 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 [] wn00003 ▸
       at 20 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b24 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CZ12 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CZ12 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ [])
  b24 = at 24 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 22 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 (CZ23 ∷ Sw12 ∷ []) wn00107 ▸
       at 20 2 (CZ23 ∷ CS01 ∷ []) (low-comm (CS) (CZ)) ▸
       at 19 2 (CZ13 ∷ Sw12 ∷ []) wn00108 ▸
       at 19 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 [] wn00003 ▸
       at 19 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b25 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CZ12 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CZ12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ [])
  b25 = at 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 23 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 21 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 (CZ23 ∷ Sw12 ∷ []) wn00107 ▸
       at 19 2 (CZ23 ∷ CS01 ∷ []) (low-comm (CS) (CZ)) ▸
       at 18 2 (CZ13 ∷ Sw12 ∷ []) wn00108 ▸
       at 18 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 [] wn00003 ▸ done

  b26 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CZ12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ Sw23 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ [])
  b26 = at 18 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 16 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 22 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 20 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 (CZ23 ∷ Sw12 ∷ []) wn00107 ▸
       at 18 2 (CZ23 ∷ CS01 ∷ []) (low-comm (CS) (CZ)) ▸
       at 17 2 (CZ13 ∷ Sw12 ∷ []) wn00108 ▸
       at 17 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b27 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ Sw23 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ [])
  b27 = at 16 2 [] wn00003 ▸
       at 17 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (CZ12 ∷ S0 ∷ []) (low₁-comm (S) (CZ)) ▸
       at 14 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 20 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 18 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (CZ23 ∷ Sw12 ∷ []) wn00107 ▸
       at 16 2 (CZ23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CZ)) ▸ done

  b28 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CZ23 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ CZ23 ∷ Sw12 ∷ Sw23 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ [])
  b28 = at 15 2 (CZ13 ∷ Sw12 ∷ []) wn00108 ▸
       at 15 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 15 5 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 19 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 17 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (CZ23 ∷ Sw12 ∷ []) wn00107 ▸ done

  b29 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ CZ23 ∷ Sw12 ∷ Sw23 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ CZ13 ∷ Sw23 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ [])
  b29 = at 15 2 (CZ23 ∷ CS01 ∷ []) (low-comm (CS) (CZ)) ▸
       at 14 2 (CZ13 ∷ Sw12 ∷ []) wn00108 ▸
       at 14 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] wn00003 ▸
       at 14 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 18 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 16 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸ done

  b30 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ CZ13 ∷ Sw23 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ [])
  b30 = at 15 2 (CZ23 ∷ Sw12 ∷ []) wn00107 ▸
       at 14 2 (CZ23 ∷ CS01 ∷ []) (low-comm (CS) (CZ)) ▸
       at 13 2 (CZ13 ∷ Sw12 ∷ []) wn00108 ▸
       at 13 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 13 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b31 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ CZ12 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ [])
  b31 = at 15 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (CZ23 ∷ Sw12 ∷ []) wn00107 ▸
       at 13 2 (CZ23 ∷ CS01 ∷ []) (low-comm (CS) (CZ)) ▸
       at 12 2 (CZ13 ∷ Sw12 ∷ []) wn00108 ▸
       at 12 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 12 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CZ12 ∷ S0 ∷ []) (low₁-comm (S) (CZ)) ▸ done

  b32 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ CZ12 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CZ12 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ [])
  b32 = at 9 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 13 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (CZ23 ∷ Sw12 ∷ []) wn00107 ▸
       at 11 2 (CZ23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CZ)) ▸
       at 10 2 (CZ13 ∷ Sw12 ∷ []) wn00108 ▸
       at 10 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸ done

  b33 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CZ12 ∷ Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ Sw23 ∷ CZ13 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ [])
  b33 = at 10 5 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CZ12 ∷ S0 ∷ []) (low₁-comm (S) (CZ)) ▸
       at 7 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 3 (CZ13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CZ23 ∷ Sw12 ∷ []) wn00107 ▸
       at 9 2 (CZ23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CZ)) ▸
       at 8 2 (CZ13 ∷ Sw12 ∷ []) wn00108 ▸ done

  b34 : Chain (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ Sw23 ∷ CZ13 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ []) (CS13 ∷ CS13 ∷ CZ12 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ [])
  b34 = at 8 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 8 5 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (CZ12 ∷ CX10 ∷ []) wn01258 ▸
       at 5 2 (CZ12 ∷ CK13 ∷ []) wn01310 ▸
       at 4 2 (CZ12 ∷ CK13 ∷ []) wn01310 ▸
       at 3 2 (CZ12 ∷ CS13 ∷ []) wn00190 ▸
       at 2 2 (CZ12 ∷ CK13 ∷ []) wn01310 ▸ done

  b35 : Chain (CS13 ∷ CS13 ∷ CZ12 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ []) (CZ12 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ [])
  b35 = at 1 2 (CZ12 ∷ CS13 ∷ []) wn00190 ▸
       at 0 2 (CZ12 ∷ CS13 ∷ []) wn00190 ▸
       at 30 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 29 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 31 2 [] wn00003 ▸
       at 28 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 30 2 [] wn00003 ▸
       at 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b36 : Chain (CZ12 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX10 ∷ CS03 ∷ CS03 ∷ CK03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ []) (CZ12 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CX10 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ [])
  b36 = at 29 2 [] wn00003 ▸
       at 26 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 28 2 [] wn00003 ▸
       at 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 27 2 [] wn00003 ▸
       at 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 [] wn00003 ▸
       at 23 2 (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap)) ▸ done

  b37 : Chain (CZ12 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CX10 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ []) (CZ12 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX10 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ [])
  b37 = at 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 24 2 [] wn00003 ▸
       at 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 [] wn00003 ▸
       at 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 22 2 [] wn00003 ▸
       at 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 [] wn00003 ▸ done

  b38 : Chain (CZ12 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX10 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ []) (CZ12 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX10 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ [])
  b38 = at 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 [] wn00003 ▸
       at 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 [] wn00003 ▸
       at 16 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 15 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 [] wn00003 ▸
       at 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b39 : Chain (CZ12 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ CK03 ∷ S0 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX10 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ []) (CZ12 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ Sw23 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX10 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ [])
  b39 = at 16 2 [] wn00003 ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] wn00003 ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 11 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 10 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸ done

  b40 : Chain (CZ12 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX10 ∷ CK03 ∷ S0 ∷ Sw23 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX10 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ []) (CZ12 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ Sw23 ∷ CK12 ∷ CK12 ∷ CX10 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX10 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ [])
  b40 = at 9 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 8 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 7 2 (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap)) ▸
       at 6 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 5 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸ done

  b41 : Chain (CZ12 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ Sw23 ∷ CK12 ∷ CK12 ∷ CX10 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX10 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ []) (CZ12 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX10 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX10 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ [])
  b41 = at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 3 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸ done

  b42 : Chain (CZ12 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX10 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX10 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ Sw23 ∷ []) (CZ12 ∷ CS03 ∷ CS03 ∷ CK03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ [])
  b42 = at 2 29 (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) wn01260 ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b43 : Chain (CZ12 ∷ CS03 ∷ CS03 ∷ CK03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ []) (CZ12 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ Sw23 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ [])
  b43 = at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸ done

  b44 : Chain (CZ12 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ Sw23 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ []) (CZ12 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ [])
  b44 = at 9 2 (S1 ∷ Sw23 ∷ []) (sym (low-comm ((S ↑)) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (S1 ∷ Sw23 ∷ []) (sym (low-comm ((S ↑)) (Swap))) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 13 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b45 : Chain (CZ12 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ []) (CZ12 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ [])
  b45 = at 16 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 14 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 17 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 15 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (S1 ∷ Sw23 ∷ []) (sym (low-comm ((S ↑)) (Swap))) ▸
       at 19 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 17 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 20 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b46 : Chain (CZ12 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ []) (CZ12 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ [])
  b46 = at 18 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 21 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 19 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 22 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 20 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 23 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 21 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 24 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b47 : Chain (CZ12 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ []) (CZ12 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ Sw23 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ [])
  b47 = at 22 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 26 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 24 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 27 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 25 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 28 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 26 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸ done

  b48 : Chain (CZ12 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ Sw23 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ []) (CZ12 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b48 = at 29 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 27 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 30 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 28 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 31 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 29 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 30 2 [] wn00003 ▸ done

-- pass [CS03 CS03 CK03 CS03 CK03 CK03 CX01 CK13 S1 CK13 S1 CS13 CS13 CS13 CK13 S1 CS13 CS13 CS13 CS13 CS13 CS13 CX01 CS13 CS13 CK13 CS13 CK13 CK13] [CS01]: 111 steps
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-CS01 : ⟪ (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-CS01 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CS01 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ Sw23 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CS01 ∷ Sw23 ∷ [])
  b0 = at 30 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 29 2 (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap)) ▸
       at 28 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 30 2 [] wn00003 ▸
       at 27 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 29 2 [] wn00003 ▸
       at 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 28 2 [] wn00003 ▸ done

  b1 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ Sw23 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CS01 ∷ Sw23 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CS01 ∷ Sw23 ∷ [])
  b1 = at 25 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 27 2 [] wn00003 ▸
       at 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 [] wn00003 ▸
       at 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 25 2 [] wn00003 ▸
       at 22 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CS01 ∷ Sw23 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CS01 ∷ Sw23 ∷ [])
  b2 = at 23 2 [] wn00003 ▸
       at 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 22 2 [] wn00003 ▸
       at 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 [] wn00003 ▸
       at 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 [] wn00003 ▸
       at 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CS01 ∷ Sw23 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CS01 ∷ Sw23 ∷ [])
  b3 = at 19 2 [] wn00003 ▸
       at 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 [] wn00003 ▸
       at 15 2 (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap)) ▸
       at 14 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 [] wn00003 ▸
       at 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 [] wn00003 ▸ done

  b4 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CS01 ∷ Sw23 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ Sw23 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CS01 ∷ Sw23 ∷ [])
  b4 = at 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] wn00003 ▸
       at 10 2 (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap)) ▸
       at 9 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 8 2 (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap)) ▸ done

  b5 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ Sw23 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CS01 ∷ Sw23 ∷ []) (CS03 ∷ CS03 ∷ CK03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CS01 ∷ Sw23 ∷ [])
  b5 = at 7 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 5 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 4 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (CS03 ∷ CS03 ∷ CK03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ [])
  b6 = at 5 2 [] wn00003 ▸
       at 2 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 30 (CS01 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) wn01261 ▸ done

  b7 : Chain (Sw23 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ []) (CS01 ∷ CS03 ∷ CS03 ∷ CK03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ [])
  b7 = at 0 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b8 : Chain (CS01 ∷ CS03 ∷ CS03 ∷ CK03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ []) (CS01 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ Sw23 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ [])
  b8 = at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CK03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸ done

  b9 : Chain (CS01 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ Sw23 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ []) (CS01 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ [])
  b9 = at 9 2 (S1 ∷ Sw23 ∷ []) (sym (low-comm ((S ↑)) (Swap))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 10 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (S1 ∷ Sw23 ∷ []) (sym (low-comm ((S ↑)) (Swap))) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 12 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 13 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b10 : Chain (CS01 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ []) (CS01 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ [])
  b10 = at 16 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 14 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 17 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 15 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (S1 ∷ Sw23 ∷ []) (sym (low-comm ((S ↑)) (Swap))) ▸
       at 19 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 17 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 20 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b11 : Chain (CS01 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ []) (CS01 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ [])
  b11 = at 18 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 21 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 19 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 22 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 20 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 23 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 21 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 24 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b12 : Chain (CS01 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ []) (CS01 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ Sw23 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ [])
  b12 = at 22 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 26 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 24 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 27 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 25 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 28 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 26 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸ done

  b13 : Chain (CS01 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ Sw23 ∷ CS12 ∷ CK12 ∷ CK12 ∷ Sw23 ∷ []) (CS01 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  b13 = at 29 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 27 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 30 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 28 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 31 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 29 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 30 2 [] wn00003 ▸ done
