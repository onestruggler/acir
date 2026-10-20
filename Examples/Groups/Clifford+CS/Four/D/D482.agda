{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D482 where

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
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00003 ; wn00005 ; wn00007 ; wn00027 ; wn00031 ; wn00048 ; wn00065)
open import Examples.Groups.Clifford+CS.Four.Wins.W02 using (wn00317 ; wn00329 ; wn00330)
open import Examples.Groups.Clifford+CS.Four.Wins.W10 using (wn00772)
open import Examples.Groups.Clifford+CS.Four.Wins.W20 using (wn01052 ; wn01053)
open import Examples.Groups.Clifford+CS.Four.Wins.W21 using (wn01106)
open import Examples.Groups.Clifford+CS.Four.Wins.W24 using (wn01228)
open import Examples.Groups.Clifford+CS.Four.Wins.W25 using (wn01271 ; wn01272 ; wn01273 ; wn01274)

-- pass [CS02 CS02 CK02 CS02 CK02 CK02 CX01 CK12 S1 CK12 S1 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CX01 CS12 CS12 CK12 CS12 CK12 CK12] [X0 CKd03 X0]: 371 steps
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-vs-X0-CKd03-X0 : ⟪ (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK03⁻ ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-vs-X0-CKd03-X0 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (run b46))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ X0 ∷ Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ CK12 ∷ Sw23 ∷ Sw23 ∷ X0 ∷ [])
  b0 = at 28 2 (X0 ∷ CK12 ∷ []) (sym (low₁-comm (X) (CK₀₁))) ▸
       at 30 1 (Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 29 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 30 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 30 2 (Sw12 ∷ CK23 ∷ []) wn01052 ▸
       at 31 2 (CK01⁻ ∷ CK23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CK₀₁))) ▸
       at 32 2 (Sw12 ∷ CK13 ∷ []) wn01053 ▸
       at 33 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ X0 ∷ Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ CK12 ∷ Sw23 ∷ Sw23 ∷ X0 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ X0 ∷ Sw23 ∷ Sw12 ∷ CK23 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ X0 ∷ CK12 ∷ [])
  b1 = at 35 2 [] wn00003 ▸
       at 29 5 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 30 2 (X0 ∷ CK12 ∷ []) (sym (low₁-comm (X) (CK₀₁))) ▸
       at 27 2 (X0 ∷ CK12 ∷ []) (sym (low₁-comm (X) (CK₀₁))) ▸
       at 29 1 (Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 28 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 29 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 29 2 (Sw12 ∷ CK23 ∷ []) wn01052 ▸ done

  b2 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ X0 ∷ Sw23 ∷ Sw12 ∷ CK23 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ X0 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ X0 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ X0 ∷ CK12 ∷ CK12 ∷ [])
  b2 = at 30 2 (CK01⁻ ∷ CK23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CK₀₁))) ▸
       at 31 2 (Sw12 ∷ CK13 ∷ []) wn01053 ▸
       at 32 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 34 2 [] wn00003 ▸
       at 28 5 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 29 2 (X0 ∷ CK12 ∷ []) (sym (low₁-comm (X) (CK₀₁))) ▸
       at 26 2 (X0 ∷ CS12 ∷ []) (sym (low₁-comm (X) (CS))) ▸
       at 28 1 (Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ X0 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ X0 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ X0 ∷ CK03⁻ ∷ CS12 ∷ X0 ∷ CK12 ∷ CK12 ∷ [])
  b3 = at 27 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 28 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 28 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 29 2 (CK01⁻ ∷ CS23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CS))) ▸
       at 30 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 33 2 [] wn00003 ▸
       at 27 5 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b4 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ X0 ∷ CK03⁻ ∷ CS12 ∷ X0 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ X0 ∷ Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ CK13 ∷ Sw23 ∷ X0 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b4 = at 28 2 (X0 ∷ CS12 ∷ []) (sym (low₁-comm (X) (CS))) ▸
       at 25 2 (X0 ∷ CK12 ∷ []) (sym (low₁-comm (X) (CK₀₁))) ▸
       at 27 1 (Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 26 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 27 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 27 2 (Sw12 ∷ CK23 ∷ []) wn01052 ▸
       at 28 2 (CK01⁻ ∷ CK23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CK₀₁))) ▸
       at 29 2 (Sw12 ∷ CK13 ∷ []) wn01053 ▸ done

  b5 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ X0 ∷ Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ CK13 ∷ Sw23 ∷ X0 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ X0 ∷ Sw23 ∷ CS13 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ X0 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b5 = at 30 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 32 2 [] wn00003 ▸
       at 26 5 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 27 2 (X0 ∷ CK12 ∷ []) (sym (low₁-comm (X) (CK₀₁))) ▸
       at 24 2 (X0 ∷ CS12 ∷ []) (sym (low₁-comm (X) (CS))) ▸
       at 26 1 (Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 25 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 26 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b6 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ X0 ∷ Sw23 ∷ CS13 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ X0 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ X0 ∷ CS12 ∷ CK03⁻ ∷ X0 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b6 = at 26 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 27 2 (CK01⁻ ∷ CS23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CS))) ▸
       at 28 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 31 2 [] wn00003 ▸
       at 25 5 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 (X0 ∷ CS12 ∷ []) (sym (low₁-comm (X) (CS))) ▸
       at 23 2 (X0 ∷ CS12 ∷ []) (sym (low₁-comm (X) (CS))) ▸ done

  b7 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ X0 ∷ CS12 ∷ CK03⁻ ∷ X0 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ X0 ∷ Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ X0 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b7 = at 25 1 (Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 24 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 25 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 25 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 26 2 (CK01⁻ ∷ CS23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CS))) ▸
       at 27 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 30 2 [] wn00003 ▸ done

  b8 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ X0 ∷ Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ X0 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b8 = at 24 5 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 25 2 (X0 ∷ CS12 ∷ []) (sym (low₁-comm (X) (CS))) ▸
       at 26 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 25 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 24 1 (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 [] wn00003 ▸
       at 23 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 22 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸ done

  b9 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sw23 ∷ CX01 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ CS12 ∷ CK03⁻ ∷ X0 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b9 = at 23 4 (X0 ∷ CK02⁻ ∷ X0 ∷ CX01 ∷ []) wn01271 ▸
       at 22 2 (X0 ∷ Sw23 ∷ []) (sym (low₁-comm (X) ((Swap ↑)))) ▸
       at 25 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 23 3 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 24 2 (X0 ∷ Sw23 ∷ []) (sym (low₁-comm (X) ((Swap ↑)))) ▸
       at 25 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 26 2 [] wn00003 ▸
       at 21 2 (X0 ∷ CS12 ∷ []) (sym (low₁-comm (X) (CS))) ▸ done

  b10 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ CS12 ∷ CK03⁻ ∷ X0 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ X0 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b10 = at 23 1 (Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 22 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 23 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 24 2 (CK01⁻ ∷ CS23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CS))) ▸
       at 25 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 28 2 [] wn00003 ▸ done

  b11 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ X0 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ Sw23 ∷ Sw12 ∷ CK01⁻ ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ X0 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b11 = at 22 5 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 (X0 ∷ CS12 ∷ []) (sym (low₁-comm (X) (CS))) ▸
       at 20 2 (X0 ∷ CS12 ∷ []) (sym (low₁-comm (X) (CS))) ▸
       at 22 1 (Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 21 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 22 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 22 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 23 2 (CK01⁻ ∷ CS23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CS))) ▸ done

  b12 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ Sw23 ∷ Sw12 ∷ CK01⁻ ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ X0 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ X0 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b12 = at 24 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 27 2 [] wn00003 ▸
       at 21 5 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 22 2 (X0 ∷ CS12 ∷ []) (sym (low₁-comm (X) (CS))) ▸
       at 19 2 (X0 ∷ CS12 ∷ []) (sym (low₁-comm (X) (CS))) ▸
       at 21 1 (Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 20 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b13 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ X0 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b13 = at 21 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 22 2 (CK01⁻ ∷ CS23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CS))) ▸
       at 23 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 26 2 [] wn00003 ▸
       at 20 5 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 (X0 ∷ CS12 ∷ []) (sym (low₁-comm (X) (CS))) ▸ done

  b14 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ X0 ∷ Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ X0 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b14 = at 18 2 (X0 ∷ CS12 ∷ []) (sym (low₁-comm (X) (CS))) ▸
       at 20 1 (Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 19 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 20 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 21 2 (CK01⁻ ∷ CS23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CS))) ▸
       at 22 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b15 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ X0 ∷ Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ X0 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ X0 ∷ Sw23 ∷ Sw12 ∷ CS23 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ X0 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b15 = at 25 2 [] wn00003 ▸
       at 19 5 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 (X0 ∷ CS12 ∷ []) (sym (low₁-comm (X) (CS))) ▸
       at 17 2 (X0 ∷ CS12 ∷ []) (sym (low₁-comm (X) (CS))) ▸
       at 19 1 (Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 18 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 19 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸ done

  b16 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ X0 ∷ Sw23 ∷ Sw12 ∷ CS23 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ X0 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ X0 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ X0 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b16 = at 20 2 (CK01⁻ ∷ CS23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CS))) ▸
       at 21 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 24 2 [] wn00003 ▸
       at 18 5 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 (X0 ∷ CS12 ∷ []) (sym (low₁-comm (X) (CS))) ▸
       at 16 2 (X0 ∷ CS12 ∷ []) (sym (low₁-comm (X) (CS))) ▸
       at 18 1 (Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b17 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ X0 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ X0 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ X0 ∷ CK03⁻ ∷ CS12 ∷ X0 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b17 = at 17 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 18 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 19 2 (CK01⁻ ∷ CS23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CS))) ▸
       at 20 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 [] wn00003 ▸
       at 17 5 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b18 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ X0 ∷ CK03⁻ ∷ CS12 ∷ X0 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ X0 ∷ Sw23 ∷ CK02⁻ ∷ Sw23 ∷ Sw23 ∷ S1 ∷ Sw23 ∷ X0 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b18 = at 18 2 (X0 ∷ CS12 ∷ []) (sym (low₁-comm (X) (CS))) ▸
       at 15 2 (X0 ∷ S1 ∷ []) (sym (low₁-comm (X) (S))) ▸
       at 18 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 17 1 (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 [] wn00003 ▸
       at 16 2 (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap)) ▸
       at 17 2 (CK02⁻ ∷ S1 ∷ []) wn01272 ▸
       at 18 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b19 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ X0 ∷ Sw23 ∷ CK02⁻ ∷ Sw23 ∷ Sw23 ∷ S1 ∷ Sw23 ∷ X0 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ Sw23 ∷ CK13 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ X0 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b19 = at 16 3 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (S1 ∷ Sw23 ∷ []) (sym (low-comm ((S ↑)) (Swap))) ▸
       at 18 2 [] wn00003 ▸
       at 17 2 (X0 ∷ S1 ∷ []) (sym (low₁-comm (X) (S))) ▸
       at 14 2 (X0 ∷ CK12 ∷ []) (sym (low₁-comm (X) (CK₀₁))) ▸
       at 16 1 (Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 16 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸ done

  b20 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ Sw23 ∷ CK13 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ X0 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ X0 ∷ CS12 ∷ CK03⁻ ∷ X0 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b20 = at 16 2 (Sw12 ∷ CK23 ∷ []) wn01052 ▸
       at 17 2 (CK01⁻ ∷ CK23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CK₀₁))) ▸
       at 18 2 (Sw12 ∷ CK13 ∷ []) wn01053 ▸
       at 19 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 [] wn00003 ▸
       at 15 5 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (X0 ∷ CK12 ∷ []) (sym (low₁-comm (X) (CK₀₁))) ▸
       at 13 2 (X0 ∷ CS12 ∷ []) (sym (low₁-comm (X) (CS))) ▸ done

  b21 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ X0 ∷ CS12 ∷ CK03⁻ ∷ X0 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ X0 ∷ Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ X0 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b21 = at 15 1 (Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 15 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 16 2 (CK01⁻ ∷ CS23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CS))) ▸
       at 17 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 [] wn00003 ▸ done

  b22 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ X0 ∷ Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ CS12 ∷ X0 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ X0 ∷ Sw23 ∷ Sw12 ∷ CK01⁻ ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ X0 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b22 = at 14 5 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (X0 ∷ CS12 ∷ []) (sym (low₁-comm (X) (CS))) ▸
       at 12 2 (X0 ∷ CS12 ∷ []) (sym (low₁-comm (X) (CS))) ▸
       at 14 1 (Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 14 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 15 2 (CK01⁻ ∷ CS23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CS))) ▸ done

  b23 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ X0 ∷ Sw23 ∷ Sw12 ∷ CK01⁻ ∷ CS23 ∷ Sw12 ∷ Sw23 ∷ X0 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ X0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ X0 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b23 = at 16 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 [] wn00003 ▸
       at 13 5 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (X0 ∷ CS12 ∷ []) (sym (low₁-comm (X) (CS))) ▸
       at 11 2 (X0 ∷ CS12 ∷ []) (sym (low₁-comm (X) (CS))) ▸
       at 13 1 (Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b24 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ X0 ∷ Sw23 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ X0 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b24 = at 13 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw12 ∷ CS23 ∷ []) wn00065 ▸
       at 14 2 (CK01⁻ ∷ CS23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CS))) ▸
       at 15 2 (Sw12 ∷ CS13 ∷ []) wn00048 ▸
       at 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 [] wn00003 ▸
       at 12 5 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (X0 ∷ CS12 ∷ []) (sym (low₁-comm (X) (CS))) ▸ done

  b25 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ X0 ∷ CK03⁻ ∷ Sw23 ∷ S1 ∷ Sw23 ∷ X0 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b25 = at 10 2 (X0 ∷ S1 ∷ []) (sym (low₁-comm (X) (S))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 12 1 (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 11 2 (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap)) ▸
       at 12 2 (CK02⁻ ∷ S1 ∷ []) wn01272 ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 3 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b26 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ X0 ∷ CK03⁻ ∷ Sw23 ∷ S1 ∷ Sw23 ∷ X0 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ X0 ∷ Sw23 ∷ Sw12 ∷ CK23 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ X0 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b26 = at 12 2 (S1 ∷ Sw23 ∷ []) (sym (low-comm ((S ↑)) (Swap))) ▸
       at 13 2 [] wn00003 ▸
       at 12 2 (X0 ∷ S1 ∷ []) (sym (low₁-comm (X) (S))) ▸
       at 9 2 (X0 ∷ CK12 ∷ []) (sym (low₁-comm (X) (CK₀₁))) ▸
       at 11 1 (Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw12 ∷ CK23 ∷ []) wn01052 ▸ done

  b27 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ X0 ∷ Sw23 ∷ Sw12 ∷ CK23 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ X0 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ X0 ∷ S1 ∷ CK03⁻ ∷ Sw23 ∷ Sw23 ∷ X0 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b27 = at 12 2 (CK01⁻ ∷ CK23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CK₀₁))) ▸
       at 13 2 (Sw12 ∷ CK13 ∷ []) wn01053 ▸
       at 14 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 [] wn00003 ▸
       at 10 5 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (X0 ∷ CK12 ∷ []) (sym (low₁-comm (X) (CK₀₁))) ▸
       at 8 2 (X0 ∷ S1 ∷ []) (sym (low₁-comm (X) (S))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b28 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ X0 ∷ S1 ∷ CK03⁻ ∷ Sw23 ∷ Sw23 ∷ X0 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ X0 ∷ CK03⁻ ∷ S1 ∷ X0 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b28 = at 10 1 (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 9 2 (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap)) ▸
       at 10 2 (CK02⁻ ∷ S1 ∷ []) wn01272 ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (S1 ∷ Sw23 ∷ []) (sym (low-comm ((S ↑)) (Swap))) ▸
       at 11 2 [] wn00003 ▸ done

  b29 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ X0 ∷ CK03⁻ ∷ S1 ∷ X0 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ X0 ∷ Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ CK13 ∷ Sw23 ∷ X0 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b29 = at 10 2 (X0 ∷ S1 ∷ []) (sym (low₁-comm (X) (S))) ▸
       at 7 2 (X0 ∷ CK12 ∷ []) (sym (low₁-comm (X) (CK₀₁))) ▸
       at 9 1 (Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CK13 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw12 ∷ CK23 ∷ []) wn01052 ▸
       at 10 2 (CK01⁻ ∷ CK23 ∷ []) (sym (low-comm ((S • CK₀₁)) (CK₀₁))) ▸
       at 11 2 (Sw12 ∷ CK13 ∷ []) wn01053 ▸ done

  b30 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ X0 ∷ Sw23 ∷ Sw12 ∷ CK01⁻ ∷ Sw12 ∷ CK13 ∷ Sw23 ∷ X0 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ X0 ∷ Sw23 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b30 = at 12 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 8 5 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (X0 ∷ CK12 ∷ []) (sym (low₁-comm (X) (CK₀₁))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 8 1 (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸ done

  b31 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ X0 ∷ Sw23 ∷ CK02⁻ ∷ X0 ∷ Sw23 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b31 = at 7 2 (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑))) ▸
       at 6 2 (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap)) ▸
       at 7 4 (X0 ∷ CK02⁻ ∷ X0 ∷ CX01 ∷ []) wn01271 ▸
       at 6 2 (X0 ∷ Sw23 ∷ []) (sym (low₁-comm (X) ((Swap ↑)))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (X0 ∷ Sw23 ∷ []) (sym (low₁-comm (X) ((Swap ↑)))) ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸ done

  b32 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ CX01 ∷ Sw23 ∷ Sw23 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X0 ∷ Sw01 ∷ CK13⁻ ∷ X1 ∷ Sw01 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b32 = at 10 2 [] wn00003 ▸
       at 9 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 8 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 7 1 (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 8 2 (Sw01 ∷ CK12⁻ ∷ []) wn01228 ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 8 3 (CK13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b33 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X0 ∷ Sw01 ∷ CK13⁻ ∷ X1 ∷ Sw01 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ X0 ∷ Sw23 ∷ CK02⁻ ∷ Sw23 ∷ Sw01 ∷ X1 ∷ CK12 ∷ Sw01 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b33 = at 6 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 5 2 (Sw01 ∷ CK12 ∷ []) wn00772 ▸
       at 6 4 (X1 ∷ CK13⁻ ∷ X1 ∷ CK12 ∷ []) wn01273 ▸
       at 5 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 7 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CK02⁻ ∷ Sw01 ∷ []) wn00330 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b34 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ X0 ∷ Sw23 ∷ CK02⁻ ∷ Sw23 ∷ Sw01 ∷ X1 ∷ CK12 ∷ Sw01 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ X0 ∷ Sw23 ∷ CK02⁻ ∷ Sw01 ∷ Sw23 ∷ X1 ∷ Sw01 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b34 = at 6 3 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 8 2 (CK02 ∷ Sw01 ∷ []) wn00329 ▸
       at 9 2 [] wn00031 ▸
       at 8 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 7 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 6 1 (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b35 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ X0 ∷ Sw23 ∷ CK02⁻ ∷ Sw01 ∷ Sw23 ∷ X1 ∷ Sw01 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ X0 ∷ Sw01 ∷ Sw23 ∷ CK12⁻ ∷ Sw23 ∷ X1 ∷ CK12 ∷ Sw01 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b35 = at 7 2 (Sw01 ∷ CK12⁻ ∷ []) wn01228 ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 7 3 (CK13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 4 2 (Sw01 ∷ CK12 ∷ []) wn00772 ▸
       at 5 4 (X1 ∷ CK13⁻ ∷ X1 ∷ CK12 ∷ []) wn01273 ▸
       at 4 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 6 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b36 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ X0 ∷ Sw01 ∷ Sw23 ∷ CK12⁻ ∷ Sw23 ∷ X1 ∷ CK12 ∷ Sw01 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ Sw01 ∷ Sw01 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b36 = at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 2 (CK02⁻ ∷ Sw01 ∷ []) wn00330 ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 3 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 7 2 (CK02 ∷ Sw01 ∷ []) wn00329 ▸
       at 8 2 [] wn00031 ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸ done

  b37 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ Sw01 ∷ Sw01 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ Sw01 ∷ CS12 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw01 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b37 = at 6 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 5 1 (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 2 (Sw01 ∷ CK12⁻ ∷ []) wn01228 ▸
       at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 6 3 (CK13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 3 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸ done

  b38 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ Sw01 ∷ CS12 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw01 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ Sw01 ∷ CS12 ∷ Sw01 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b38 = at 4 4 (X1 ∷ CK13⁻ ∷ X1 ∷ CS12 ∷ []) wn01274 ▸
       at 3 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 5 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 5 2 (CK02⁻ ∷ Sw01 ∷ []) wn00330 ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 3 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸ done

  b39 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ Sw01 ∷ CS12 ∷ Sw01 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ CK02 ∷ X0 ∷ Sw01 ∷ Sw23 ∷ CK12⁻ ∷ Sw23 ∷ X1 ∷ Sw01 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b39 = at 6 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 7 2 [] wn00031 ▸
       at 6 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 5 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 4 1 (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 2 (Sw01 ∷ CK12⁻ ∷ []) wn01228 ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸ done

  b40 : Chain (CS02 ∷ CS02 ∷ CK02 ∷ X0 ∷ Sw01 ∷ Sw23 ∷ CK12⁻ ∷ Sw23 ∷ X1 ∷ Sw01 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ X0 ∷ Sw23 ∷ CK02⁻ ∷ Sw01 ∷ Sw23 ∷ X1 ∷ CK12 ∷ Sw01 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b40 = at 5 3 (CK13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 2 2 (Sw01 ∷ CK12 ∷ []) wn00772 ▸
       at 3 4 (X1 ∷ CK13⁻ ∷ X1 ∷ CK12 ∷ []) wn01273 ▸
       at 2 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 4 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CK02⁻ ∷ Sw01 ∷ []) wn00330 ▸ done

  b41 : Chain (CS02 ∷ CS02 ∷ X0 ∷ Sw23 ∷ CK02⁻ ∷ Sw01 ∷ Sw23 ∷ X1 ∷ CK12 ∷ Sw01 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ CS02 ∷ X0 ∷ Sw23 ∷ CK02⁻ ∷ Sw23 ∷ Sw01 ∷ X1 ∷ Sw01 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b41 = at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 5 2 (CK02 ∷ Sw01 ∷ []) wn00329 ▸
       at 6 2 [] wn00031 ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 3 1 (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b42 : Chain (CS02 ∷ CS02 ∷ X0 ∷ Sw23 ∷ CK02⁻ ∷ Sw23 ∷ Sw01 ∷ X1 ∷ Sw01 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ X0 ∷ Sw01 ∷ CK13⁻ ∷ X1 ∷ CS12 ∷ Sw01 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b42 = at 5 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 2 (Sw01 ∷ CK12⁻ ∷ []) wn01228 ▸
       at 3 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 4 3 (CK13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 1 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 2 4 (X1 ∷ CK13⁻ ∷ X1 ∷ CS12 ∷ []) wn01274 ▸
       at 1 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸ done

  b43 : Chain (CS02 ∷ X0 ∷ Sw01 ∷ CK13⁻ ∷ X1 ∷ CS12 ∷ Sw01 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b43 = at 3 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 2 (CK02⁻ ∷ Sw01 ∷ []) wn00330 ▸
       at 4 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 3 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 4 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 5 2 [] wn00031 ▸ done

  b44 : Chain (CS02 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS02 ∷ Sw01 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw01 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b44 = at 4 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 3 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸
       at 2 1 (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 2 (Sw01 ∷ CK12⁻ ∷ []) wn01228 ▸
       at 2 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 3 3 (CK13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw01 ∷ X1 ∷ []) wn01106 ▸ done

  b45 : Chain (CS02 ∷ Sw01 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ Sw01 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (X0 ∷ CK03⁻ ∷ Sw01 ∷ X1 ∷ CS12 ∷ Sw01 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b45 = at 0 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 1 4 (X1 ∷ CK13⁻ ∷ X1 ∷ CS12 ∷ []) wn01274 ▸
       at 0 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 2 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 1 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 2 2 (CK02⁻ ∷ Sw01 ∷ []) wn00330 ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 1 3 (CK03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b46 : Chain (X0 ∷ CK03⁻ ∷ Sw01 ∷ X1 ∷ CS12 ∷ Sw01 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (X0 ∷ CK03⁻ ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ [])
  b46 = at 2 2 (X0 ∷ Sw01 ∷ []) wn00317 ▸
       at 3 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 4 2 [] wn00031 ▸ done
