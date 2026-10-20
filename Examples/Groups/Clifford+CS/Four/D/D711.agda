{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Four.D.D711 where

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
open import Examples.Groups.Clifford+CS.Four.Wins.W01 using (wn00001 ; wn00003 ; wn00005 ; wn00007 ; wn00012 ; wn00014 ; wn00018 ; wn00019 ; wn00020 ; wn00021 ; wn00022 ; wn00023 ; wn00024 ; wn00025 ; wn00027 ; wn00029 ; wn00031 ; wn00045 ; wn00046 ; wn00056 ; wn00076 ; wn00123 ; wn00124 ; wn00125 ; wn00173 ; wn00175)
open import Examples.Groups.Clifford+CS.Four.Wins.W02 using (wn00227 ; wn00231 ; wn00257 ; wn00258 ; wn00310)
open import Examples.Groups.Clifford+CS.Four.Wins.W20 using (wn01049 ; wn01051)
open import Examples.Groups.Clifford+CS.Four.Wins.W27 using (wn01342)
open import Examples.Groups.Clifford+CS.Four.Wins.W41 using (wn01962 ; wn01963 ; wn01964)
open import Examples.Groups.Clifford+CS.Four.Wins.W42 using (wn02016 ; wn02017 ; wn02018 ; wn02019 ; wn02020 ; wn02021)
open import Examples.Groups.Clifford+CS.Four.Wins.W44 using (wn02086 ; wn02087 ; wn02088 ; wn02089 ; wn02090 ; wn02091 ; wn02092)
open import Examples.Groups.Clifford+CS.Four.D.D010 using (lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D510 using (lem-ROT-form ; lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D536 using (lem-pass-S0-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D537 using (lem-pass-Sd0-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D538 using (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS02 ; lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd02 ; lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S2 ; lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Sd2)
open import Examples.Groups.Clifford+CS.Four.D.D596 using (lem-ROT≡cF)
open import Examples.Groups.Clifford+CS.Four.D.D701 using (lem-R0 ; lem-S2-at0213-ᵖ-1 ; lem-pass-CS03-vs-TOFF012-CS03-TOFF012-CSd03 ; lem-pass-CSd03-vs-TOFF012-CS03-TOFF012-CSd03 ; lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-TOFF012-X1-X2-S0-CSd03-X1-X2-TOFF012-X1-X2-Sd0-CS03 ; lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03 ; lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3 ; lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF013-X3)

-- C3d-A: 25 steps
lem-C3d-A : ⟪ (CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-C3d-A = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) (CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ [])
  b0 = at 1 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 1 1 (CS02 ∷ CS02 ∷ CS02 ∷ []) wn02086 ▸
       at 2 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 0 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b1 : Chain (CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ [])
  b1 = at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸
       at 2 4 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03 ∷ []) (sym lem-R0) ▸
       at 1 4 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03 ∷ []) (sym lem-R0) ▸
       at 0 4 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03 ∷ []) (sym lem-R0) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b2 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw23 ∷ Sw23 ∷ [])
  b2 = at 7 2 [] wn00003 ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00003 ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 4 3 (CS02⁻ ∷ []) wn00310 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b3 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw23 ∷ Sw23 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b3 = at 4 2 [] wn00003 ▸ done

-- C3-Ai: 17 steps
lem-C3-Ai : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ []) ⟫ʷ
lem-C3-Ai = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS03⁻ ∷ CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  b0 = at 0 0 (Toff012 ∷ Toff012 ∷ []) wn00045 ▸
       at 1 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 0 (CS02⁻ ∷ CS02 ∷ []) wn00231 ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 2 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 [] wn00003 ▸ done

  b1 : Chain (Toff012 ∷ CS03⁻ ∷ CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ Toff012 ∷ [])
  b1 = at 2 4 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03 ∷ []) (sym lem-R0) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 6 2 [] wn01342 ▸
       at 5 2 [] wn00003 ▸ done

  b2 : Chain (Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ Toff012 ∷ []) (Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ [])
  b2 = at 4 2 [] wn00227 ▸ done

-- pass [X2 X3 TOFF012 CS03 TOFF012 CSd03 X2 X3] [TOFF012 CS03 TOFF012 CSd03]: 139 steps
lem-pass-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3-vs-TOFF012-CS03-TOFF012-CSd03 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (run b17)))))))))))))))))
  where
  b0 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ S0 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b0 = at 7 2 (Toff012 ∷ X3 ∷ []) (sym (low₃-comm (Toff) (X))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸
       at 8 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 9 2 (S0 ∷ CS02⁻ ∷ X2 ∷ []) wn01962 ▸
       at 8 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b1 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ S0 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ X2 ∷ CS02⁻ ∷ Sw23 ∷ [])
  b1 = at 9 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 11 2 [] wn00003 ▸
       at 10 2 (Toff012 ∷ X3 ∷ []) (sym (low₃-comm (Toff) (X))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 12 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 11 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸ done

  b2 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ X2 ∷ CS02⁻ ∷ Sw23 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ X2 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ X3 ∷ [])
  b2 = at 12 2 (S0⁻ ∷ CS02 ∷ X2 ∷ []) wn01963 ▸
       at 11 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 12 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 14 2 [] wn00003 ▸
       at 6 2 (X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ []) wn02016 ▸
       at 9 2 (S0 ∷ X2 ∷ []) (sym (low₁-comm (S) ((X ↑)))) ▸ done

  b3 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ X2 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ Sw01 ∷ CS13⁻ ∷ X2 ∷ Sw01 ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ X3 ∷ [])
  b3 = at 12 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 11 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 12 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 11 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 12 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 11 2 (CS13⁻ ∷ X2 ∷ []) wn00258 ▸ done

  b4 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ Sw01 ∷ CS13⁻ ∷ X2 ∷ Sw01 ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X3 ∷ [])
  b4 = at 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 10 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 12 2 [] wn00031 ▸
       at 11 2 (X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ []) wn02016 ▸ done

  b5 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ Sw01 ∷ X2 ∷ CS13 ∷ Sw01 ∷ X3 ∷ [])
  b5 = at 14 2 (S0⁻ ∷ X2 ∷ []) (sym (low₁-comm ((S • S • S)) ((X ↑)))) ▸
       at 17 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 17 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 16 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 17 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸ done

  b6 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ Sw01 ∷ X2 ∷ CS13 ∷ Sw01 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ X3 ∷ [])
  b6 = at 16 2 (CS13 ∷ X2 ∷ []) wn00257 ▸
       at 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 16 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 17 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 15 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 17 2 [] wn00031 ▸ done

  b7 : Chain (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b7 = at 2 14 (X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03) ▸
       at 1 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 2 2 (Toff012 ∷ X3 ∷ []) (sym (low₃-comm (Toff) (X))) ▸
       at 3 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 4 2 (S0 ∷ X3 ∷ []) (sym (low₁-comm (S) ((X ↑ ↑)))) ▸
       at 7 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸ done

  b8 : Chain (X2 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ X3 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b8 = at 5 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 6 2 (S0⁻ ∷ CS02 ∷ X2 ∷ []) wn01963 ▸
       at 5 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 8 2 [] wn00003 ▸
       at 7 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸ done

  b9 : Chain (X2 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ X3 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b9 = at 8 2 (Toff012 ∷ X3 ∷ []) (sym (low₃-comm (Toff) (X))) ▸
       at 9 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 10 2 (S0⁻ ∷ X3 ∷ []) (sym (low₁-comm ((S • S • S)) ((X ↑ ↑)))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸
       at 11 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 12 2 (S0 ∷ CS02⁻ ∷ X2 ∷ []) wn01962 ▸ done

  b10 : Chain (X2 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (Toff012 ∷ S0 ∷ S0⁻ ∷ X2 ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b10 = at 11 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 14 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 12 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 14 2 [] wn00003 ▸
       at 0 4 (Toff012 ∷ X2 ∷ []) wn02017 ▸
       at 1 2 (S0 ∷ X2 ∷ []) (sym (low₁-comm (S) ((X ↑)))) ▸
       at 2 2 (S0⁻ ∷ X2 ∷ []) (sym (low₁-comm ((S • S • S)) ((X ↑)))) ▸ done

  b11 : Chain (Toff012 ∷ S0 ∷ S0⁻ ∷ X2 ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (Toff012 ∷ S0 ∷ S0⁻ ∷ Sw01 ∷ CS13 ∷ X2 ∷ Sw01 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b11 = at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 4 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 5 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 4 2 (CS13 ∷ X2 ∷ []) wn00257 ▸ done

  b12 : Chain (Toff012 ∷ S0 ∷ S0⁻ ∷ Sw01 ∷ CS13 ∷ X2 ∷ Sw01 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (Toff012 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b12 = at 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 3 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 4 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 5 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 5 2 [] wn00031 ▸
       at 4 4 (Toff012 ∷ X2 ∷ []) wn02017 ▸ done

  b13 : Chain (Toff012 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (Toff012 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ S0⁻ ∷ S0 ∷ X2 ∷ Sw01 ∷ CS13⁻ ∷ Sw01 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b13 = at 5 2 (S0⁻ ∷ X2 ∷ []) (sym (low₁-comm ((S • S • S)) ((X ↑)))) ▸
       at 6 2 (S0 ∷ X2 ∷ []) (sym (low₁-comm (S) ((X ↑)))) ▸
       at 9 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 8 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b14 : Chain (Toff012 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ S0⁻ ∷ S0 ∷ X2 ∷ Sw01 ∷ CS13⁻ ∷ Sw01 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (Toff012 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Sw01 ∷ Sw01 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b14 = at 7 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 8 2 (CS13⁻ ∷ X2 ∷ []) wn00258 ▸
       at 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 8 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 9 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸ done

  b15 : Chain (Toff012 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Sw01 ∷ Sw01 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (Toff012 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b15 = at 9 2 [] wn00031 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 2 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 1 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 2 3 (CS02 ∷ []) wn01964 ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b16 : Chain (Toff012 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ Toff012 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b16 = at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 4 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸
       at 3 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 4 3 (CS02⁻ ∷ []) wn02018 ▸ done

  b17 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  b17 = at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸ done

-- pass [X1 X2 X3 TOFF012 CS03 TOFF012 CSd03 X1 X2 X3] [TOFF012 CS03 TOFF012 CSd03]: 189 steps
lem-pass-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3-vs-TOFF012-CS03-TOFF012-CSd03 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (run b23)))))))))))))))))))))))
  where
  b0 : Chain (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ S0 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b0 = at 9 2 (Toff012 ∷ X3 ∷ []) (sym (low₃-comm (Toff) (X))) ▸
       at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 [] wn00003 ▸
       at 10 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 11 2 (S0 ∷ CS02⁻ ∷ X2 ∷ []) wn01962 ▸
       at 10 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b1 : Chain (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ S0 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03⁻ ∷ []) (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ X2 ∷ CS02⁻ ∷ Sw23 ∷ [])
  b1 = at 11 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 13 2 [] wn00003 ▸
       at 12 2 (Toff012 ∷ X3 ∷ []) (sym (low₃-comm (Toff) (X))) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 14 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 [] wn00003 ▸
       at 13 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸ done

  b2 : Chain (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ S0 ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ X2 ∷ CS02⁻ ∷ Sw23 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ X2 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ X3 ∷ [])
  b2 = at 14 2 (S0⁻ ∷ CS02 ∷ X2 ∷ []) wn01963 ▸
       at 13 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 16 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 14 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 16 2 [] wn00003 ▸
       at 8 2 (X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ []) wn02016 ▸
       at 11 2 (S0 ∷ X2 ∷ []) (sym (low₁-comm (S) ((X ↑)))) ▸ done

  b3 : Chain (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ X2 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ Sw01 ∷ CS13⁻ ∷ X2 ∷ Sw01 ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ X3 ∷ [])
  b3 = at 14 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 13 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 14 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸
       at 13 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 14 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 13 2 (CS13⁻ ∷ X2 ∷ []) wn00258 ▸ done

  b4 : Chain (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ Sw01 ∷ CS13⁻ ∷ X2 ∷ Sw01 ∷ Toff012 ∷ S0⁻ ∷ CS03 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X3 ∷ [])
  b4 = at 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 14 2 [] wn00031 ▸
       at 13 2 (X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ []) wn02016 ▸ done

  b5 : Chain (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ Sw01 ∷ X2 ∷ CS13 ∷ Sw01 ∷ X3 ∷ [])
  b5 = at 16 2 (S0⁻ ∷ X2 ∷ []) (sym (low₁-comm ((S • S • S)) ((X ↑)))) ▸
       at 19 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 20 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 19 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 18 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 19 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸ done

  b6 : Chain (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ Sw01 ∷ X2 ∷ CS13 ∷ Sw01 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ X3 ∷ [])
  b6 = at 18 2 (CS13 ∷ X2 ∷ []) wn00257 ▸
       at 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 17 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 18 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 19 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 17 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 19 2 [] wn00031 ▸ done

  b7 : Chain (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X1 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ X3 ∷ [])
  b7 = at 7 4 (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ X1 ∷ []) wn02019 ▸
       at 12 2 (S0 ∷ X1 ∷ []) (sym (low₁-comm (S) (X))) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 14 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 16 2 [] wn00003 ▸
       at 13 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 14 2 (CS02⁻ ∷ X1 ∷ []) wn01051 ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b8 : Chain (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X1 ∷ Sw23 ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0⁻ ∷ X1 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ X2 ∷ X3 ∷ [])
  b8 = at 13 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 15 2 [] wn00003 ▸
       at 14 4 (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ X1 ∷ []) wn02019 ▸
       at 19 2 (S0⁻ ∷ X1 ∷ []) (sym (low₁-comm ((S • S • S)) (X))) ▸
       at 22 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 23 2 [] wn00003 ▸ done

  b9 : Chain (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0⁻ ∷ X1 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X1 ∷ X3 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b9 = at 20 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 21 2 (CS02 ∷ X1 ∷ []) wn01049 ▸
       at 22 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 20 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 21 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 22 2 [] wn00003 ▸
       at 3 18 (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-TOFF012-X1-X2-S0-CSd03-X1-X2-TOFF012-X1-X2-Sd0-CS03) ▸
       at 2 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸ done

  b10 : Chain (X1 ∷ X2 ∷ X1 ∷ X3 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b10 = at 3 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 4 2 (Toff012 ∷ X3 ∷ []) (sym (low₃-comm (Toff) (X))) ▸
       at 5 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 6 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 7 2 (S0 ∷ X3 ∷ []) (sym (low₁-comm (S) ((X ↑ ↑)))) ▸
       at 10 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 [] wn00003 ▸ done

  b11 : Chain (X1 ∷ X2 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0 ∷ X3 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ X1 ∷ X3 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b11 = at 8 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 9 2 (S0⁻ ∷ CS02 ∷ X2 ∷ []) wn01963 ▸
       at 8 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 11 2 [] wn00003 ▸
       at 10 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸ done

  b12 : Chain (X1 ∷ X2 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ X1 ∷ X3 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0⁻ ∷ X3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b12 = at 11 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 12 2 (Toff012 ∷ X3 ∷ []) (sym (low₃-comm (Toff) (X))) ▸
       at 13 2 (X1 ∷ X3 ∷ []) (sym (low-comm ((X ↑)) ((X ↑)))) ▸
       at 14 2 (X2 ∷ X3 ∷ []) (sym (low₃-comm ((X ↑ ↑)) (X))) ▸
       at 15 2 (S0⁻ ∷ X3 ∷ []) (sym (low₁-comm ((S • S • S)) ((X ↑ ↑)))) ▸
       at 18 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 19 2 [] wn00003 ▸ done

  b13 : Chain (X1 ∷ X2 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0⁻ ∷ X3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X1 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b13 = at 16 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 17 2 (S0 ∷ CS02⁻ ∷ X2 ∷ []) wn01962 ▸
       at 16 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 19 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 17 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 18 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 19 2 [] wn00003 ▸
       at 1 6 (X1 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) wn02020 ▸ done

  b14 : Chain (X1 ∷ X1 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X1 ∷ Toff012 ∷ X1 ∷ S0 ∷ S0⁻ ∷ X2 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b14 = at 4 2 (S0 ∷ X2 ∷ []) (sym (low₁-comm (S) ((X ↑)))) ▸
       at 5 2 (S0⁻ ∷ X2 ∷ []) (sym (low₁-comm ((S • S • S)) ((X ↑)))) ▸
       at 8 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 8 2 (Sw01 ∷ CS12 ∷ []) wn00007 ▸
       at 7 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 8 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸ done

  b15 : Chain (X1 ∷ X1 ∷ Toff012 ∷ X1 ∷ S0 ∷ S0⁻ ∷ X2 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X1 ∷ Toff012 ∷ X1 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Sw01 ∷ Sw01 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b15 = at 6 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 7 2 (CS13 ∷ X2 ∷ []) wn00257 ▸
       at 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 7 2 (CS02 ∷ Sw01 ∷ []) wn00027 ▸
       at 8 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸ done

  b16 : Chain (X1 ∷ X1 ∷ Toff012 ∷ X1 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Sw01 ∷ Sw01 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X1 ∷ Toff012 ∷ X1 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ X1 ∷ Toff012 ∷ X1 ∷ S0⁻ ∷ S0 ∷ X2 ∷ Sw23 ∷ Sw01 ∷ CS12⁻ ∷ Sw23 ∷ Sw01 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b16 = at 8 2 [] wn00031 ▸
       at 7 6 (X1 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) wn02020 ▸
       at 10 2 (S0⁻ ∷ X2 ∷ []) (sym (low₁-comm ((S • S • S)) ((X ↑)))) ▸
       at 11 2 (S0 ∷ X2 ∷ []) (sym (low₁-comm (S) ((X ↑)))) ▸
       at 14 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 13 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 15 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 14 2 (Sw01 ∷ CS12⁻ ∷ []) wn00076 ▸ done

  b17 : Chain (X1 ∷ X1 ∷ Toff012 ∷ X1 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ X1 ∷ Toff012 ∷ X1 ∷ S0⁻ ∷ S0 ∷ X2 ∷ Sw23 ∷ Sw01 ∷ CS12⁻ ∷ Sw23 ∷ Sw01 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X1 ∷ Toff012 ∷ X1 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ X1 ∷ Toff012 ∷ X1 ∷ S0⁻ ∷ S0 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw01 ∷ X2 ∷ Sw01 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b17 = at 13 2 (Sw01 ∷ Sw23 ∷ []) (sym (low-comm (Swap) (Swap))) ▸
       at 14 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw01 ∷ X2 ∷ []) (sym (low-comm (Swap) (X))) ▸
       at 13 2 (CS13⁻ ∷ X2 ∷ []) wn00258 ▸
       at 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 2 (CS02⁻ ∷ Sw01 ∷ []) wn00029 ▸
       at 14 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸ done

  b18 : Chain (X1 ∷ X1 ∷ Toff012 ∷ X1 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ X1 ∷ Toff012 ∷ X1 ∷ S0⁻ ∷ S0 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw01 ∷ X2 ∷ Sw01 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (Toff012 ∷ S0 ∷ S0⁻ ∷ X1 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ X1 ∷ Toff012 ∷ X1 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b18 = at 12 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X)) ▸
       at 14 2 [] wn00031 ▸
       at 0 4 (Toff012 ∷ X1 ∷ []) wn02021 ▸
       at 1 2 (S0 ∷ X1 ∷ []) (sym (low₁-comm (S) (X))) ▸
       at 2 2 (S0⁻ ∷ X1 ∷ []) (sym (low₁-comm ((S • S • S)) (X))) ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b19 : Chain (Toff012 ∷ S0 ∷ S0⁻ ∷ X1 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ X1 ∷ Toff012 ∷ X1 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (Toff012 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X1 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b19 = at 6 2 [] wn00003 ▸
       at 3 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 4 2 (CS02 ∷ X1 ∷ []) wn01049 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 5 2 [] wn00003 ▸
       at 4 4 (Toff012 ∷ X1 ∷ []) wn02021 ▸ done

  b20 : Chain (Toff012 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ X1 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (Toff012 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ S0⁻ ∷ S0 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X1 ∷ Sw23 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b20 = at 5 2 (S0⁻ ∷ X1 ∷ []) (sym (low₁-comm ((S • S • S)) (X))) ▸
       at 6 2 (S0 ∷ X1 ∷ []) (sym (low₁-comm (S) (X))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 7 2 (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap)) ▸
       at 8 2 (CS02⁻ ∷ X1 ∷ []) wn01051 ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b21 : Chain (Toff012 ∷ S0 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ S0⁻ ∷ S0 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ X1 ∷ Sw23 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (Toff012 ∷ Sw23 ∷ S0 ∷ S0⁻ ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b21 = at 7 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (X1 ∷ Sw23 ∷ []) (sym (low-comm ((X ↑)) (Swap))) ▸
       at 9 2 [] wn00003 ▸
       at 4 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 2 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 1 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸ done

  b22 : Chain (Toff012 ∷ Sw23 ∷ S0 ∷ S0⁻ ∷ CS02 ∷ Sw23 ∷ Toff012 ∷ S0⁻ ∷ S0 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ S0⁻ ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ Sw23 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b22 = at 2 3 (CS02 ∷ []) wn01964 ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 [] wn00003 ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 4 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸ done

  b23 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ S0⁻ ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ Sw23 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  b23 = at 3 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸
       at 4 3 (CS02⁻ ∷ []) wn02018 ▸
       at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 3 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸ done

-- pass [TOFF102 CS13 TOFF102 CSd13] [X3 TOFF013 X3 CS02 X3 TOFF013 X3 CSd02]: 4 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 = run b0
  where
  b0 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b0 = at 0 7 (X3 ∷ Toff013 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF013-X3) ▸
       at 3 5 (CS02 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS02) ▸
       at 4 7 (X3 ∷ Toff013 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF013-X3) ▸
       at 7 5 (CS02⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd02) ▸ done

-- pass [TOFF102 CS13 TOFF102 CSd13] [X1 X3 TOFF013 X1 X3 CS02 X1 X3 TOFF013 X1 X3 CSd02]: 4 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3-CS02-X1-X3-TOFF013-X1-X3-CSd02 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ CS02 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ CS02 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ CS02⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3-CS02-X1-X3-TOFF013-X1-X3-CSd02 = run b0
  where
  b0 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ CS02 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ CS02⁻ ∷ []) (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ CS02 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ CS02⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b0 = at 0 9 (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3) ▸
       at 5 5 (CS02 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS02) ▸
       at 6 9 (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3) ▸
       at 11 5 (CS02⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd02) ▸ done

-- pass [TOFF102 CS13 TOFF102 CSd13] [X3 TOFF013 X3 S2 CSd02 X3 TOFF013 X3 Sd2 CS02]: 6 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF013-X3-S2-CSd02-X3-TOFF013-X3-Sd2-CS02 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF013-X3-S2-CSd02-X3-TOFF013-X3-Sd2-CS02 = run b0
  where
  b0 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b0 = at 0 7 (X3 ∷ Toff013 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF013-X3) ▸
       at 3 5 (S2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S2) ▸
       at 4 5 (CS02⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd02) ▸
       at 5 7 (X3 ∷ Toff013 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF013-X3) ▸
       at 8 5 (S2⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Sd2) ▸
       at 9 5 (CS02 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS02) ▸ done

-- pass [TOFF102 CS13 TOFF102 CSd13] [X1 X3 TOFF013 X1 X3 S2 CSd02 X1 X3 TOFF013 X1 X3 Sd2 CS02]: 6 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3-S2-CSd02-X1-X3-TOFF013-X1-X3-Sd2-CS02 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3-S2-CSd02-X1-X3-TOFF013-X1-X3-Sd2-CS02 = run b0
  where
  b0 : Chain (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ []) (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  b0 = at 0 9 (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3) ▸
       at 5 5 (S2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S2) ▸
       at 6 5 (CS02⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd02) ▸
       at 7 9 (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3) ▸
       at 12 5 (S2⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Sd2) ▸
       at 13 5 (CS02 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS02) ▸ done

-- pass [X3 K0 CS03 Kd0 X3] [TOFF012 CS03 TOFF012 CSd03]: 44 steps
lem-pass-X3-K0-CS03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X3 ∷ K0 ∷ CS03 ∷ K0⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ K0 ∷ CS03 ∷ K0⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-K0-CS03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (X3 ∷ K0 ∷ CS03 ∷ K0⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ S0 ∷ CS02⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b0 = at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 3 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 1 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 0 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 1 5 (X2 ∷ CK20 ∷ X2 ∷ S0 ∷ CS02⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) wn02087 ▸ done

  b1 : Chain (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ S0 ∷ CS02⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (X3 ∷ CK30 ∷ X3 ∷ S0 ∷ CS03⁻ ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b1 = at 0 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 3 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸ done

  b2 : Chain (X3 ∷ CK30 ∷ X3 ∷ S0 ∷ CS03⁻ ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ S0 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  b2 = at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 8 2 [] wn00003 ▸
       at 5 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 4 5 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 3 5 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ []) (lem-pass-S0-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 0 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03) ▸ done

  b3 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ S0 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ [])
  b3 = at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 10 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 9 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 7 2 (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑))) ▸ done

  b4 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ Sw23 ∷ S0 ∷ CS02⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ K0 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ X2 ∷ Sw23 ∷ [])
  b4 = at 6 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 4 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 5 8 (X2 ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X2 ∷ []) wn02088 ▸
       at 4 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 5 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b5 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ K0 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ X2 ∷ Sw23 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ K0 ∷ CS03 ∷ K0⁻ ∷ X3 ∷ [])
  b5 = at 6 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑)))) ▸
       at 8 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 9 2 [] wn00003 ▸ done

-- pass [X3 K0 CSd03 Kd0 X3] [TOFF012 CS03 TOFF012 CSd03]: 44 steps
lem-pass-X3-K0-CSd03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X3 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-K0-CSd03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (X3 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ S0⁻ ∷ CS02 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b0 = at 5 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 3 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00003 ▸
       at 1 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 0 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 1 5 (X2 ∷ CK20 ∷ X2 ∷ S0⁻ ∷ CS02 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) wn02089 ▸ done

  b1 : Chain (Sw23 ∷ X2 ∷ CK20 ∷ X2 ∷ S0⁻ ∷ CS02 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (X3 ∷ CK30 ∷ X3 ∷ S0⁻ ∷ CS03 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  b1 = at 0 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 3 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 1 3 (CK30 ∷ []) (by-assoc Eq.refl) ▸
       at 2 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 3 2 (S0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((S • S • S)) ((Swap ↑)))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 4 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸ done

  b2 : Chain (X3 ∷ CK30 ∷ X3 ∷ S0⁻ ∷ CS03 ∷ X3 ∷ Sw23 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ S0⁻ ∷ CS03 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  b2 = at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 6 3 (CK30⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 8 2 [] wn00003 ▸
       at 5 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 4 5 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03 ∷ []) (lem-pass-CS03-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 3 5 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ []) (lem-pass-Sd0-vs-TOFF012-CS03-TOFF012-CSd03) ▸
       at 0 7 (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03) ▸ done

  b3 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ S0⁻ ∷ CS03 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ Sw23 ∷ S0⁻ ∷ CS02 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ [])
  b3 = at 12 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 10 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 9 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 7 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸ done

  b4 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ Sw23 ∷ S0⁻ ∷ CS02 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ Sw23 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ K0 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ X2 ∷ Sw23 ∷ [])
  b4 = at 6 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 4 2 (Sw23 ∷ X2 ∷ []) wn00173 ▸
       at 5 8 (X2 ∷ K0 ∷ CS02⁻ ∷ K0⁻ ∷ X2 ∷ []) wn02090 ▸
       at 4 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 5 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b5 : Chain (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ K0 ∷ Sw23 ∷ CS02⁻ ∷ Sw23 ∷ Sw23 ∷ K0⁻ ∷ X2 ∷ Sw23 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ X3 ∷ [])
  b5 = at 6 3 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑)))) ▸
       at 8 2 (X3 ∷ Sw23 ∷ []) wn00175 ▸
       at 9 2 [] wn00003 ▸ done

-- ROT-gad: 214 steps
lem-ROT-gad : ⟪ (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-ROT-gad = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (run b26))))))))))))))))))))))))))
  where
  b0 : Chain (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (K0 ∷ K0⁻ ∷ S0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ [])
  b0 = at 0 15 (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ023 ∷ []) (lem-ROT≡cF) ▸
       at 0 4 (K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ []) (lem-ROT-form) ▸
       at 3 2 (K0⁻ ∷ Sw12 ∷ []) (sym (low₁-comm ((K • iI)) (Swap))) ▸
       at 2 2 (K0⁻ ∷ Sw23 ∷ []) (sym (low₁-comm ((K • iI)) ((Swap ↑)))) ▸
       at 1 2 (K0⁻ ∷ Sw12 ∷ []) (sym (low₁-comm ((K • iI)) (Swap))) ▸
       at 4 2 (S0 ∷ Sw12 ∷ []) (sym (low₁-comm (S) (Swap))) ▸
       at 3 2 (S0 ∷ Sw23 ∷ []) (sym (low₁-comm (S) ((Swap ↑)))) ▸
       at 2 2 (S0 ∷ Sw12 ∷ []) (sym (low₁-comm (S) (Swap))) ▸ done

  b1 : Chain (K0 ∷ K0⁻ ∷ S0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ []) (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Sw12 ∷ K0⁻ ∷ Sw23 ∷ S0⁻ ∷ K0 ∷ Sw12 ∷ K0⁻ ∷ [])
  b1 = at 5 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸
       at 4 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 3 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸
       at 13 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 12 2 (Sw12 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) (Swap)) ▸
       at 11 2 (Sw12 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) (Swap)) ▸
       at 14 2 (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑))) ▸
       at 13 2 (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑))) ▸ done

  b2 : Chain (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Sw12 ∷ K0⁻ ∷ Sw23 ∷ S0⁻ ∷ K0 ∷ Sw12 ∷ K0⁻ ∷ []) (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ [])
  b2 = at 12 2 (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑))) ▸
       at 15 2 (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap)) ▸
       at 14 2 (Sw12 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) (Swap)) ▸
       at 13 2 (Sw12 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) (Swap)) ▸
       at 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 8 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 9 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸ done

  b3 : Chain (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw12 ∷ Sw23 ∷ CS03 ∷ K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS02 ∷ K0 ∷ ι ∷ CS03⁻ ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ [])
  b3 = at 6 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 8 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸
       at 8 2 (CS12 ∷ Sw12 ∷ []) wn00018 ▸
       at 11 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 9 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CS12⁻ ∷ Sw12 ∷ []) wn00019 ▸
       at 13 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸ done

  b4 : Chain (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw12 ∷ Sw23 ∷ CS03 ∷ K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS02 ∷ K0 ∷ ι ∷ CS03⁻ ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw12 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ [])
  b4 = at 11 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 13 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00014 ▸
       at 13 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸
       at 14 2 (ι ∷ Sw12 ∷ []) (sym (low₁-comm (iI) (Swap))) ▸
       at 7 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00046 ▸
       at 7 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸ done

  b5 : Chain (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw12 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Toff012 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw12 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ CS12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ [])
  b5 = at 8 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 10 2 (CS01⁻ ∷ Sw23 ∷ []) (sym (low-comm ((CS • CS • CS)) (Swap))) ▸
       at 11 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 8 5 (CS03⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸
       at 10 2 (CS12 ∷ Sw12 ∷ []) wn00018 ▸
       at 13 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸ done

  b6 : Chain (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw12 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ CS12 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw12 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw12 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ [])
  b6 = at 11 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (CS12⁻ ∷ Sw12 ∷ []) wn00019 ▸
       at 15 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 13 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 15 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00014 ▸
       at 15 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸
       at 16 2 (ι ∷ Sw12 ∷ []) (sym (low₁-comm (iI) (Swap))) ▸ done

  b7 : Chain (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw12 ∷ Sw23 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw12 ∷ CS02 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ [])
  b7 = at 9 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00046 ▸
       at 9 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00014 ▸
       at 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 5 2 [] wn00003 ▸
       at 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b8 : Chain (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw12 ∷ CS02 ∷ K0 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw12 ∷ CS02 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ [])
  b8 = at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b9 : Chain (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw12 ∷ CS02 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ Sw23 ∷ ι ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw12 ∷ CS02 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ [])
  b9 = at 13 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 6 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00003 ▸
       at 9 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸ done

  b10 : Chain (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw12 ∷ CS02 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ Sw23 ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw12 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ [])
  b10 = at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 13 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 14 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 7 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 7 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 6 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸ done

  b11 : Chain (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw12 ∷ CS02 ∷ Toff013 ∷ Sw23 ∷ CS03⁻ ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw12 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ [])
  b11 = at 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 2 [] wn00003 ▸
       at 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b12 : Chain (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw12 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ K0 ∷ CS13 ∷ CX01 ∷ Sw23 ∷ CS12⁻ ∷ Sw23 ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw12 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ [])
  b12 = at 11 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 13 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 15 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 8 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸ done

  b13 : Chain (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw12 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw23 ∷ K0 ∷ Sw23 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw12 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ [])
  b13 = at 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 [] wn00003 ▸
       at 11 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 [] wn00003 ▸
       at 13 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 [] wn00003 ▸ done

  b14 : Chain (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ Sw12 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS01 ∷ Sw12 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ [])
  b14 = at 15 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 16 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 9 8 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) wn00056 ▸
       at 9 8 (Toff012 ∷ []) (by-assoc Eq.refl) ▸
       at 8 3 (Toff013 ∷ []) (by-assoc Eq.refl) ▸
       at 9 2 [] wn00003 ▸
       at 5 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 4 2 [] wn00014 ▸ done

  b15 : Chain (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS01 ∷ Sw12 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS01 ∷ Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ Toff013 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ [])
  b15 = at 6 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 9 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 7 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸ done

  b16 : Chain (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS01 ∷ Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ Sw23 ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ CS02⁻ ∷ Toff013 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS01 ∷ K0 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ CS02⁻ ∷ Toff013 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ [])
  b16 = at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 13 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 14 2 [] wn00003 ▸
       at 5 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸
       at 6 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸ done

  b17 : Chain (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS01 ∷ K0 ∷ CS23 ∷ Sw12 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ CS02⁻ ∷ Toff013 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ ι ∷ CS02⁻ ∷ Toff013 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ [])
  b17 = at 9 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 7 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 11 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 9 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 10 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 12 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸ done

  b18 : Chain (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS01 ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw23 ∷ Sw12 ∷ Sw23 ∷ K0 ∷ ι ∷ CS02⁻ ∷ Toff013 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS01 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ CS02⁻ ∷ Toff013 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ [])
  b18 = at 13 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 10 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸
       at 12 2 (ι ∷ Sw12 ∷ []) (sym (low₁-comm (iI) (Swap))) ▸
       at 5 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 6 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 7 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 8 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b19 : Chain (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS01 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ Sw01 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ CS02⁻ ∷ Toff013 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS01 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ Sw01 ∷ ι ∷ Sw12 ∷ CS02⁻ ∷ Toff013 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ [])
  b19 = at 9 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 10 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 11 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 12 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 11 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸ done

  b20 : Chain (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS01 ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ Sw01 ∷ ι ∷ Sw12 ∷ CS02⁻ ∷ Toff013 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ [])
  b20 = at 13 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 6 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸
       at 6 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 5 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 7 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) (by-assoc Eq.refl) ▸
       at 6 2 [] wn00014 ▸
       at 8 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (by-assoc Eq.refl) ▸ done

  b21 : Chain (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ [])
  b21 = at 8 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 11 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 9 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 10 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 13 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸
       at 11 3 (CS13⁻ ∷ []) (by-assoc Eq.refl) ▸
       at 12 2 (CX01 ∷ Sw23 ∷ []) (sym (low-comm (CX₀₁) (Swap))) ▸
       at 15 0 (Sw23 ∷ Sw23 ∷ []) wn00001 ▸ done

  b22 : Chain (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Sw12 ∷ K0 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ K0 ∷ ι ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ K0 ∷ CS23 ∷ CX02 ∷ Sw12 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ [])
  b22 = at 13 3 (CS03 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (K0 ∷ Sw23 ∷ []) (sym (low₁-comm (K) ((Swap ↑)))) ▸
       at 15 2 (ι ∷ Sw23 ∷ []) (sym (low₁-comm (iI) ((Swap ↑)))) ▸
       at 16 2 [] wn00003 ▸
       at 7 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸
       at 8 2 (CS23 ∷ Sw12 ∷ []) wn00020 ▸
       at 11 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 9 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸ done

  b23 : Chain (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ K0 ∷ CS23 ∷ CX02 ∷ Sw12 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ [])
  b23 = at 10 2 (CS23⁻ ∷ Sw12 ∷ []) wn00021 ▸
       at 13 0 (Sw12 ∷ Sw12 ∷ []) wn00012 ▸
       at 11 3 (CX02 ∷ []) (by-assoc Eq.refl) ▸
       at 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 12 3 (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) wn00022 ▸
       at 14 2 (CS01 ∷ Sw23 ∷ []) (sym (low-comm (CS) (Swap))) ▸
       at 15 3 (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) wn00023 ▸
       at 12 5 (CS03 ∷ []) (by-assoc Eq.refl) ▸ done

  b24 : Chain (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ K0 ∷ CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Sw12 ∷ K0 ∷ ι ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ [])
  b24 = at 13 2 (K0 ∷ Sw12 ∷ []) (sym (low₁-comm (K) (Swap))) ▸
       at 14 2 (ι ∷ Sw12 ∷ []) (sym (low₁-comm (iI) (Swap))) ▸
       at 7 0 (Sw01 ∷ Sw01 ∷ []) wn00005 ▸
       at 8 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 9 2 (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS)) ▸
       at 10 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸
       at 11 2 (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS))) ▸
       at 12 2 (CX12 ∷ Sw01 ∷ []) wn00024 ▸ done

  b25 : Chain (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ Sw01 ∷ CS03 ∷ K0 ∷ ι ∷ Sw12 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ [])
  b25 = at 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) (by-assoc Eq.refl) ▸
       at 13 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 14 2 (CS12 ∷ Sw01 ∷ []) wn00025 ▸
       at 15 2 (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap)) ▸
       at 13 3 (CS13 ∷ []) (by-assoc Eq.refl) ▸
       at 14 2 (K1 ∷ Sw01 ∷ []) wn00123 ▸
       at 15 2 (ι1 ∷ Sw01 ∷ []) wn00124 ▸
       at 8 8 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) wn00125 ▸ done

  b26 : Chain (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Sw01 ∷ K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ Sw01 ∷ Sw12 ∷ Sw12 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ [])
  b26 = at 8 8 (Toff123 ∷ []) (by-assoc Eq.refl) ▸
       at 7 3 (Toff023 ∷ []) (by-assoc Eq.refl) ▸
       at 8 2 [] wn00014 ▸
       at 4 4 (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (sym lem-S2-at0213-ᵖ-1) ▸
       at 0 4 (S0 ∷ K0 ∷ []) wn02091 ▸
       at 6 4 (K0⁻ ∷ S0⁻ ∷ []) wn02092 ▸ done
