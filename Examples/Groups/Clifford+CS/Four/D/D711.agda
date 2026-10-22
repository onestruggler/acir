{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD711 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D711 (W : Ws) (Sᴰ : SD711) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 38
  lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 0 Sᴰ
  lem-ROT-form : St 2018
  lem-ROT-form = pickᴰ 1 Sᴰ
  lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 841
  lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 2 Sᴰ
  lem-pass-S0-vs-TOFF012-CS03-TOFF012-CSd03 : St 1110
  lem-pass-S0-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 3 Sᴰ
  lem-pass-Sd0-vs-TOFF012-CS03-TOFF012-CSd03 : St 1114
  lem-pass-Sd0-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 4 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS02 : St 2019
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS02 = pickᴰ 5 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd02 : St 2020
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd02 = pickᴰ 6 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S2 : St 2021
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S2 = pickᴰ 7 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Sd2 : St 2022
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Sd2 = pickᴰ 8 Sᴰ
  lem-ROT≡cF : St 1425
  lem-ROT≡cF = pickᴰ 9 Sᴰ
  lem-R0 : St 2023
  lem-R0 = pickᴰ 10 Sᴰ
  lem-S2-at0213-ᵖ-1 : St 2024
  lem-S2-at0213-ᵖ-1 = pickᴰ 11 Sᴰ
  lem-pass-CS03-vs-TOFF012-CS03-TOFF012-CSd03 : St 2025
  lem-pass-CS03-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 12 Sᴰ
  lem-pass-CSd03-vs-TOFF012-CS03-TOFF012-CSd03 : St 2026
  lem-pass-CSd03-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 13 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-TOFF012-X1-X2-S0-CSd03-X1-X2-TOFF012-X1-X2-Sd0-CS03 : St 2027
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-TOFF012-X1-X2-S0-CSd03-X1-X2-TOFF012-X1-X2-Sd0-CS03 = pickᴰ 14 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03 : St 2028
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03 = pickᴰ 15 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3 : St 2029
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3 = pickᴰ 16 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF013-X3 : St 2030
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF013-X3 = pickᴰ 17 Sᴰ

private
  q1 : Eqn
  q1 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q2 : Eqn
  q2 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q3 : Eqn
  q3 = eqn (CS02⁻ ∷ []) (CS02 ∷ CS02 ∷ CS02 ∷ []) (wn 2086 W)
  q4 : Eqn
  q4 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03 ∷ []) (CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) lem-R0
  q5 : Eqn
  q5 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ []) (CS02⁻ ∷ []) (wn 310 W)

-- C3d-A: 25 steps
lem-C3d-A : ⟪ (CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-C3d-A = derive (CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw 1 q1 ∷
   re 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q2 ∷
   rw 1 q3 ∷
   rw 2 q1 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 4 q1 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q2 ∷
   rw⁻ 2 q4 ∷
   rw⁻ 1 q4 ∷
   rw⁻ 0 q4 ∷
   rw 6 q1 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q2 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q2 ∷
   rw 4 q5 ∷
   rw 5 q1 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 4 q2 ∷ []) Eq.refl

private
  q6 : Eqn
  q6 = eqn [] (Toff012 ∷ Toff012 ∷ []) (wn 45 W)
  q7 : Eqn
  q7 = eqn [] (CS02⁻ ∷ CS02 ∷ []) (wn 231 W)
  q8 : Eqn
  q8 = eqn (CS02 ∷ CS02⁻ ∷ []) [] (wn 1342 W)
  q9 : Eqn
  q9 = eqn (Toff012 ∷ Toff012 ∷ []) [] (wn 227 W)

-- C3-Ai: 17 steps
lem-C3-Ai : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ []) ⟫ʷ
lem-C3-Ai = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ [])
  (rw 0 q6 ∷
   rw 1 q1 ∷
   rw 2 q7 ∷
   rw 3 q1 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 4 q1 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q2 ∷
   rw⁻ 2 q4 ∷
   rw 7 q1 ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   rw 6 q8 ∷
   rw 5 q2 ∷
   rw 4 q9 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = eqn (Toff012 ∷ X3 ∷ []) (X3 ∷ Toff012 ∷ []) (low₃-comm (Toff) (X))
  q11 : Eqn
  q11 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q12 : Eqn
  q12 = eqn (X2 ∷ CS02 ∷ []) (S0 ∷ CS02⁻ ∷ X2 ∷ []) (wn 1962 W)
  q13 : Eqn
  q13 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q14 : Eqn
  q14 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q15 : Eqn
  q15 = eqn (X2 ∷ CS02⁻ ∷ []) (S0⁻ ∷ CS02 ∷ X2 ∷ []) (wn 1963 W)
  q16 : Eqn
  q16 = eqn (S0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑)))
  q17 : Eqn
  q17 = eqn (X2 ∷ Toff012 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ []) (wn 2016 W)
  q18 : Eqn
  q18 = eqn (S0 ∷ X2 ∷ []) (X2 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑)))
  q19 : Eqn
  q19 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q20 : Eqn
  q20 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q21 : Eqn
  q21 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q22 : Eqn
  q22 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q23 : Eqn
  q23 = eqn (X2 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X2 ∷ []) (wn 258 W)
  q24 : Eqn
  q24 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q25 : Eqn
  q25 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q26 : Eqn
  q26 = eqn (S0⁻ ∷ X2 ∷ []) (X2 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑)))
  q27 : Eqn
  q27 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q28 : Eqn
  q28 = eqn (X2 ∷ CS13 ∷ []) (CS13 ∷ X2 ∷ []) (wn 257 W)
  q29 : Eqn
  q29 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q30 : Eqn
  q30 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03)
  q31 : Eqn
  q31 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q32 : Eqn
  q32 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q33 : Eqn
  q33 = eqn (S0⁻ ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑ ↑)))
  q34 : Eqn
  q34 = eqn (X2 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (Toff012 ∷ X2 ∷ []) (wn 2017 W)
  q35 : Eqn
  q35 = eqn (S0 ∷ S0⁻ ∷ CS02 ∷ []) (CS02 ∷ []) (wn 1964 W)
  q36 : Eqn
  q36 = eqn (S0⁻ ∷ S0 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ []) (wn 2018 W)

-- pass [X2 X3 TOFF012 CS03 TOFF012 CSd03 X2 X3] [TOFF012 CS03 TOFF012 CSd03]: 139 steps
lem-pass-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 7 q10 ∷
   rw 10 q1 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q2 ∷
   rw 8 q11 ∷
   rw 9 q12 ∷
   rw⁻ 8 q13 ∷
   rw 11 q1 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   rw 10 q14 ∷
   rw 11 q2 ∷
   rw⁻ 10 q10 ∷
   rw 13 q1 ∷
   re 12 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q2 ∷
   rw 11 q11 ∷
   rw 12 q15 ∷
   rw⁻ 11 q16 ∷
   rw 14 q1 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q14 ∷
   rw 14 q2 ∷
   rw 6 q17 ∷
   rw⁻ 9 q18 ∷
   rw 12 q19 ∷
   re 11 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q20 ∷
   rw 12 q21 ∷
   rw⁻ 11 q20 ∷
   re 12 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q22 ∷
   rw 11 q23 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q20 ∷
   rw 11 q24 ∷
   rw 12 q20 ∷
   re 10 3 (CS03⁻ ∷ []) ∷
   rw 11 q22 ∷
   rw 12 q25 ∷
   rw 11 q17 ∷
   rw⁻ 14 q26 ∷
   rw 17 q19 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q20 ∷
   rw 17 q27 ∷
   rw⁻ 16 q20 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw⁻ 15 q22 ∷
   rw 16 q28 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q20 ∷
   rw 16 q29 ∷
   rw 17 q20 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 16 q22 ∷
   rw 17 q25 ∷
   rw 2 q30 ∷
   rw⁻ 1 q31 ∷
   rw⁻ 2 q10 ∷
   rw⁻ 3 q31 ∷
   rw⁻ 4 q32 ∷
   rw 7 q1 ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   rw 5 q11 ∷
   rw 6 q15 ∷
   rw⁻ 5 q16 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q14 ∷
   rw 8 q2 ∷
   rw⁻ 7 q31 ∷
   rw⁻ 8 q10 ∷
   rw⁻ 9 q31 ∷
   rw⁻ 10 q33 ∷
   rw 13 q1 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q2 ∷
   rw 11 q11 ∷
   rw 12 q12 ∷
   rw⁻ 11 q13 ∷
   rw 14 q1 ∷
   re 12 3 (CS03⁻ ∷ []) ∷
   rw 13 q14 ∷
   rw 14 q2 ∷
   rw 0 q34 ∷
   rw⁻ 1 q18 ∷
   rw⁻ 2 q26 ∷
   rw 5 q19 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q20 ∷
   rw 5 q27 ∷
   rw⁻ 4 q20 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 3 q22 ∷
   rw 4 q28 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q20 ∷
   rw 4 q29 ∷
   rw 5 q20 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q22 ∷
   rw 5 q25 ∷
   rw 4 q34 ∷
   rw⁻ 5 q26 ∷
   rw⁻ 6 q18 ∷
   rw 9 q19 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q20 ∷
   rw 9 q21 ∷
   rw⁻ 8 q20 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q22 ∷
   rw 8 q23 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q20 ∷
   rw 8 q24 ∷
   rw 9 q20 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw 8 q22 ∷
   rw 9 q25 ∷
   rw 4 q1 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q2 ∷
   rw 2 q16 ∷
   rw 1 q13 ∷
   rw 2 q35 ∷
   rw 3 q1 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q2 ∷
   rw 6 q1 ∷
   re 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   rw 4 q13 ∷
   rw 3 q16 ∷
   rw 4 q36 ∷
   rw 5 q1 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 4 q2 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = eqn (X1 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ X1 ∷ []) (wn 2019 W)
  q38 : Eqn
  q38 = eqn (S0 ∷ X1 ∷ []) (X1 ∷ S0 ∷ []) (low₁-comm (S) (X))
  q39 : Eqn
  q39 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q40 : Eqn
  q40 = eqn (X1 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X1 ∷ []) (wn 1051 W)
  q41 : Eqn
  q41 = eqn (S0⁻ ∷ X1 ∷ []) (X1 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) (X))
  q42 : Eqn
  q42 = eqn (X1 ∷ CS02 ∷ []) (CS02 ∷ X1 ∷ []) (wn 1049 W)
  q43 : Eqn
  q43 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-TOFF012-X1-X2-S0-CSd03-X1-X2-TOFF012-X1-X2-Sd0-CS03)
  q44 : Eqn
  q44 = eqn (X1 ∷ X3 ∷ []) (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑)))
  q45 : Eqn
  q45 = eqn (X2 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (wn 2020 W)
  q46 : Eqn
  q46 = eqn (X1 ∷ X1 ∷ Toff012 ∷ X1 ∷ []) (Toff012 ∷ X1 ∷ []) (wn 2021 W)

-- pass [X1 X2 X3 TOFF012 CS03 TOFF012 CSd03 X1 X2 X3] [TOFF012 CS03 TOFF012 CSd03]: 189 steps
lem-pass-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 9 q10 ∷
   rw 12 q1 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q2 ∷
   rw 10 q11 ∷
   rw 11 q12 ∷
   rw⁻ 10 q13 ∷
   rw 13 q1 ∷
   re 11 3 (CS03⁻ ∷ []) ∷
   rw 12 q14 ∷
   rw 13 q2 ∷
   rw⁻ 12 q10 ∷
   rw 15 q1 ∷
   re 14 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q2 ∷
   rw 13 q11 ∷
   rw 14 q15 ∷
   rw⁻ 13 q16 ∷
   rw 16 q1 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 15 q14 ∷
   rw 16 q2 ∷
   rw 8 q17 ∷
   rw⁻ 11 q18 ∷
   rw 14 q19 ∷
   re 13 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q20 ∷
   rw 14 q21 ∷
   rw⁻ 13 q20 ∷
   re 14 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q22 ∷
   rw 13 q23 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q20 ∷
   rw 13 q24 ∷
   rw 14 q20 ∷
   re 12 3 (CS03⁻ ∷ []) ∷
   rw 13 q22 ∷
   rw 14 q25 ∷
   rw 13 q17 ∷
   rw⁻ 16 q26 ∷
   rw 19 q19 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q20 ∷
   rw 19 q27 ∷
   rw⁻ 18 q20 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw⁻ 17 q22 ∷
   rw 18 q28 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q20 ∷
   rw 18 q29 ∷
   rw 19 q20 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 18 q22 ∷
   rw 19 q25 ∷
   rw 7 q37 ∷
   rw⁻ 12 q38 ∷
   rw 15 q1 ∷
   re 14 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q2 ∷
   rw 13 q39 ∷
   rw 14 q40 ∷
   rw 15 q1 ∷
   re 13 3 (CS03⁻ ∷ []) ∷
   rw⁻ 14 q39 ∷
   rw 15 q2 ∷
   rw 14 q37 ∷
   rw⁻ 19 q41 ∷
   rw 22 q1 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q2 ∷
   rw 20 q39 ∷
   rw 21 q42 ∷
   rw 22 q1 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw⁻ 21 q39 ∷
   rw 22 q2 ∷
   rw 3 q43 ∷
   rw⁻ 2 q44 ∷
   rw⁻ 3 q31 ∷
   rw⁻ 4 q10 ∷
   rw⁻ 5 q44 ∷
   rw⁻ 6 q31 ∷
   rw⁻ 7 q32 ∷
   rw 10 q1 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q2 ∷
   rw 8 q11 ∷
   rw 9 q15 ∷
   rw⁻ 8 q16 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q14 ∷
   rw 11 q2 ∷
   rw⁻ 10 q44 ∷
   rw⁻ 11 q31 ∷
   rw⁻ 12 q10 ∷
   rw⁻ 13 q44 ∷
   rw⁻ 14 q31 ∷
   rw⁻ 15 q33 ∷
   rw 18 q1 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q2 ∷
   rw 16 q11 ∷
   rw 17 q12 ∷
   rw⁻ 16 q13 ∷
   rw 19 q1 ∷
   re 17 3 (CS03⁻ ∷ []) ∷
   rw 18 q14 ∷
   rw 19 q2 ∷
   rw 1 q45 ∷
   rw⁻ 4 q18 ∷
   rw⁻ 5 q26 ∷
   rw 8 q19 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q20 ∷
   rw 8 q27 ∷
   rw⁻ 7 q20 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 6 q22 ∷
   rw 7 q28 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q20 ∷
   rw 7 q29 ∷
   rw 8 q20 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q22 ∷
   rw 8 q25 ∷
   rw 7 q45 ∷
   rw⁻ 10 q26 ∷
   rw⁻ 11 q18 ∷
   rw 14 q19 ∷
   re 13 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q20 ∷
   rw 14 q21 ∷
   rw⁻ 13 q20 ∷
   re 14 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q22 ∷
   rw 13 q23 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q20 ∷
   rw 13 q24 ∷
   rw 14 q20 ∷
   re 12 3 (CS03⁻ ∷ []) ∷
   rw 13 q22 ∷
   rw 14 q25 ∷
   rw 0 q46 ∷
   rw⁻ 1 q38 ∷
   rw⁻ 2 q41 ∷
   rw 5 q1 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q2 ∷
   rw 3 q39 ∷
   rw 4 q42 ∷
   rw 5 q1 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw⁻ 4 q39 ∷
   rw 5 q2 ∷
   rw 4 q46 ∷
   rw⁻ 5 q41 ∷
   rw⁻ 6 q38 ∷
   rw 9 q1 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   rw 7 q39 ∷
   rw 8 q40 ∷
   rw 9 q1 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw⁻ 8 q39 ∷
   rw 9 q2 ∷
   rw 4 q1 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q2 ∷
   rw 2 q16 ∷
   rw 1 q13 ∷
   rw 2 q35 ∷
   rw 3 q1 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q2 ∷
   rw 6 q1 ∷
   re 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   rw 4 q13 ∷
   rw 3 q16 ∷
   rw 4 q36 ∷
   rw 5 q1 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 4 q2 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF013-X3)
  q48 : Eqn
  q48 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS02 ∷ []) (CS02 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS02)
  q49 : Eqn
  q49 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd02)

-- pass [TOFF102 CS13 TOFF102 CSd13] [X3 TOFF013 X3 CS02 X3 TOFF013 X3 CSd02]: 4 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw 0 q47 ∷
   rw 3 q48 ∷
   rw 4 q47 ∷
   rw 7 q49 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3)

-- pass [TOFF102 CS13 TOFF102 CSd13] [X1 X3 TOFF013 X1 X3 CS02 X1 X3 TOFF013 X1 X3 CSd02]: 4 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3-CS02-X1-X3-TOFF013-X1-X3-CSd02 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ CS02 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ CS02 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ CS02⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3-CS02-X1-X3-TOFF013-X1-X3-CSd02 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ CS02 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ CS02⁻ ∷ []) (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ CS02 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ CS02⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw 0 q50 ∷
   rw 5 q48 ∷
   rw 6 q50 ∷
   rw 11 q49 ∷ []) Eq.refl

private
  q51 : Eqn
  q51 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S2 ∷ []) (S2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S2)
  q52 : Eqn
  q52 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Sd2)

-- pass [TOFF102 CS13 TOFF102 CSd13] [X3 TOFF013 X3 S2 CSd02 X3 TOFF013 X3 Sd2 CS02]: 6 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF013-X3-S2-CSd02-X3-TOFF013-X3-Sd2-CS02 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF013-X3-S2-CSd02-X3-TOFF013-X3-Sd2-CS02 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw 0 q47 ∷
   rw 3 q51 ∷
   rw 4 q49 ∷
   rw 5 q47 ∷
   rw 8 q52 ∷
   rw 9 q48 ∷ []) Eq.refl

-- pass [TOFF102 CS13 TOFF102 CSd13] [X1 X3 TOFF013 X1 X3 S2 CSd02 X1 X3 TOFF013 X1 X3 Sd2 CS02]: 6 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3-S2-CSd02-X1-X3-TOFF013-X1-X3-Sd2-CS02 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3-S2-CSd02-X1-X3-TOFF013-X1-X3-Sd2-CS02 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ []) (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw 0 q50 ∷
   rw 5 q51 ∷
   rw 6 q49 ∷
   rw 7 q50 ∷
   rw 12 q52 ∷
   rw 13 q48 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = eqn (K0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑)))
  q54 : Eqn
  q54 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q55 : Eqn
  q55 = eqn (X2 ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X2 ∷ []) (X2 ∷ CK20 ∷ X2 ∷ S0 ∷ CS02⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 2087 W)
  q56 : Eqn
  q56 = eqn (X3 ∷ CK30⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
  q57 : Eqn
  q57 = eqn (CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-TOFF012-CS03-TOFF012-CSd03)
  q58 : Eqn
  q58 = eqn (S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ []) (lem-pass-S0-vs-TOFF012-CS03-TOFF012-CSd03)
  q59 : Eqn
  q59 = eqn (X3 ∷ CK30 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
  q60 : Eqn
  q60 = eqn (X2 ∷ CK20 ∷ X2 ∷ S0 ∷ CS02⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (X2 ∷ K0 ∷ CS02 ∷ K0⁻ ∷ X2 ∷ []) (wn 2088 W)

-- pass [X3 K0 CS03 Kd0 X3] [TOFF012 CS03 TOFF012 CSd03]: 44 steps
lem-pass-X3-K0-CS03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X3 ∷ K0 ∷ CS03 ∷ K0⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ K0 ∷ CS03 ∷ K0⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-K0-CS03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (X3 ∷ K0 ∷ CS03 ∷ K0⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ K0 ∷ CS03 ∷ K0⁻ ∷ X3 ∷ [])
  (rw 5 q1 ∷
   rw 4 q11 ∷
   rw 3 q53 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q2 ∷
   rw 1 q54 ∷
   rw 0 q11 ∷
   rw 1 q55 ∷
   rw 0 q14 ∷
   rw 3 q1 ∷
   re 1 3 (CK30 ∷ []) ∷
   rw 2 q14 ∷
   rw⁻ 3 q13 ∷
   rw 6 q1 ∷
   re 4 3 (CS03⁻ ∷ []) ∷
   rw 5 q14 ∷
   rw 8 q1 ∷
   re 6 3 (CK30⁻ ∷ []) ∷
   rw 7 q14 ∷
   rw 8 q2 ∷
   rw 5 q56 ∷
   rw 4 q57 ∷
   rw 3 q58 ∷
   rw 0 q59 ∷
   rw 12 q1 ∷
   rw 11 q11 ∷
   re 10 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q2 ∷
   rw 9 q11 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   rw 7 q13 ∷
   rw 6 q11 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   rw 4 q11 ∷
   rw 5 q60 ∷
   rw 4 q14 ∷
   rw⁻ 5 q54 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q53 ∷
   rw 8 q14 ∷
   rw 9 q2 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = eqn (X2 ∷ K0 ∷ CS02⁻ ∷ K0⁻ ∷ X2 ∷ []) (X2 ∷ CK20 ∷ X2 ∷ S0⁻ ∷ CS02 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 2089 W)
  q62 : Eqn
  q62 = eqn (CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03 ∷ []) (lem-pass-CS03-vs-TOFF012-CS03-TOFF012-CSd03)
  q63 : Eqn
  q63 = eqn (S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ []) (lem-pass-Sd0-vs-TOFF012-CS03-TOFF012-CSd03)
  q64 : Eqn
  q64 = eqn (X2 ∷ CK20 ∷ X2 ∷ S0⁻ ∷ CS02 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (X2 ∷ K0 ∷ CS02⁻ ∷ K0⁻ ∷ X2 ∷ []) (wn 2090 W)

-- pass [X3 K0 CSd03 Kd0 X3] [TOFF012 CS03 TOFF012 CSd03]: 44 steps
lem-pass-X3-K0-CSd03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X3 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-K0-CSd03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (X3 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ X3 ∷ [])
  (rw 5 q1 ∷
   rw 4 q11 ∷
   rw 3 q53 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q2 ∷
   rw 1 q54 ∷
   rw 0 q11 ∷
   rw 1 q61 ∷
   rw 0 q14 ∷
   rw 3 q1 ∷
   re 1 3 (CK30 ∷ []) ∷
   rw 2 q14 ∷
   rw⁻ 3 q16 ∷
   rw 6 q1 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q14 ∷
   rw 8 q1 ∷
   re 6 3 (CK30⁻ ∷ []) ∷
   rw 7 q14 ∷
   rw 8 q2 ∷
   rw 5 q56 ∷
   rw 4 q62 ∷
   rw 3 q63 ∷
   rw 0 q59 ∷
   rw 12 q1 ∷
   rw 11 q11 ∷
   re 10 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q2 ∷
   rw 9 q11 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   rw 7 q16 ∷
   rw 6 q11 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   rw 4 q11 ∷
   rw 5 q64 ∷
   rw 4 q14 ∷
   rw⁻ 5 q54 ∷
   rw 8 q1 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   rw⁻ 7 q53 ∷
   rw 8 q14 ∷
   rw 9 q2 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = eqn (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ023 ∷ []) (lem-ROT≡cF)
  q66 : Eqn
  q66 = eqn (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ023 ∷ []) (K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ K0 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ K0⁻ ∷ []) (lem-ROT-form)
  q67 : Eqn
  q67 = eqn (K0⁻ ∷ Sw12 ∷ []) (Sw12 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) (Swap))
  q68 : Eqn
  q68 = eqn (S0 ∷ Sw12 ∷ []) (Sw12 ∷ S0 ∷ []) (low₁-comm (S) (Swap))
  q69 : Eqn
  q69 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap))
  q70 : Eqn
  q70 = eqn (S0⁻ ∷ Sw12 ∷ []) (Sw12 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) (Swap))
  q71 : Eqn
  q71 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q72 : Eqn
  q72 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q73 : Eqn
  q73 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q74 : Eqn
  q74 = eqn (Sw12 ∷ CS12 ∷ []) (CS12 ∷ Sw12 ∷ []) (wn 18 W)
  q75 : Eqn
  q75 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q76 : Eqn
  q76 = eqn (Sw12 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Sw12 ∷ []) (wn 19 W)
  q77 : Eqn
  q77 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q78 : Eqn
  q78 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q79 : Eqn
  q79 = eqn (K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 46 W)
  q80 : Eqn
  q80 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q81 : Eqn
  q81 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q82 : Eqn
  q82 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q83 : Eqn
  q83 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 56 W)
  q84 : Eqn
  q84 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q85 : Eqn
  q85 = eqn (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) (wn 21 W)
  q86 : Eqn
  q86 = eqn (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) (wn 123 W)
  q87 : Eqn
  q87 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q88 : Eqn
  q88 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q89 : Eqn
  q89 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q90 : Eqn
  q90 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q91 : Eqn
  q91 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)
  q92 : Eqn
  q92 = eqn (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wn 125 W)
  q93 : Eqn
  q93 = eqn (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) lem-S2-at0213-ᵖ-1
  q94 : Eqn
  q94 = eqn (K0 ∷ K0⁻ ∷ S0 ∷ K0 ∷ []) (S0 ∷ K0 ∷ []) (wn 2091 W)
  q95 : Eqn
  q95 = eqn (K0⁻ ∷ S0⁻ ∷ K0 ∷ K0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ []) (wn 2092 W)

-- ROT-gad: 214 steps
lem-ROT-gad : ⟪ (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-ROT-gad = derive (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ [])
  (rw 0 q65 ∷
   rw 0 q66 ∷
   rw⁻ 3 q67 ∷
   rw⁻ 2 q53 ∷
   rw⁻ 1 q67 ∷
   rw⁻ 4 q68 ∷
   rw⁻ 3 q13 ∷
   rw⁻ 2 q68 ∷
   rw⁻ 5 q69 ∷
   rw⁻ 4 q54 ∷
   rw⁻ 3 q69 ∷
   rw 13 q69 ∷
   rw 12 q70 ∷
   rw 11 q67 ∷
   rw 14 q54 ∷
   rw 13 q16 ∷
   rw 12 q53 ∷
   rw 15 q69 ∷
   rw 14 q70 ∷
   rw 13 q67 ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 6 q71 ∷
   rw⁻ 8 q72 ∷
   rw 9 q73 ∷
   re 6 5 (CS03 ∷ []) ∷
   re 8 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 7 q69 ∷
   rw 8 q74 ∷
   rw 11 q75 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 10 q76 ∷
   rw 13 q75 ∷
   re 11 3 (CX02 ∷ []) ∷
   re 13 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 12 q77 ∷
   rw⁻ 13 q69 ∷
   rw⁻ 14 q78 ∷
   rw 7 q79 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q71 ∷
   rw⁻ 10 q80 ∷
   rw 11 q73 ∷
   re 8 5 (CS03⁻ ∷ []) ∷
   re 10 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 9 q69 ∷
   rw 10 q74 ∷
   rw 13 q75 ∷
   re 11 3 (CX02 ∷ []) ∷
   rw 12 q76 ∷
   rw 15 q75 ∷
   re 13 3 (CX02 ∷ []) ∷
   re 15 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 14 q77 ∷
   rw⁻ 15 q69 ∷
   rw⁻ 16 q78 ∷
   rw 9 q79 ∷
   re 9 8 (Toff012 ∷ []) ∷
   rw 10 q77 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q2 ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 6 q54 ∷
   rw 9 q1 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q81 ∷
   rw 11 q1 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q81 ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q54 ∷
   rw⁻ 13 q82 ∷
   rw 6 q1 ∷
   rw⁻ 7 q54 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   rw⁻ 9 q81 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   rw⁻ 11 q81 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q2 ∷
   rw⁻ 13 q54 ∷
   rw⁻ 14 q82 ∷
   rw 7 q83 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 6 3 (Toff013 ∷ []) ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   re 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 8 q54 ∷
   rw 11 q1 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 10 q81 ∷
   rw 13 q1 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q81 ∷
   rw 15 q1 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw⁻ 14 q54 ∷
   rw⁻ 15 q82 ∷
   rw 8 q1 ∷
   rw⁻ 9 q54 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   rw⁻ 11 q81 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q2 ∷
   rw⁻ 13 q81 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q2 ∷
   rw⁻ 15 q54 ∷
   rw⁻ 16 q82 ∷
   rw 9 q83 ∷
   re 9 8 (Toff012 ∷ []) ∷
   re 8 3 (Toff013 ∷ []) ∷
   rw 9 q2 ∷
   re 5 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 4 q77 ∷
   re 6 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 6 q54 ∷
   rw 9 q1 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q81 ∷
   rw 11 q1 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q81 ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q54 ∷
   rw⁻ 13 q82 ∷
   rw 14 q2 ∷
   rw⁻ 5 q69 ∷
   rw 6 q84 ∷
   rw 9 q75 ∷
   re 7 3 (CX02 ∷ []) ∷
   rw 8 q85 ∷
   rw 11 q75 ∷
   re 9 3 (CX02 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 10 q71 ∷
   rw⁻ 12 q72 ∷
   rw 13 q73 ∷
   re 10 5 (CS03 ∷ []) ∷
   rw⁻ 11 q69 ∷
   rw⁻ 12 q78 ∷
   rw 5 q19 ∷
   rw 6 q86 ∷
   rw 7 q87 ∷
   rw 8 q88 ∷
   rw 9 q89 ∷
   rw 10 q88 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q20 ∷
   rw 12 q90 ∷
   rw 13 q20 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 12 q86 ∷
   rw 13 q91 ∷
   rw 6 q92 ∷
   re 6 8 (Toff123 ∷ []) ∷
   re 5 3 (Toff023 ∷ []) ∷
   re 7 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 6 q77 ∷
   re 8 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 8 q54 ∷
   rw 11 q1 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 10 q81 ∷
   rw 13 q1 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q81 ∷
   rw 15 q1 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw⁻ 14 q54 ∷
   rw⁻ 15 q82 ∷
   rw 16 q2 ∷
   rw⁻ 7 q69 ∷
   rw 8 q84 ∷
   rw 11 q75 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 10 q85 ∷
   rw 13 q75 ∷
   re 11 3 (CX02 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 12 q71 ∷
   rw⁻ 14 q72 ∷
   rw 15 q73 ∷
   re 12 5 (CS03 ∷ []) ∷
   rw⁻ 13 q69 ∷
   rw⁻ 14 q78 ∷
   rw 7 q19 ∷
   rw 8 q86 ∷
   rw 9 q87 ∷
   rw 10 q88 ∷
   rw 11 q89 ∷
   rw 12 q88 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q20 ∷
   rw 14 q90 ∷
   rw 15 q20 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 14 q86 ∷
   rw 15 q91 ∷
   rw 8 q92 ∷
   re 8 8 (Toff123 ∷ []) ∷
   re 7 3 (Toff023 ∷ []) ∷
   rw 8 q77 ∷
   rw⁻ 4 q93 ∷
   rw 0 q94 ∷
   rw 6 q95 ∷ []) Eq.refl
