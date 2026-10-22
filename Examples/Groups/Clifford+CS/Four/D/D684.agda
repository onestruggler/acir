{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD684 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D684 (W : Ws) (Sᴰ : SD684) where

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
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-TOFF102-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 : St 1805
  lem-pass-TOFF102-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 = pickᴰ 0 Sᴰ
  lem-S2 : St 1778
  lem-S2 = pickᴰ 1 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02 : St 1806
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02 = pickᴰ 2 Sᴰ
  lem-pass-CS13-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 : St 1807
  lem-pass-CS13-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 = pickᴰ 3 Sᴰ
  lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-S0-CSd03 : St 1808
  lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-S0-CSd03 = pickᴰ 4 Sᴰ
  lem-pass-CSd13-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 : St 1809
  lem-pass-CSd13-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 = pickᴰ 5 Sᴰ

private
  q1 : Eqn
  q1 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q2 : Eqn
  q2 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q3 : Eqn
  q3 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q4 : Eqn
  q4 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q5 : Eqn
  q5 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q6 : Eqn
  q6 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 56 W)
  q7 : Eqn
  q7 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q8 : Eqn
  q8 = eqn (X2 ∷ Toff012 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ []) (wn 2016 W)
  q9 : Eqn
  q9 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q10 : Eqn
  q10 = eqn (CS02 ∷ X3 ∷ []) (X3 ∷ CS02 ∷ []) (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q11 : Eqn
  q11 = eqn (CS02⁻ ∷ X3 ∷ []) (X3 ∷ CS02⁻ ∷ []) (low₃-comm ((Swap ↑ • (CS • CS • CS) • Swap ↑)) (X))
  q12 : Eqn
  q12 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q13 : Eqn
  q13 = eqn (X2 ∷ Sw23 ∷ []) (Sw23 ∷ X3 ∷ []) (wn 1609 W)
  q14 : Eqn
  q14 = eqn (Toff012 ∷ X3 ∷ []) (X3 ∷ Toff012 ∷ []) (low₃-comm (Toff) (X))
  q15 : Eqn
  q15 = eqn (X2 ∷ CS02 ∷ []) (S0 ∷ CS02⁻ ∷ X2 ∷ []) (wn 1962 W)
  q16 : Eqn
  q16 = eqn (X2 ∷ CS02⁻ ∷ []) (S0⁻ ∷ CS02 ∷ X2 ∷ []) (wn 1963 W)
  q17 : Eqn
  q17 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q18 : Eqn
  q18 = eqn (X1 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ X1 ∷ []) (wn 2019 W)
  q19 : Eqn
  q19 = eqn (S0 ∷ X1 ∷ []) (X1 ∷ S0 ∷ []) (low₁-comm (S) (X))
  q20 : Eqn
  q20 = eqn (X1 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X1 ∷ []) (wn 1051 W)
  q21 : Eqn
  q21 = eqn (S0⁻ ∷ X1 ∷ []) (X1 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) (X))
  q22 : Eqn
  q22 = eqn (X1 ∷ CS02 ∷ []) (CS02 ∷ X1 ∷ []) (wn 1049 W)
  q23 : Eqn
  q23 = eqn (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02)
  q24 : Eqn
  q24 = eqn (X2 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (wn 2020 W)
  q25 : Eqn
  q25 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q26 : Eqn
  q26 = eqn (S0⁻ ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑ ↑)))
  q27 : Eqn
  q27 = eqn (X1 ∷ X2 ∷ []) (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X))
  q28 : Eqn
  q28 = eqn (S0 ∷ X2 ∷ []) (X2 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑)))
  q29 : Eqn
  q29 = eqn (S0⁻ ∷ X2 ∷ []) (X2 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑)))
  q30 : Eqn
  q30 = eqn (X1 ∷ X1 ∷ Toff012 ∷ X1 ∷ []) (Toff012 ∷ X1 ∷ []) (wn 2021 W)
  q31 : Eqn
  q31 = eqn (S0 ∷ S0⁻ ∷ CS02 ∷ []) (CS02 ∷ []) (wn 1964 W)
  q32 : Eqn
  q32 = eqn (S0⁻ ∷ S0 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ []) (wn 2018 W)

-- pass [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3] [TOFF013 CS02 TOFF013 CSd02]: 557 steps
lem-pass-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3-vs-TOFF013-CS02-TOFF013-CSd02 = derive (X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ X2 ∷ X3 ∷ [])
  (rw 11 q1 ∷
   re 10 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 11 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 10 q2 ∷
   rw 13 q1 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw⁻ 12 q3 ∷
   rw 15 q1 ∷
   re 13 3 (CS13⁻ ∷ []) ∷
   rw⁻ 14 q3 ∷
   rw 17 q1 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw⁻ 16 q2 ∷
   rw⁻ 17 q4 ∷
   rw 18 q5 ∷
   rw 17 q4 ∷
   rw 16 q2 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q5 ∷
   rw 14 q3 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   rw 12 q3 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   rw 10 q2 ∷
   rw 11 q6 ∷
   re 11 8 (Toff012 ∷ []) ∷
   rw 9 q7 ∷
   rw 10 q8 ∷
   rw 9 q9 ∷
   re 11 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 10 q2 ∷
   rw 13 q1 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw⁻ 12 q3 ∷
   rw 15 q1 ∷
   re 13 3 (CS13⁻ ∷ []) ∷
   rw⁻ 14 q3 ∷
   rw 17 q1 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw⁻ 16 q2 ∷
   rw⁻ 17 q4 ∷
   rw 10 q1 ∷
   rw⁻ 11 q2 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q5 ∷
   rw⁻ 13 q3 ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q5 ∷
   rw⁻ 15 q3 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q5 ∷
   rw⁻ 17 q2 ∷
   rw⁻ 18 q4 ∷
   rw 11 q6 ∷
   re 11 8 (Toff012 ∷ []) ∷
   re 10 3 (Toff013 ∷ []) ∷
   rw 11 q9 ∷
   rw 12 q9 ∷
   rw 13 q5 ∷
   rw⁻ 12 q10 ∷
   rw 15 q1 ∷
   re 14 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 15 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 14 q2 ∷
   rw 17 q1 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw⁻ 16 q3 ∷
   rw 19 q1 ∷
   re 17 3 (CS13⁻ ∷ []) ∷
   rw⁻ 18 q3 ∷
   rw 21 q1 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw⁻ 20 q2 ∷
   rw⁻ 21 q4 ∷
   rw 22 q5 ∷
   rw 21 q4 ∷
   rw 20 q2 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q5 ∷
   rw 18 q3 ∷
   re 17 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q5 ∷
   rw 16 q3 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q5 ∷
   rw 14 q2 ∷
   rw 15 q6 ∷
   re 15 8 (Toff012 ∷ []) ∷
   rw 13 q7 ∷
   rw 14 q8 ∷
   rw 13 q9 ∷
   re 15 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 14 q2 ∷
   rw 17 q1 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw⁻ 16 q3 ∷
   rw 19 q1 ∷
   re 17 3 (CS13⁻ ∷ []) ∷
   rw⁻ 18 q3 ∷
   rw 21 q1 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw⁻ 20 q2 ∷
   rw⁻ 21 q4 ∷
   rw 14 q1 ∷
   rw⁻ 15 q2 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q5 ∷
   rw⁻ 17 q3 ∷
   re 19 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q5 ∷
   rw⁻ 19 q3 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q5 ∷
   rw⁻ 21 q2 ∷
   rw⁻ 22 q4 ∷
   rw 15 q6 ∷
   re 15 8 (Toff012 ∷ []) ∷
   re 14 3 (Toff013 ∷ []) ∷
   rw 15 q9 ∷
   rw 16 q9 ∷
   rw 17 q5 ∷
   rw⁻ 16 q11 ∷
   rw 8 q12 ∷
   re 10 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   rw 9 q13 ∷
   rw⁻ 10 q14 ∷
   rw 11 q7 ∷
   re 9 3 (Toff013 ∷ []) ∷
   rw 10 q12 ∷
   rw 11 q15 ∷
   rw 13 q12 ∷
   re 15 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   rw 14 q13 ∷
   rw⁻ 15 q14 ∷
   rw 16 q7 ∷
   re 14 3 (Toff013 ∷ []) ∷
   rw 15 q12 ∷
   rw 16 q16 ∷
   rw 11 q1 ∷
   rw 10 q7 ∷
   re 9 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 10 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 9 q2 ∷
   rw 12 q1 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw⁻ 11 q3 ∷
   rw 14 q1 ∷
   re 12 3 (CS13⁻ ∷ []) ∷
   rw⁻ 13 q3 ∷
   rw 16 q1 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw⁻ 15 q2 ∷
   rw⁻ 16 q4 ∷
   rw 17 q5 ∷
   rw 16 q4 ∷
   rw 15 q2 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q5 ∷
   rw 13 q3 ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q5 ∷
   rw 11 q3 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q5 ∷
   rw 9 q2 ∷
   rw 10 q6 ∷
   re 10 8 (Toff012 ∷ []) ∷
   rw 8 q7 ∷
   rw 7 q17 ∷
   rw 8 q18 ∷
   rw⁻ 7 q17 ∷
   rw 8 q9 ∷
   re 10 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 9 q2 ∷
   rw 12 q1 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw⁻ 11 q3 ∷
   rw 14 q1 ∷
   re 12 3 (CS13⁻ ∷ []) ∷
   rw⁻ 13 q3 ∷
   rw 16 q1 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw⁻ 15 q2 ∷
   rw⁻ 16 q4 ∷
   rw 9 q1 ∷
   rw⁻ 10 q2 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   rw⁻ 12 q3 ∷
   re 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   rw⁻ 14 q3 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   rw⁻ 16 q2 ∷
   rw⁻ 17 q4 ∷
   rw 10 q6 ∷
   re 10 8 (Toff012 ∷ []) ∷
   re 9 3 (Toff013 ∷ []) ∷
   rw⁻ 10 q17 ∷
   rw 11 q9 ∷
   rw⁻ 12 q17 ∷
   rw 13 q5 ∷
   rw⁻ 12 q19 ∷
   rw 13 q20 ∷
   rw 18 q1 ∷
   rw 17 q7 ∷
   re 16 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 17 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 16 q2 ∷
   rw 19 q1 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw⁻ 18 q3 ∷
   rw 21 q1 ∷
   re 19 3 (CS13⁻ ∷ []) ∷
   rw⁻ 20 q3 ∷
   rw 23 q1 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw⁻ 22 q2 ∷
   rw⁻ 23 q4 ∷
   rw 24 q5 ∷
   rw 23 q4 ∷
   rw 22 q2 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q5 ∷
   rw 20 q3 ∷
   re 19 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 21 q5 ∷
   rw 18 q3 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q5 ∷
   rw 16 q2 ∷
   rw 17 q6 ∷
   re 17 8 (Toff012 ∷ []) ∷
   rw 15 q7 ∷
   rw 14 q17 ∷
   rw 15 q18 ∷
   rw⁻ 14 q17 ∷
   rw 15 q9 ∷
   re 17 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 16 q2 ∷
   rw 19 q1 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw⁻ 18 q3 ∷
   rw 21 q1 ∷
   re 19 3 (CS13⁻ ∷ []) ∷
   rw⁻ 20 q3 ∷
   rw 23 q1 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw⁻ 22 q2 ∷
   rw⁻ 23 q4 ∷
   rw 16 q1 ∷
   rw⁻ 17 q2 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q5 ∷
   rw⁻ 19 q3 ∷
   re 21 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q5 ∷
   rw⁻ 21 q3 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q5 ∷
   rw⁻ 23 q2 ∷
   rw⁻ 24 q4 ∷
   rw 17 q6 ∷
   re 17 8 (Toff012 ∷ []) ∷
   re 16 3 (Toff013 ∷ []) ∷
   rw⁻ 17 q17 ∷
   rw 18 q9 ∷
   rw⁻ 19 q17 ∷
   rw 20 q5 ∷
   rw⁻ 19 q21 ∷
   rw 20 q22 ∷
   rw 3 q23 ∷
   rw 8 q1 ∷
   rw 7 q7 ∷
   rw 6 q17 ∷
   re 5 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 5 q2 ∷
   rw 8 q1 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q3 ∷
   rw 12 q1 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 q2 ∷
   rw⁻ 12 q4 ∷
   rw 13 q5 ∷
   rw 12 q4 ∷
   rw 11 q2 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q5 ∷
   rw 9 q3 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw 7 q3 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 5 q2 ∷
   rw 6 q6 ∷
   re 6 8 (Toff012 ∷ []) ∷
   rw 4 q7 ∷
   rw 3 q17 ∷
   rw 2 q7 ∷
   rw 3 q24 ∷
   rw⁻ 2 q17 ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q2 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q2 ∷
   rw⁻ 10 q4 ∷
   rw 3 q1 ∷
   rw⁻ 4 q2 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw⁻ 6 q3 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw⁻ 8 q3 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw⁻ 10 q2 ∷
   rw⁻ 11 q4 ∷
   rw 4 q6 ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 3 3 (Toff013 ∷ []) ∷
   rw⁻ 4 q17 ∷
   rw 5 q9 ∷
   rw 6 q5 ∷
   rw⁻ 5 q25 ∷
   rw⁻ 6 q11 ∷
   rw 13 q1 ∷
   rw 12 q7 ∷
   rw 11 q17 ∷
   re 10 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 11 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 10 q2 ∷
   rw 13 q1 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw⁻ 12 q3 ∷
   rw 15 q1 ∷
   re 13 3 (CS13⁻ ∷ []) ∷
   rw⁻ 14 q3 ∷
   rw 17 q1 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw⁻ 16 q2 ∷
   rw⁻ 17 q4 ∷
   rw 18 q5 ∷
   rw 17 q4 ∷
   rw 16 q2 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q5 ∷
   rw 14 q3 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   rw 12 q3 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   rw 10 q2 ∷
   rw 11 q6 ∷
   re 11 8 (Toff012 ∷ []) ∷
   rw 9 q7 ∷
   rw 8 q17 ∷
   rw 7 q7 ∷
   rw 8 q24 ∷
   rw⁻ 7 q17 ∷
   re 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 8 q2 ∷
   rw 11 q1 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 10 q3 ∷
   rw 13 q1 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q3 ∷
   rw 15 q1 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw⁻ 14 q2 ∷
   rw⁻ 15 q4 ∷
   rw 8 q1 ∷
   rw⁻ 9 q2 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw⁻ 11 q3 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q5 ∷
   rw⁻ 13 q3 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q5 ∷
   rw⁻ 15 q2 ∷
   rw⁻ 16 q4 ∷
   rw 9 q6 ∷
   re 9 8 (Toff012 ∷ []) ∷
   re 8 3 (Toff013 ∷ []) ∷
   rw⁻ 9 q17 ∷
   rw 10 q9 ∷
   rw 11 q5 ∷
   rw⁻ 10 q26 ∷
   rw⁻ 11 q10 ∷
   rw⁻ 1 q27 ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   rw 2 q13 ∷
   rw⁻ 3 q14 ∷
   rw 4 q7 ∷
   re 2 3 (Toff013 ∷ []) ∷
   rw⁻ 3 q27 ∷
   rw⁻ 4 q28 ∷
   rw 5 q16 ∷
   rw⁻ 7 q27 ∷
   re 9 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   rw 8 q13 ∷
   rw⁻ 9 q14 ∷
   rw 10 q7 ∷
   re 8 3 (Toff013 ∷ []) ∷
   rw⁻ 9 q27 ∷
   rw⁻ 10 q29 ∷
   rw 11 q15 ∷
   rw 4 q1 ∷
   rw 3 q17 ∷
   re 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q2 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q2 ∷
   rw⁻ 9 q4 ∷
   rw 10 q5 ∷
   rw 9 q4 ∷
   rw 8 q2 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 6 q3 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 4 q3 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 2 q2 ∷
   rw 3 q6 ∷
   re 3 8 (Toff012 ∷ []) ∷
   rw 1 q17 ∷
   rw 0 q17 ∷
   rw 1 q30 ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 0 q2 ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q2 ∷
   rw⁻ 7 q4 ∷
   rw 0 q1 ∷
   rw⁻ 1 q2 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw⁻ 7 q2 ∷
   rw⁻ 8 q4 ∷
   rw 1 q6 ∷
   re 1 8 (Toff012 ∷ []) ∷
   re 0 3 (Toff013 ∷ []) ∷
   rw⁻ 1 q17 ∷
   rw 2 q5 ∷
   rw⁻ 1 q19 ∷
   rw⁻ 2 q21 ∷
   rw 3 q22 ∷
   rw 8 q1 ∷
   rw 7 q17 ∷
   re 6 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 6 q2 ∷
   rw 9 q1 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q3 ∷
   rw 11 q1 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q3 ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q2 ∷
   rw⁻ 13 q4 ∷
   rw 14 q5 ∷
   rw 13 q4 ∷
   rw 12 q2 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   rw 10 q3 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   rw 8 q3 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 6 q2 ∷
   rw 7 q6 ∷
   re 7 8 (Toff012 ∷ []) ∷
   rw 5 q17 ∷
   rw 4 q17 ∷
   rw 5 q30 ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 4 q2 ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q3 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q2 ∷
   rw⁻ 11 q4 ∷
   rw 4 q1 ∷
   rw⁻ 5 q2 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw⁻ 9 q3 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw⁻ 11 q2 ∷
   rw⁻ 12 q4 ∷
   rw 5 q6 ∷
   re 5 8 (Toff012 ∷ []) ∷
   re 4 3 (Toff013 ∷ []) ∷
   rw⁻ 5 q17 ∷
   rw 6 q5 ∷
   rw⁻ 5 q21 ∷
   rw⁻ 6 q19 ∷
   rw 7 q20 ∷
   rw 1 q31 ∷
   rw 3 q32 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q34 : Eqn
  q34 = eqn (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0 ∷ CS03⁻ ∷ []) (S0 ∷ CS03⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-S0-CSd03)
  q35 : Eqn
  q35 = eqn (S0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑)))

-- pass [X3 CS23 TOFF201 CSd23 TOFF201 X3] [CS03]: 31 steps
lem-pass-X3-CS23-TOFF201-CSd23-TOFF201-X3-vs-CS03 : ⟪ (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS23-TOFF201-CSd23-TOFF201-X3-vs-CS03 = derive (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS03 ∷ []) (CS03 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ [])
  (rw 7 q1 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 5 q7 ∷
   rw 6 q15 ∷
   rw⁻ 5 q33 ∷
   rw 8 q1 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   rw 7 q9 ∷
   rw 8 q5 ∷
   rw 1 q34 ∷
   rw⁻ 0 q25 ∷
   rw 3 q1 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 1 q7 ∷
   rw 2 q16 ∷
   rw⁻ 1 q35 ∷
   rw 4 q1 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q9 ∷
   rw 4 q5 ∷
   rw 3 q1 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 1 q35 ∷
   rw 0 q33 ∷
   rw 1 q31 ∷
   rw 2 q1 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 1 q5 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = eqn (Toff102 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2)
  q37 : Eqn
  q37 = eqn (CS13⁻ ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2)
  q38 : Eqn
  q38 = eqn (CS13 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ []) (lem-pass-CS13-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2)

-- pass [CS13 TOFF102 CSd13 TOFF102] [iI Sd0 Sd3 CS03 X2 TOFF012 X2 iI iI iI S0 S3 CSd03 X2 TOFF012 X2]: 4 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 : ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 = derive (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ [])
  (rw 3 q36 ∷
   rw 2 q37 ∷
   rw 1 q36 ∷
   rw 0 q38 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) lem-S2

-- resp TOFF013 CS02 TOFF013 CSd02: 1 steps
lem-resp-TOFF013-CS02-TOFF013-CSd02 : ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-resp-TOFF013-CS02-TOFF013-CSd02 = derive (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw⁻ 0 q39 ∷ []) Eq.refl
