{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D752 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D008 W using (lem-pass-S0-vs-CSd03 ; lem-pass-Sd0-vs-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D010 W using (lem-pass-CS12-vs-CSd03 ; lem-pass-S0-vs-CCZ013 ; lem-pass-S0-vs-CCZ123 ; lem-pass-Sd0-vs-CCZ013)
open import Examples.Groups.Clifford+CS.Four.D.D510 W using (lem-pass-CCZ123-vs-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D513 W using (lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CS20-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D538 W using (lem-pass-CS12-vs-CCZ013 ; lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-Sd0-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D541 W using (lem-pass-X2-CK20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 ; lem-pass-X2-CK21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 ; lem-pass-X2-CKd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 ; lem-pass-X2-CKd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 ; lem-pass-X2-CS20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 ; lem-pass-X2-CS21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 ; lem-pass-X2-CSd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 ; lem-pass-X2-CSd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
open import Examples.Groups.Clifford+CS.Four.D.D596 W using (lem-pass-CK21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 ; lem-pass-CKd21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 ; lem-pass-CS21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 ; lem-pass-CSd21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2)
open import Examples.Groups.Clifford+CS.Four.D.D623 W using (lem-pass-CS20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 ; lem-pass-CSd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3)
open import Examples.Groups.Clifford+CS.Four.D.D683 W using (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3)
open import Examples.Groups.Clifford+CS.Four.D.D701 W using (lem-pass-X3-CK30-X3-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X3-CKd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X3-CS30-X3-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X3-CSd30-X3-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D702 W using (lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D712 W using (lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2)
open import Examples.Groups.Clifford+CS.Four.D.D713 W using (lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-3 ; lem-pass-CK31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 ; lem-pass-CKd31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 ; lem-pass-CS31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 ; lem-pass-CSd31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 ; lem-pass-X3-CK30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 ; lem-pass-X3-CKd30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 ; lem-pass-X3-CS30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 ; lem-pass-X3-CSd30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
open import Examples.Groups.Clifford+CS.Four.D.D714 W using (lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-2 ; lem-pass-X2-CK20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 ; lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CSd20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
open import Examples.Groups.Clifford+CS.Four.D.D730 W using (lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩-2 ; lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3 ; lem-ca-split-Gad⟨t≡1-W≡⟨2⟩-d≡SK-e≡1⟩-2 ; lem-pass-CK20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 ; lem-pass-CK31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 ; lem-pass-CKd31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 ; lem-pass-CS31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 ; lem-pass-CSd31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 ; lem-pass-X2-CKd20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 ; lem-pass-X2-CS20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 ; lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 ; lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
open import Examples.Groups.Clifford+CS.Four.D.D743 W using (lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ ; lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SSK-e≡-1⟩ ; lem-E-PPi ; lem-PP-flip-ᵖ-1 ; lem-c--⟶-ci-E ; lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2 ; lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡1⟩-2 ; lem-merge3 ; lem-pass-CKd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 ; lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 ; lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 ; lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 ; lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 ; lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 ; lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2)

private
  q1 : Eqn
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q3 : Eqn
  q3 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wn 9 W)
  q4 : Eqn
  q4 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q5 : Eqn
  q5 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q6 : Eqn
  q6 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q7 : Eqn
  q7 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q8 : Eqn
  q8 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q9 : Eqn
  q9 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q10 : Eqn
  q10 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wn 271 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q12 : Eqn
  q12 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q13 : Eqn
  q13 = eqn (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) (wn 8 W)
  q14 : Eqn
  q14 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wn 10 W)
  q15 : Eqn
  q15 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q16 : Eqn
  q16 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap))
  q17 : Eqn
  q17 = eqn (ι1 ∷ Sw23 ∷ []) (Sw23 ∷ ι1 ∷ []) (low-comm ((iI ↑)) (Swap))
  q18 : Eqn
  q18 = eqn (K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 272 W)
  q19 : Eqn
  q19 = eqn (X2 ∷ Sw23 ∷ []) (Sw23 ∷ X3 ∷ []) (wn 1609 W)
  q20 : Eqn
  q20 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 56 W)
  q21 : Eqn
  q21 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) (CS12 ∷ CCZ012 ∷ []) (lem-merge3)
  q22 : Eqn
  q22 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 43 W)
  q23 : Eqn
  q23 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q24 : Eqn
  q24 = eqn (Sw01 ∷ CX01 ∷ []) (CX10 ∷ Sw01 ∷ []) (wn 28 W)
  q25 : Eqn
  q25 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q26 : Eqn
  q26 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q27 : Eqn
  q27 = eqn (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 11 W)
  q28 : Eqn
  q28 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)

-- merge3 @1032: 393 steps
lem-merge3-at1032 : ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X2 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CCZ013 ∷ []) ⟫ʷ
lem-merge3-at1032 = derive (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X2 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X2 ∷ []) (CS03 ∷ CCZ013 ∷ [])
  (rw 10 q1 ∷
   rw⁻ 9 q2 ∷
   rw 8 q3 ∷
   re 7 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 8 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 7 q4 ∷
   rw 10 q5 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 9 q6 ∷
   rw 12 q5 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q6 ∷
   rw 14 q5 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw⁻ 13 q4 ∷
   rw⁻ 14 q7 ∷
   rw 15 q8 ∷
   rw 14 q9 ∷
   rw 13 q10 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q11 ∷
   rw 13 q12 ∷
   rw⁻ 12 q11 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 11 q13 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q11 ∷
   rw 11 q3 ∷
   rw⁻ 10 q11 ∷
   re 11 3 (CS03⁻ ∷ []) ∷
   rw 9 q13 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q11 ∷
   rw 9 q14 ∷
   rw⁻ 8 q11 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 7 q10 ∷
   rw 8 q5 ∷
   rw⁻ 9 q15 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q8 ∷
   rw⁻ 11 q16 ∷
   re 13 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q8 ∷
   rw⁻ 13 q16 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q8 ∷
   rw⁻ 15 q15 ∷
   rw⁻ 16 q17 ∷
   rw 9 q18 ∷
   re 9 8 (Toff012 ∷ []) ∷
   re 8 3 (Toff013 ∷ []) ∷
   rw 6 q14 ∷
   re 5 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 6 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q5 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q6 ∷
   rw 10 q5 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q6 ∷
   rw 12 q5 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 q4 ∷
   rw⁻ 12 q7 ∷
   rw 13 q8 ∷
   rw 12 q9 ∷
   rw 11 q10 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q11 ∷
   rw 11 q12 ∷
   rw⁻ 10 q11 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 9 q13 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q11 ∷
   rw 9 q3 ∷
   rw⁻ 8 q11 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   rw 7 q13 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q11 ∷
   rw 7 q14 ∷
   rw⁻ 6 q11 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 5 q10 ∷
   rw 6 q5 ∷
   rw⁻ 7 q15 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   rw⁻ 9 q16 ∷
   re 11 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q8 ∷
   rw⁻ 11 q16 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q8 ∷
   rw⁻ 13 q15 ∷
   rw⁻ 14 q17 ∷
   rw 7 q18 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 6 3 (Toff013 ∷ []) ∷
   rw⁻ 4 q2 ∷
   rw 3 q3 ∷
   re 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q5 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q6 ∷
   rw 7 q5 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q6 ∷
   rw 9 q5 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q4 ∷
   rw⁻ 9 q7 ∷
   rw 10 q8 ∷
   rw 9 q9 ∷
   rw 8 q10 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q11 ∷
   rw 8 q12 ∷
   rw⁻ 7 q11 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 6 q13 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q11 ∷
   rw 6 q3 ∷
   rw⁻ 5 q11 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   rw 4 q13 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q11 ∷
   rw 4 q14 ∷
   rw⁻ 3 q11 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 2 q10 ∷
   rw 3 q5 ∷
   rw⁻ 4 q15 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q8 ∷
   rw⁻ 6 q16 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q8 ∷
   rw⁻ 8 q16 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q8 ∷
   rw⁻ 10 q15 ∷
   rw⁻ 11 q17 ∷
   rw 4 q18 ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 3 3 (Toff013 ∷ []) ∷
   rw 1 q14 ∷
   re 0 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 0 q4 ∷
   rw 3 q5 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q6 ∷
   rw 5 q5 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q6 ∷
   rw 7 q5 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw⁻ 7 q7 ∷
   rw 8 q8 ∷
   rw 7 q9 ∷
   rw 6 q10 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q11 ∷
   rw 6 q12 ∷
   rw⁻ 5 q11 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 4 q13 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q11 ∷
   rw 4 q3 ∷
   rw⁻ 3 q11 ∷
   re 4 3 (CS03⁻ ∷ []) ∷
   rw 2 q13 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q11 ∷
   rw 2 q14 ∷
   rw⁻ 1 q11 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 0 q10 ∷
   rw 1 q5 ∷
   rw⁻ 2 q15 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q8 ∷
   rw⁻ 4 q16 ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q8 ∷
   rw⁻ 6 q16 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q8 ∷
   rw⁻ 8 q15 ∷
   rw⁻ 9 q17 ∷
   rw 2 q18 ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   rw 11 q5 ∷
   rw 10 q19 ∷
   rw 9 q5 ∷
   re 10 3 (CS03⁻ ∷ []) ∷
   re 8 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 8 q15 ∷
   rw 11 q5 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 10 q6 ∷
   rw 13 q5 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q6 ∷
   rw 15 q5 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw⁻ 14 q15 ∷
   rw⁻ 15 q7 ∷
   rw 16 q8 ∷
   rw 15 q7 ∷
   rw 14 q15 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q8 ∷
   rw 12 q6 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q8 ∷
   rw 10 q6 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q8 ∷
   rw 8 q15 ∷
   rw 9 q20 ∷
   re 9 8 (Toff012 ∷ []) ∷
   rw 7 q5 ∷
   re 8 3 (CS03 ∷ []) ∷
   re 6 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 6 q15 ∷
   rw 9 q5 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q6 ∷
   rw 11 q5 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q6 ∷
   rw 13 q5 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q15 ∷
   rw⁻ 13 q7 ∷
   rw 14 q8 ∷
   rw 13 q7 ∷
   rw 12 q15 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q8 ∷
   rw 10 q6 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q8 ∷
   rw 8 q6 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q8 ∷
   rw 6 q15 ∷
   rw 7 q20 ∷
   re 7 8 (Toff012 ∷ []) ∷
   rw 5 q19 ∷
   rw 4 q5 ∷
   re 5 3 (CS03⁻ ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q15 ∷
   rw 6 q5 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q6 ∷
   rw 8 q5 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q6 ∷
   rw 10 q5 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q15 ∷
   rw⁻ 10 q7 ∷
   rw 11 q8 ∷
   rw 10 q7 ∷
   rw 9 q15 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q8 ∷
   rw 7 q6 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   rw 5 q6 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q8 ∷
   rw 3 q15 ∷
   rw 4 q20 ∷
   re 4 8 (Toff012 ∷ []) ∷
   rw 2 q5 ∷
   re 3 3 (CS03 ∷ []) ∷
   re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q15 ∷
   rw 4 q5 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q6 ∷
   rw 6 q5 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q6 ∷
   rw 8 q5 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q15 ∷
   rw⁻ 8 q7 ∷
   rw 9 q8 ∷
   rw 8 q7 ∷
   rw 7 q15 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   rw 5 q6 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q8 ∷
   rw 3 q6 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q8 ∷
   rw 1 q15 ∷
   rw 2 q20 ∷
   re 2 8 (Toff012 ∷ []) ∷
   rw 2 q21 ∷
   rw 3 q5 ∷
   re 1 3 (CS13 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q5 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q6 ∷
   rw 6 q5 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q6 ∷
   rw 8 q5 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 2 q5 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q8 ∷
   rw⁻ 4 q6 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q8 ∷
   rw⁻ 6 q6 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q8 ∷
   rw 3 q22 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   re 2 3 (CCZ013 ∷ []) ∷
   rw 3 q8 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 q11 ∷
   rw 1 q23 ∷
   rw 2 q11 ∷
   re 0 3 (CS03 ∷ []) ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q5 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q6 ∷
   rw 6 q5 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q6 ∷
   rw 8 q5 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q8 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q11 ∷
   rw 2 q23 ∷
   rw 3 q11 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q24 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q11 ∷
   rw 4 q25 ∷
   rw 5 q11 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 4 q24 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q11 ∷
   rw 6 q26 ∷
   rw 7 q11 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 1 q5 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q8 ∷
   rw⁻ 3 q16 ∷
   re 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q8 ∷
   rw⁻ 5 q16 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q8 ∷
   rw 2 q27 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw 2 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = eqn [] (CS12 ∷ CS12⁻ ∷ []) (wn 2052 W)
  q30 : Eqn
  q30 = eqn [] (CCZ012 ∷ CCZ012 ∷ []) (wn 4 W)
  q31 : Eqn
  q31 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) (CS12 ∷ CCZ012 ∷ []) lem-merge3
  q32 : Eqn
  q32 = eqn (Toff012 ∷ Toff012 ∷ []) [] (wn 227 W)
  q33 : Eqn
  q33 = eqn (CS02⁻ ∷ CS02 ∷ []) [] (wn 1358 W)
  q34 : Eqn
  q34 = eqn (CS02 ∷ CS02⁻ ∷ []) [] (wn 1342 W)
  q35 : Eqn
  q35 = eqn (X3 ∷ X3 ∷ []) [] (wn 390 W)

-- merge3 ^-1: 37 steps
lem-merge3-ᵖ-1 : ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-merge3-ᵖ-1 = derive (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CCZ012 ∷ CS12⁻ ∷ [])
  (rw 10 q29 ∷
   rw 11 q30 ∷
   rw⁻ 10 q31 ∷
   rw 9 q32 ∷
   rw 10 q5 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q8 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q8 ∷
   rw 9 q33 ∷
   rw 8 q8 ∷
   rw 7 q32 ∷
   rw 8 q5 ∷
   re 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q8 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   rw 7 q34 ∷
   rw 6 q8 ∷
   rw 5 q35 ∷
   rw 4 q32 ∷
   rw 5 q5 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q8 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q8 ∷
   rw 4 q33 ∷
   rw 3 q8 ∷
   rw 2 q32 ∷
   rw 3 q5 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q8 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q8 ∷
   rw 2 q34 ∷
   rw 1 q8 ∷
   rw 0 q35 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = eqn (CS12 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS12 ∷ []) (lem-pass-CS12-vs-CCZ013)
  q37 : Eqn
  q37 = eqn (CS12 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS12 ∷ []) (lem-pass-CS12-vs-CSd03)
  q38 : Eqn
  q38 = eqn (CS12 ∷ CS12⁻ ∷ []) [] (wn 1455 W)
  q39 : Eqn
  q39 = eqn (S0⁻ ∷ CCZ013 ∷ []) (CCZ013 ∷ S0⁻ ∷ []) (lem-pass-Sd0-vs-CCZ013)
  q40 : Eqn
  q40 = eqn (S0⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ S0⁻ ∷ []) (lem-pass-Sd0-vs-CSd03)
  q41 : Eqn
  q41 = eqn (S0⁻ ∷ S0 ∷ []) [] (wn 2487 W)
  q42 : Eqn
  q42 = eqn [] (Toff012 ∷ Toff012 ∷ []) (wn 45 W)
  q43 : Eqn
  q43 = eqn (Toff012 ∷ CCZ013 ∷ Toff012 ∷ []) (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz)
  q44 : Eqn
  q44 = eqn [] (CS02⁻ ∷ CS02 ∷ []) (wn 231 W)
  q45 : Eqn
  q45 = eqn (S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ []) lem-pass-Sd0-vs-CS03-TOFF012-CSd03-TOFF012
  q46 : Eqn
  q46 = eqn (S0 ∷ CCZ013 ∷ []) (CCZ013 ∷ S0 ∷ []) (lem-pass-S0-vs-CCZ013)
  q47 : Eqn
  q47 = eqn (S0 ∷ CCZ123 ∷ []) (CCZ123 ∷ S0 ∷ []) (lem-pass-S0-vs-CCZ123)
  q48 : Eqn
  q48 = eqn (S0 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ S0 ∷ []) (lem-pass-S0-vs-CSd03)
  q49 : Eqn
  q49 = eqn (S0 ∷ S0⁻ ∷ []) [] (wn 1728 W)
  q50 : Eqn
  q50 = eqn (CCZ123 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CSd03)
  q51 : Eqn
  q51 = eqn (CCZ123 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-E-PPi)

-- CI conj: 22 steps
lem-CI-conj : ⟪ (S0 ∷ Toff012 ∷ S0⁻ ∷ CS12 ∷ CCZ013 ∷ CS03⁻ ∷ CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-CI-conj = derive (S0 ∷ Toff012 ∷ S0⁻ ∷ CS12 ∷ CCZ013 ∷ CS03⁻ ∷ CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (CCZ013 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw 3 q36 ∷
   rw 4 q37 ∷
   rw 5 q38 ∷
   rw 2 q39 ∷
   rw 3 q40 ∷
   rw 4 q41 ∷
   rw 3 q42 ∷
   rw 1 q43 ∷
   rw 3 q5 ∷
   rw 4 q44 ∷
   rw 5 q5 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 6 q5 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q8 ∷
   rw⁻ 4 q45 ∷
   rw 0 q46 ∷
   rw 1 q47 ∷
   rw 2 q48 ∷
   rw 3 q49 ∷
   rw 1 q50 ∷
   rw 2 q51 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = eqn (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3)
  q53 : Eqn
  q53 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-TOFF102-CS13-TOFF102-CSd13)
  q54 : Eqn
  q54 = eqn (X3 ∷ CK30⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-TOFF102-CS13-TOFF102-CSd13)
  q55 : Eqn
  q55 = eqn (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF102-CS13-TOFF102-CSd13)
  q56 : Eqn
  q56 = eqn (X3 ∷ CK30 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-TOFF102-CS13-TOFF102-CSd13)
  q57 : Eqn
  q57 = eqn (X3 ∷ CS03 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-TOFF102-CS13-TOFF102-CSd13)
  q58 : Eqn
  q58 = eqn (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3

-- pass [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3] [TOFF102 CS13 TOFF102 CSd13]: 7 steps
lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ [])
  (rw 0 q52 ∷
   rw 15 q53 ∷
   rw 12 q54 ∷
   rw 6 q55 ∷
   rw 3 q56 ∷
   rw 0 q57 ∷
   rw⁻ 4 q58 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = eqn [] (X2 ∷ X2 ∷ []) (wn 871 W)
  q60 : Eqn
  q60 = eqn [] (CS13 ∷ CS13⁻ ∷ []) (wn 1376 W)
  q61 : Eqn
  q61 = eqn [] (Toff102 ∷ Toff102 ∷ []) (wn 1377 W)
  q62 : Eqn
  q62 = eqn [] (CS13⁻ ∷ CS13 ∷ []) (wn 1378 W)
  q63 : Eqn
  q63 = eqn (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2
  q64 : Eqn
  q64 = eqn (X2 ∷ X2 ∷ []) [] (wn 389 W)
  q65 : Eqn
  q65 = eqn (CS13⁻ ∷ CS13 ∷ []) [] (wn 1379 W)
  q66 : Eqn
  q66 = eqn (Toff102 ∷ Toff102 ∷ []) [] (wn 1380 W)
  q67 : Eqn
  q67 = eqn (CS13 ∷ CS13⁻ ∷ []) [] (wn 1381 W)

-- pass [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3] [X2 CS13 TOFF102 CSd13 TOFF102 X2]: 13 steps
lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-X2-CS13-TOFF102-CSd13-TOFF102-X2 : ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-X2-CS13-TOFF102-CSd13-TOFF102-X2 = derive (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ [])
  (rw 0 q59 ∷
   rw 1 q60 ∷
   rw 2 q61 ∷
   rw 3 q62 ∷
   rw 4 q61 ∷
   rw 5 q59 ∷
   rw⁻ 6 q63 ∷
   rw 21 q64 ∷
   rw 20 q65 ∷
   rw 19 q66 ∷
   rw 18 q67 ∷
   rw 17 q66 ∷
   rw 16 q64 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CCZ123 ∷ []) (lem-c--⟶-ci-E)
  q69 : Eqn
  q69 = eqn (K0⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) (CCZ))
  q70 : Eqn
  q70 = eqn (S0⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) (CCZ))

-- Ri = R E: 3 steps
lem-Ri-≡-R-E : ⟪ (S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ CCZ123 ∷ []) ⟫ʷ
lem-Ri-≡-R-E = derive (S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ CCZ123 ∷ [])
  (rw 2 q68 ∷
   rw⁻ 6 q69 ∷
   rw⁻ 7 q70 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = eqn [] (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) (wn 2488 W)
  q72 : Eqn
  q72 = eqn [] (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (wn 2489 W)
  q73 : Eqn
  q73 = eqn (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) (X0 ∷ S0 ∷ S0 ∷ ι ∷ []) (wn 2490 W)
  q74 : Eqn
  q74 = eqn (ι ∷ CS02 ∷ []) (CS02 ∷ ι ∷ []) (wn 1739 W)
  q75 : Eqn
  q75 = eqn (ι ∷ Toff012 ∷ []) (Toff012 ∷ ι ∷ []) (wn 1738 W)
  q76 : Eqn
  q76 = eqn (ι ∷ CS02⁻ ∷ []) (CS02⁻ ∷ ι ∷ []) (wn 1740 W)
  q77 : Eqn
  q77 = eqn (S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ []) (lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012)
  q78 : Eqn
  q78 = eqn (S0 ∷ S0 ∷ ι ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (X0 ∷ []) (wn 2491 W)
  q79 : Eqn
  q79 = eqn (X0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X0 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-PP-flip-ᵖ-1)

-- spell Gad(t=0, W=(), d=1, e=-1) -> Gad(t=0, W=(), d=SSKSSK, e=1): 27 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SSKSSK-e≡1⟩ : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SSKSSK-e≡1⟩ = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ [])
  (rw 0 q71 ∷
   rw 16 q72 ∷
   rw 6 q73 ∷
   rw 11 q5 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q8 ∷
   rw 9 q7 ∷
   rw 10 q74 ∷
   rw 11 q5 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q7 ∷
   rw 11 q8 ∷
   rw 10 q75 ∷
   rw 13 q5 ∷
   re 12 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q8 ∷
   rw 11 q7 ∷
   rw 12 q76 ∷
   rw 13 q5 ∷
   re 11 3 (CS03⁻ ∷ []) ∷
   rw⁻ 12 q7 ∷
   rw 13 q8 ∷
   rw 12 q75 ∷
   rw 8 q77 ∷
   rw 7 q77 ∷
   rw 11 q78 ∷
   rw 6 q79 ∷ []) Eq.refl

private
  q80 : Eqn
  q80 = eqn (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) (S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) (wn 2492 W)
  q81 : Eqn
  q81 = eqn (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (wn 2493 W)

-- spell Gad(t=0, W=(), d=SdKdSS, e=-1) -> Gad(t=0, W=(), d=SK, e=1): 27 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ : ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ = derive (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ [])
  (rw 0 q80 ∷
   rw 12 q81 ∷
   rw 2 q73 ∷
   rw 7 q5 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   rw 5 q7 ∷
   rw 6 q74 ∷
   rw 7 q5 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q7 ∷
   rw 7 q8 ∷
   rw 6 q75 ∷
   rw 9 q5 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q8 ∷
   rw 7 q7 ∷
   rw 8 q76 ∷
   rw 9 q5 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw⁻ 8 q7 ∷
   rw 9 q8 ∷
   rw 8 q75 ∷
   rw 4 q77 ∷
   rw 3 q77 ∷
   rw 7 q78 ∷
   rw 2 q79 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q83 : Eqn
  q83 = eqn (X3 ∷ CK30⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q84 : Eqn
  q84 = eqn (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q85 : Eqn
  q85 = eqn (X3 ∷ CK30 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q86 : Eqn
  q86 = eqn (X3 ∷ CS03 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)

-- pass [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 7 steps
lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ [])
  (rw 0 q52 ∷
   rw 15 q82 ∷
   rw 12 q83 ∷
   rw 6 q84 ∷
   rw 3 q85 ∷
   rw 0 q86 ∷
   rw⁻ 8 q58 ∷ []) Eq.refl

private
  q87 : Eqn
  q87 = eqn (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (CS13 ∷ CK31 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ []) (lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-3)
  q88 : Eqn
  q88 = eqn (CS13 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS13 ∷ []) lem-pass-CS31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q89 : Eqn
  q89 = eqn (CK31 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK31 ∷ []) lem-pass-CK31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q90 : Eqn
  q90 = eqn (CK31⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK31⁻ ∷ []) lem-pass-CKd31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q91 : Eqn
  q91 = eqn (CS13⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS13⁻ ∷ []) lem-pass-CSd31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q92 : Eqn
  q92 = eqn (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (CS13 ∷ CK31 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ []) lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-3

-- pass [X3 CS03 TOFF012 CSd03 TOFF012 X3] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 7 steps
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ [])
  (rw 6 q87 ∷
   rw⁻ 0 q88 ∷
   rw⁻ 1 q89 ∷
   rw 2 q55 ∷
   rw⁻ 6 q90 ∷
   rw⁻ 7 q91 ∷
   rw⁻ 0 q92 ∷ []) Eq.refl

private
  q93 : Eqn
  q93 = eqn (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩-2)
  q94 : Eqn
  q94 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q95 : Eqn
  q95 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q96 : Eqn
  q96 = eqn (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q97 : Eqn
  q97 = eqn (X2 ∷ CK20 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q98 : Eqn
  q98 = eqn (X2 ∷ CS02 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q99 : Eqn
  q99 = eqn (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩-2

-- pass [X2 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 7 steps
lem-pass-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ [])
  (rw 0 q93 ∷
   rw 15 q94 ∷
   rw 12 q95 ∷
   rw 6 q96 ∷
   rw 3 q97 ∷
   rw 0 q98 ∷
   rw⁻ 8 q99 ∷ []) Eq.refl

private
  q100 : Eqn
  q100 = eqn (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (CS02 ∷ CK20 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CK20⁻ ∷ CS02⁻ ∷ []) (lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2)
  q101 : Eqn
  q101 = eqn (CS02 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS02 ∷ []) lem-pass-CS20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q102 : Eqn
  q102 = eqn (CK20 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK20 ∷ []) lem-pass-CK20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q103 : Eqn
  q103 = eqn (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012)
  q104 : Eqn
  q104 = eqn (CK20⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK20⁻ ∷ []) lem-pass-CKd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q105 : Eqn
  q105 = eqn (CS02⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS02⁻ ∷ []) lem-pass-CSd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q106 : Eqn
  q106 = eqn (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (CS02 ∷ CK20 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CK20⁻ ∷ CS02⁻ ∷ []) lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2

-- pass [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 7 steps
lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ [])
  (rw 8 q100 ∷
   rw⁻ 0 q101 ∷
   rw⁻ 1 q102 ∷
   rw 2 q103 ∷
   rw⁻ 6 q104 ∷
   rw⁻ 7 q105 ∷
   rw⁻ 0 q106 ∷ []) Eq.refl

private
  q107 : Eqn
  q107 = eqn (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2)
  q108 : Eqn
  q108 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1)
  q109 : Eqn
  q109 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1)
  q110 : Eqn
  q110 = eqn (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1)
  q111 : Eqn
  q111 = eqn (X2 ∷ CK20 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1)
  q112 : Eqn
  q112 = eqn (X2 ∷ CS02 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1)
  q113 : Eqn
  q113 = eqn (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2

-- pass [X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2 X3] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 7 steps
lem-pass-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ [])
  (rw 0 q107 ∷
   rw 17 q108 ∷
   rw 14 q109 ∷
   rw 6 q110 ∷
   rw 3 q111 ∷
   rw 0 q112 ∷
   rw⁻ 8 q113 ∷ []) Eq.refl

private
  q114 : Eqn
  q114 = eqn (X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡1⟩-2)
  q115 : Eqn
  q115 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q116 : Eqn
  q116 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q117 : Eqn
  q117 = eqn (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) (lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q118 : Eqn
  q118 = eqn (X2 ∷ CK21 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q119 : Eqn
  q119 = eqn (X2 ∷ CS12 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q120 : Eqn
  q120 = eqn (X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡1⟩-2

-- pass [X2 X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2 X3] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 7 steps
lem-pass-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ [])
  (rw 0 q114 ∷
   rw 17 q115 ∷
   rw 14 q116 ∷
   rw 6 q117 ∷
   rw 3 q118 ∷
   rw 0 q119 ∷
   rw⁻ 8 q120 ∷ []) Eq.refl

private
  q121 : Eqn
  q121 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q122 : Eqn
  q122 = eqn (K0 ∷ X3 ∷ []) (X3 ∷ K0 ∷ []) (low₁-comm (K) ((X ↑ ↑)))
  q123 : Eqn
  q123 = eqn (K0⁻ ∷ S0⁻ ∷ S0 ∷ K0 ∷ []) [] (wn 2494 W)
  q124 : Eqn
  q124 = eqn (S0⁻ ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑ ↑)))
  q125 : Eqn
  q125 = eqn (K0⁻ ∷ X3 ∷ []) (X3 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((X ↑ ↑)))

-- merge3 Gad(t=0, W=(), d=SK, e=1): 6 steps
lem-merge3-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ : ⟪ (S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS12 ∷ CCZ012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-merge3-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ = derive (S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (S0 ∷ K0 ∷ CS12 ∷ CCZ012 ∷ K0⁻ ∷ S0⁻ ∷ [])
  (rw⁻ 8 q121 ∷
   rw⁻ 9 q122 ∷
   rw 6 q123 ∷
   rw 12 q124 ∷
   rw 11 q125 ∷
   rw 2 q21 ∷ []) Eq.refl

private
  q126 : Eqn
  q126 = eqn (CS01 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ CS01 ∷ []) (lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩)
  q127 : Eqn
  q127 = eqn (CS01 ∷ CS01⁻ ∷ []) [] (wn 1698 W)
  q128 : Eqn
  q128 = eqn (CS01 ∷ S0 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0 ∷ CS01 ∷ []) (lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SSK-e≡-1⟩)

-- CAw1 SS Gad(t=0, W=(), d=SK, e=-1): 4 steps
lem-CAw1-SS-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ : ⟪ (CS01 ∷ CS01 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ
lem-CAw1-SS-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ = derive (CS01 ∷ CS01 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ CS01⁻ ∷ CS01⁻ ∷ []) (S0⁻ ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0 ∷ [])
  (rw 1 q126 ∷
   rw 11 q127 ∷
   rw 0 q128 ∷
   rw 8 q127 ∷ []) Eq.refl

private
  q129 : Eqn
  q129 = eqn (S0⁻ ∷ K0 ∷ []) (S0 ∷ K0 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (wn 2495 W)
  q130 : Eqn
  q130 = eqn (K0⁻ ∷ S0 ∷ []) (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (wn 2496 W)
  q131 : Eqn
  q131 = eqn (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (X0 ∷ []) (wn 2497 W)
  q132 : Eqn
  q132 = eqn (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (X0 ∷ []) (wn 2498 W)

-- spell Gad(t=0, W=(), d=SdK, e=-1) -> Gad(t=0, W=(), d=SK, e=1): 5 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ : ⟪ (S0⁻ ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ = derive (S0⁻ ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0 ∷ []) (S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ [])
  (rw 0 q129 ∷
   rw 10 q130 ∷
   rw 2 q131 ∷
   rw 7 q132 ∷
   rw 2 q79 ∷ []) Eq.refl

private
  q133 : Eqn
  q133 = eqn (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw⁻ 0 q133 ∷ []) Eq.refl

private
  q134 : Eqn
  q134 = eqn (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (CS12 ∷ CK21 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ []) (lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-2)
  q135 : Eqn
  q135 = eqn (CS12⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CS12⁻ ∷ []) (lem-pass-CSd21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2)
  q136 : Eqn
  q136 = eqn (CK21⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CK21⁻ ∷ []) (lem-pass-CKd21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2)
  q137 : Eqn
  q137 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2)
  q138 : Eqn
  q138 = eqn (CK21 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CK21 ∷ []) (lem-pass-CK21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2)
  q139 : Eqn
  q139 = eqn (CS12 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CS12 ∷ []) (lem-pass-CS21-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2)
  q140 : Eqn
  q140 = eqn (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (CS12 ∷ CK21 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ []) lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-2

-- pass [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1] [X2 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2]: 7 steps
lem-pass-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 : ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ
lem-pass-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 = derive (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ [])
  (rw 0 q134 ∷
   rw 7 q135 ∷
   rw 6 q136 ∷
   rw 2 q137 ∷
   rw 1 q138 ∷
   rw 0 q139 ∷
   rw⁻ 10 q140 ∷ []) Eq.refl

private
  q141 : Eqn
  q141 = eqn (X2 ∷ CS02 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) lem-pass-X2-CS20-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q142 : Eqn
  q142 = eqn (X2 ∷ CK20 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q143 : Eqn
  q143 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3)
  q144 : Eqn
  q144 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q145 : Eqn
  q145 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2 X3]: 7 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw 4 q107 ∷
   rw⁻ 0 q141 ∷
   rw⁻ 3 q142 ∷
   rw 6 q143 ∷
   rw⁻ 14 q144 ∷
   rw⁻ 17 q145 ∷
   rw⁻ 0 q113 ∷ []) Eq.refl

private
  q146 : Eqn
  q146 = eqn (CS13⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS13⁻ ∷ []) (lem-pass-CSd31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3)
  q147 : Eqn
  q147 = eqn (CK31⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CK31⁻ ∷ []) (lem-pass-CKd31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3)
  q148 : Eqn
  q148 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3)
  q149 : Eqn
  q149 = eqn (CK31 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CK31 ∷ []) (lem-pass-CK31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3)
  q150 : Eqn
  q150 = eqn (CS13 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS13 ∷ []) (lem-pass-CS31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3)

-- pass [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1] [X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X3]: 7 steps
lem-pass-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ
lem-pass-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = derive (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ [])
  (rw 0 q87 ∷
   rw 7 q146 ∷
   rw 6 q147 ∷
   rw 2 q148 ∷
   rw 1 q149 ∷
   rw 0 q150 ∷
   rw⁻ 10 q92 ∷ []) Eq.refl

private
  q151 : Eqn
  q151 = eqn (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-ca-split-Gad⟨t≡1-W≡⟨2⟩-d≡SK-e≡1⟩-2)
  q152 : Eqn
  q152 = eqn (X2 ∷ CS12 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q153 : Eqn
  q153 = eqn (X2 ∷ CK21 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q154 : Eqn
  q154 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2)
  q155 : Eqn
  q155 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q156 : Eqn
  q156 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q157 : Eqn
  q157 = eqn (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) lem-ca-split-Gad⟨t≡1-W≡⟨2⟩-d≡SK-e≡1⟩-2

-- pass [TOFF102 CS13 TOFF102 CSd13] [X2 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2]: 7 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ []) (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw 4 q151 ∷
   rw⁻ 0 q152 ∷
   rw⁻ 3 q153 ∷
   rw 6 q154 ∷
   rw⁻ 12 q155 ∷
   rw⁻ 15 q156 ∷
   rw⁻ 0 q157 ∷ []) Eq.refl
