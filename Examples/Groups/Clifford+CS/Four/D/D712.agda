{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D712 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D539 W using (lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D623 W using (lem-pass-CCZ013-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D701 W using (lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 ; lem-pass-CSd03-vs-TOFF012-CS03-TOFF012-CSd03 ; lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF103-X3-CS12-X3-TOFF103-X3-CSd12 ; lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X3-CK30-X3-vs-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0 ; lem-pass-X3-CK30-X3-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X3-CKd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X3-CS30-X3-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X3-CSd30-X3-vs-K0-TOFF012-CS03-TOFF012-CSd03-Kd0 ; lem-pass-X3-CSd30-X3-vs-Sd0-Kd0-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-K0-S0 ; lem-pass-X3-CSd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF012-CS03-TOFF012-CSd03)

private
  q1 : Eqn
  q1 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q2 : Eqn
  q2 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q3 : Eqn
  q3 = eqn (CS02 ∷ []) (S0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 1815 W)
  q4 : Eqn
  q4 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q5 : Eqn
  q5 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q6 : Eqn
  q6 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ []) (K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-K0-TOFF012-CS03-TOFF012-CSd03-Kd0)
  q7 : Eqn
  q7 = eqn (S0 ∷ K0 ∷ []) (S0 ∷ K0 ∷ []) (wn 2093 W)
  q8 : Eqn
  q8 = eqn (K0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ S0 ∷ []) (wn 2094 W)
  q9 : Eqn
  q9 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q10 : Eqn
  q10 = eqn (S0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (CS02 ∷ []) (wn 1816 W)

-- CA CS30 Gad(t=0, W=(), d=K, e=1): 23 steps
lem-CA-CS30-Gad⟨t≡0-W≡⟨⟩-d≡K-e≡1⟩ : ⟪ (CS03 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ CS03 ∷ []) ⟫ʷ
lem-CA-CS30-Gad⟨t≡0-W≡⟨⟩-d≡K-e≡1⟩ = derive (CS03 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ []) (S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ CS03 ∷ [])
  (rw 1 q1 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q2 ∷
   rw 1 q3 ∷
   rw⁻ 0 q4 ∷
   rw 1 q5 ∷
   rw 4 q1 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q5 ∷
   rw 4 q2 ∷
   rw 1 q6 ∷
   rw 0 q7 ∷
   rw 6 q8 ∷
   rw 12 q1 ∷
   rw 11 q9 ∷
   re 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q2 ∷
   rw 9 q9 ∷
   rw 8 q4 ∷
   rw 9 q10 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q2 ∷ []) Eq.refl

private
  q11 : Eqn
  q11 = eqn (CK20⁻ ∷ []) (K0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 1709 W)
  q12 : Eqn
  q12 = eqn (K0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑)))
  q13 : Eqn
  q13 = eqn (X3 ∷ CK30 ∷ X3 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0)
  q14 : Eqn
  q14 = eqn (K0⁻ ∷ S0 ∷ K0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (wn 2095 W)
  q15 : Eqn
  q15 = eqn (K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ S0 ∷ K0⁻ ∷ []) (wn 2096 W)
  q16 : Eqn
  q16 = eqn (K0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (CK20⁻ ∷ []) (wn 1711 W)

-- CA CKd30 Gad(t=0, W=(), d=SK, e=1): 23 steps
lem-CA-CKd30-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ : ⟪ (CK30⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ CK30⁻ ∷ []) ⟫ʷ
lem-CA-CKd30-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ = derive (CK30⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ CK30⁻ ∷ [])
  (rw 1 q1 ∷
   re 0 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q2 ∷
   rw 1 q11 ∷
   rw⁻ 0 q12 ∷
   rw 1 q5 ∷
   rw 4 q1 ∷
   re 2 3 (CK30 ∷ []) ∷
   rw 3 q5 ∷
   rw 4 q2 ∷
   rw 1 q13 ∷
   rw 0 q14 ∷
   rw 7 q15 ∷
   rw 14 q1 ∷
   rw 13 q9 ∷
   re 12 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 14 q2 ∷
   rw 11 q9 ∷
   rw 10 q12 ∷
   rw 11 q16 ∷
   rw 12 q1 ∷
   re 10 3 (CK30⁻ ∷ []) ∷
   rw 11 q2 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-Sd0-Kd0-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-K0-S0)
  q18 : Eqn
  q18 = eqn (S0 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ []) (wn 2097 W)
  q19 : Eqn
  q19 = eqn (S0 ∷ K0 ∷ S0 ∷ []) (S0 ∷ K0 ∷ S0 ∷ []) (wn 2098 W)

-- CA CS30 Gad(t=0, W=(), d=SdKdSd, e=1): 23 steps
lem-CA-CS30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩ : ⟪ (CS03 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ []) ⟫ʷ
lem-CA-CS30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩ = derive (CS03 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) (K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ [])
  (rw 1 q1 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q2 ∷
   rw 1 q3 ∷
   rw⁻ 0 q4 ∷
   rw 1 q5 ∷
   rw 4 q1 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q5 ∷
   rw 4 q2 ∷
   rw 1 q17 ∷
   rw 0 q18 ∷
   rw 6 q19 ∷
   rw 12 q1 ∷
   rw 11 q9 ∷
   re 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q2 ∷
   rw 9 q9 ∷
   rw 8 q4 ∷
   rw 9 q10 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q2 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = eqn [] (Toff012 ∷ Toff012 ∷ []) (wn 45 W)
  q21 : Eqn
  q21 = eqn [] (CS02 ∷ CS02⁻ ∷ []) (wn 1357 W)
  q22 : Eqn
  q22 = eqn [] (CS02⁻ ∷ CS02 ∷ []) (wn 231 W)
  q23 : Eqn
  q23 = eqn [] (X3 ∷ X3 ∷ []) (wn 225 W)
  q24 : Eqn
  q24 = eqn (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q25 : Eqn
  q25 = eqn (X3 ∷ X3 ∷ []) [] (wn 390 W)
  q26 : Eqn
  q26 = eqn (Toff012 ∷ Toff012 ∷ []) [] (wn 227 W)
  q27 : Eqn
  q27 = eqn (CS02⁻ ∷ CS02 ∷ []) [] (wn 1358 W)
  q28 : Eqn
  q28 = eqn (CS02 ∷ CS02⁻ ∷ []) [] (wn 1342 W)

-- pass [X3 TOFF012 CS03 TOFF012 CSd03 X3] [TOFF012 CS03 TOFF012 CSd03] ^-1: 69 steps
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF012-CS03-TOFF012-CSd03-ᵖ-1 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF012-CS03-TOFF012-CSd03-ᵖ-1 = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  (rw 10 q20 ∷
   rw 11 q1 ∷
   rw 12 q21 ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 14 q1 ∷
   re 12 3 (CS03⁻ ∷ []) ∷
   rw 13 q2 ∷
   rw 12 q20 ∷
   rw 13 q1 ∷
   rw 14 q22 ∷
   rw 15 q1 ∷
   re 13 3 (CS03⁻ ∷ []) ∷
   rw 16 q1 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 15 q2 ∷
   rw 14 q23 ∷
   rw 15 q20 ∷
   rw 16 q1 ∷
   rw 17 q21 ∷
   rw 18 q1 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 19 q1 ∷
   re 17 3 (CS03⁻ ∷ []) ∷
   rw 18 q2 ∷
   rw 17 q20 ∷
   rw 18 q1 ∷
   rw 19 q22 ∷
   rw 20 q1 ∷
   re 18 3 (CS03⁻ ∷ []) ∷
   rw 21 q1 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 20 q2 ∷
   rw 19 q23 ∷
   rw⁻ 10 q24 ∷
   rw 9 q25 ∷
   rw 8 q26 ∷
   rw 9 q1 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   re 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q2 ∷
   rw 8 q27 ∷
   rw 7 q2 ∷
   rw 6 q26 ∷
   rw 7 q1 ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   rw 6 q28 ∷
   rw 5 q2 ∷
   rw 4 q25 ∷
   rw 3 q26 ∷
   rw 4 q1 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q2 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q2 ∷
   rw 3 q27 ∷
   rw 2 q2 ∷
   rw 1 q26 ∷
   rw 2 q1 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q2 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q2 ∷
   rw 1 q28 ∷
   rw 0 q2 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = eqn (CS02 ∷ X2 ∷ []) (X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 1462 W)
  q30 : Eqn
  q30 = eqn (X3 ∷ CS03 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
  q31 : Eqn
  q31 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ []) (X2 ∷ CS02 ∷ []) (wn 1463 W)

-- pass [CS30] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 23 steps
lem-pass-CS30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (CS03 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (CS03 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ [])
  (rw 2 q1 ∷
   rw 1 q9 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q2 ∷
   rw 1 q29 ∷
   rw 0 q5 ∷
   rw 1 q5 ∷
   rw 4 q1 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q5 ∷
   rw 4 q2 ∷
   rw 1 q30 ∷
   rw 9 q1 ∷
   rw 8 q9 ∷
   rw 7 q9 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   rw 5 q9 ∷
   rw 6 q31 ∷
   rw 5 q5 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q2 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q33 : Eqn
  q33 = eqn (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3)

-- pass [X3 CS03 TOFF012 CSd03 TOFF012 X3] [X2 TOFF102 CS13 TOFF102 CSd13 X2]: 5 steps
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = derive (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ [])
  (rw⁻ 5 q32 ∷
   rw 12 q23 ∷
   rw 1 q33 ∷
   rw⁻ 0 q32 ∷
   rw 1 q25 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q35 : Eqn
  q35 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q36 : Eqn
  q36 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q37 : Eqn
  q37 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q38 : Eqn
  q38 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q39 : Eqn
  q39 = eqn (X3 ∷ CS13⁻ ∷ X3 ∷ X2 ∷ []) (X2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (wn 2063 W)
  q40 : Eqn
  q40 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q41 : Eqn
  q41 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q42 : Eqn
  q42 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 1482 W)
  q43 : Eqn
  q43 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-TOFF102-CS13-TOFF102-CSd13)

-- pass [X3 CSd30 X3] [X2 TOFF102 CS13 TOFF102 CSd13 X2]: 61 steps
lem-pass-X3-CSd30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 4 q34 ∷
   rw⁻ 3 q35 ∷
   rw⁻ 2 q36 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q37 ∷
   rw 2 q38 ∷
   rw⁻ 1 q37 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 0 q36 ∷
   rw 1 q39 ∷
   rw 0 q35 ∷
   rw 1 q36 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q37 ∷
   rw 3 q40 ∷
   rw 4 q37 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q36 ∷
   rw 4 q41 ∷
   rw 4 q1 ∷
   rw 3 q9 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q2 ∷
   rw 1 q9 ∷
   rw 2 q42 ∷
   rw 1 q5 ∷
   rw 4 q1 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q5 ∷
   rw 4 q2 ∷
   rw 1 q43 ∷
   rw 8 q1 ∷
   rw 7 q9 ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   rw 5 q9 ∷
   rw 6 q42 ∷
   rw 5 q5 ∷
   rw 8 q1 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   rw 7 q5 ∷
   rw 8 q2 ∷
   rw 9 q34 ∷
   rw⁻ 8 q35 ∷
   rw⁻ 7 q36 ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q37 ∷
   rw 7 q38 ∷
   rw⁻ 6 q37 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q36 ∷
   rw 6 q39 ∷
   rw 5 q35 ∷
   rw 6 q36 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q37 ∷
   rw 8 q40 ∷
   rw 9 q37 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw 8 q36 ∷
   rw 9 q41 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = eqn (CK20⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK21⁻ ∷ []) (wn 137 W)
  q45 : Eqn
  q45 = eqn (X3 ∷ CK31⁻ ∷ X3 ∷ X2 ∷ []) (X2 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (wn 1677 W)
  q46 : Eqn
  q46 = eqn (Sw01 ∷ CK21⁻ ∷ []) (CK20⁻ ∷ Sw01 ∷ []) (wn 139 W)
  q47 : Eqn
  q47 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ []) (X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1485 W)
  q48 : Eqn
  q48 = eqn (X3 ∷ CK30⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-TOFF102-CS13-TOFF102-CSd13)

-- pass [X3 CKd30 X3] [X2 TOFF102 CS13 TOFF102 CSd13 X2]: 61 steps
lem-pass-X3-CKd30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = derive (X3 ∷ CK30⁻ ∷ X3 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  (rw 4 q34 ∷
   rw⁻ 3 q35 ∷
   rw⁻ 2 q36 ∷
   re 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q37 ∷
   rw 2 q44 ∷
   rw⁻ 1 q37 ∷
   re 2 3 (CK31⁻ ∷ []) ∷
   rw⁻ 0 q36 ∷
   rw 1 q45 ∷
   rw 0 q35 ∷
   rw 1 q36 ∷
   re 3 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q37 ∷
   rw 3 q46 ∷
   rw 4 q37 ∷
   re 2 3 (CK30⁻ ∷ []) ∷
   rw 3 q36 ∷
   rw 4 q41 ∷
   rw 4 q1 ∷
   rw 3 q9 ∷
   re 2 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q2 ∷
   rw 1 q9 ∷
   rw 2 q47 ∷
   rw 1 q5 ∷
   rw 4 q1 ∷
   re 2 3 (CK30⁻ ∷ []) ∷
   rw 3 q5 ∷
   rw 4 q2 ∷
   rw 1 q48 ∷
   rw 8 q1 ∷
   rw 7 q9 ∷
   re 6 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   rw 5 q9 ∷
   rw 6 q47 ∷
   rw 5 q5 ∷
   rw 8 q1 ∷
   re 6 3 (CK30⁻ ∷ []) ∷
   rw 7 q5 ∷
   rw 8 q2 ∷
   rw 9 q34 ∷
   rw⁻ 8 q35 ∷
   rw⁻ 7 q36 ∷
   re 6 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q37 ∷
   rw 7 q44 ∷
   rw⁻ 6 q37 ∷
   re 7 3 (CK31⁻ ∷ []) ∷
   rw⁻ 5 q36 ∷
   rw 6 q45 ∷
   rw 5 q35 ∷
   rw 6 q36 ∷
   re 8 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q37 ∷
   rw 8 q46 ∷
   rw 9 q37 ∷
   re 7 3 (CK30⁻ ∷ []) ∷
   rw 8 q36 ∷
   rw 9 q41 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q50 : Eqn
  q50 = eqn (X3 ∷ CK31 ∷ X3 ∷ X2 ∷ []) (X2 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (wn 1412 W)
  q51 : Eqn
  q51 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q52 : Eqn
  q52 = eqn (X2 ∷ CK20 ∷ X2 ∷ []) (X2 ∷ CK20 ∷ X2 ∷ []) (wn 1413 W)
  q53 : Eqn
  q53 = eqn (X3 ∷ CK30 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-TOFF102-CS13-TOFF102-CSd13)

-- pass [X3 CK30 X3] [X2 TOFF102 CS13 TOFF102 CSd13 X2]: 61 steps
lem-pass-X3-CK30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = derive (X3 ∷ CK30 ∷ X3 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  (rw 4 q34 ∷
   rw⁻ 3 q35 ∷
   rw⁻ 2 q36 ∷
   re 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q37 ∷
   rw 2 q49 ∷
   rw⁻ 1 q37 ∷
   re 2 3 (CK31 ∷ []) ∷
   rw⁻ 0 q36 ∷
   rw 1 q50 ∷
   rw 0 q35 ∷
   rw 1 q36 ∷
   re 3 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 2 q37 ∷
   rw 3 q51 ∷
   rw 4 q37 ∷
   re 2 3 (CK30 ∷ []) ∷
   rw 3 q36 ∷
   rw 4 q41 ∷
   rw 4 q1 ∷
   rw 3 q9 ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 4 q2 ∷
   rw 1 q9 ∷
   rw 2 q52 ∷
   rw 1 q5 ∷
   rw 4 q1 ∷
   re 2 3 (CK30 ∷ []) ∷
   rw 3 q5 ∷
   rw 4 q2 ∷
   rw 1 q53 ∷
   rw 8 q1 ∷
   rw 7 q9 ∷
   re 6 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   rw 5 q9 ∷
   rw 6 q52 ∷
   rw 5 q5 ∷
   rw 8 q1 ∷
   re 6 3 (CK30 ∷ []) ∷
   rw 7 q5 ∷
   rw 8 q2 ∷
   rw 9 q34 ∷
   rw⁻ 8 q35 ∷
   rw⁻ 7 q36 ∷
   re 6 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q37 ∷
   rw 7 q49 ∷
   rw⁻ 6 q37 ∷
   re 7 3 (CK31 ∷ []) ∷
   rw⁻ 5 q36 ∷
   rw 6 q50 ∷
   rw 5 q35 ∷
   rw 6 q36 ∷
   re 8 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 7 q37 ∷
   rw 8 q51 ∷
   rw 9 q37 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 8 q36 ∷
   rw 9 q41 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q55 : Eqn
  q55 = eqn (X3 ∷ CS13 ∷ X3 ∷ X2 ∷ []) (X2 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (wn 2064 W)
  q56 : Eqn
  q56 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q57 : Eqn
  q57 = eqn (X2 ∷ CS02 ∷ X2 ∷ []) (X2 ∷ CS02 ∷ X2 ∷ []) (wn 1490 W)
  q58 : Eqn
  q58 = eqn (X3 ∷ CS03 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-TOFF102-CS13-TOFF102-CSd13)

-- pass [X3 CS30 X3] [X2 TOFF102 CS13 TOFF102 CSd13 X2]: 61 steps
lem-pass-X3-CS30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = derive (X3 ∷ CS03 ∷ X3 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  (rw 4 q34 ∷
   rw⁻ 3 q35 ∷
   rw⁻ 2 q36 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q37 ∷
   rw 2 q54 ∷
   rw⁻ 1 q37 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 0 q36 ∷
   rw 1 q55 ∷
   rw 0 q35 ∷
   rw 1 q36 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q37 ∷
   rw 3 q56 ∷
   rw 4 q37 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q36 ∷
   rw 4 q41 ∷
   rw 4 q1 ∷
   rw 3 q9 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q2 ∷
   rw 1 q9 ∷
   rw 2 q57 ∷
   rw 1 q5 ∷
   rw 4 q1 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q5 ∷
   rw 4 q2 ∷
   rw 1 q58 ∷
   rw 8 q1 ∷
   rw 7 q9 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   rw 5 q9 ∷
   rw 6 q57 ∷
   rw 5 q5 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q5 ∷
   rw 8 q2 ∷
   rw 9 q34 ∷
   rw⁻ 8 q35 ∷
   rw⁻ 7 q36 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q37 ∷
   rw 7 q54 ∷
   rw⁻ 6 q37 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 5 q36 ∷
   rw 6 q55 ∷
   rw 5 q35 ∷
   rw 6 q36 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q37 ∷
   rw 8 q56 ∷
   rw 9 q37 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q36 ∷
   rw 9 q41 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q60 : Eqn
  q60 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q61 : Eqn
  q61 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q62 : Eqn
  q62 = eqn (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wn 196 W)
  q63 : Eqn
  q63 = eqn (X2 ∷ Toff102 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ X2 ∷ []) (wn 1778 W)
  q64 : Eqn
  q64 = eqn (CS12 ∷ X3 ∷ []) (X3 ∷ CS12 ∷ []) (low₃-comm ((CS ↑)) (X))
  q65 : Eqn
  q65 = eqn (CS12⁻ ∷ X3 ∷ []) (X3 ∷ CS12⁻ ∷ []) (low₃-comm (((CS • CS • CS) ↑)) (X))
  q66 : Eqn
  q66 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff103 ∷ X3 ∷ CS12 ∷ X3 ∷ Toff103 ∷ X3 ∷ CS12⁻ ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ CS12 ∷ X3 ∷ Toff103 ∷ X3 ∷ CS12⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF103-X3-CS12-X3-TOFF103-X3-CSd12)
  q67 : Eqn
  q67 = eqn (X2 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (Toff102 ∷ X2 ∷ []) (wn 1777 W)

-- pass [X3 TOFF012 CS03 TOFF012 CSd03 X3] [TOFF103 CS12 TOFF103 CSd12]: 249 steps
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF103-CS12-TOFF103-CSd12 : ⟪ (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF103-CS12-TOFF103-CSd12 = derive (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 7 q1 ∷
   re 6 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 7 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 6 q59 ∷
   rw 9 q1 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q60 ∷
   rw 11 q1 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q60 ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q59 ∷
   rw⁻ 13 q61 ∷
   rw 14 q2 ∷
   rw 13 q61 ∷
   rw 12 q59 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q2 ∷
   rw 10 q60 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q2 ∷
   rw 8 q60 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q2 ∷
   rw 6 q59 ∷
   rw 7 q62 ∷
   re 7 8 (Toff102 ∷ []) ∷
   rw 5 q9 ∷
   rw 6 q63 ∷
   rw 5 q5 ∷
   re 7 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 6 q59 ∷
   rw 9 q1 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q60 ∷
   rw 11 q1 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q60 ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q59 ∷
   rw⁻ 13 q61 ∷
   rw 6 q1 ∷
   rw⁻ 7 q59 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   rw⁻ 9 q60 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   rw⁻ 11 q60 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q2 ∷
   rw⁻ 13 q59 ∷
   rw⁻ 14 q61 ∷
   rw 7 q62 ∷
   re 7 8 (Toff102 ∷ []) ∷
   re 6 3 (Toff103 ∷ []) ∷
   rw 7 q5 ∷
   rw 8 q5 ∷
   rw 9 q2 ∷
   rw⁻ 8 q64 ∷
   rw 11 q1 ∷
   re 10 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 11 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 10 q59 ∷
   rw 13 q1 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw⁻ 12 q60 ∷
   rw 15 q1 ∷
   re 13 3 (CS13⁻ ∷ []) ∷
   rw⁻ 14 q60 ∷
   rw 17 q1 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw⁻ 16 q59 ∷
   rw⁻ 17 q61 ∷
   rw 18 q2 ∷
   rw 17 q61 ∷
   rw 16 q59 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q2 ∷
   rw 14 q60 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q2 ∷
   rw 12 q60 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q2 ∷
   rw 10 q59 ∷
   rw 11 q62 ∷
   re 11 8 (Toff102 ∷ []) ∷
   rw 9 q9 ∷
   rw 10 q63 ∷
   rw 9 q5 ∷
   re 11 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 10 q59 ∷
   rw 13 q1 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw⁻ 12 q60 ∷
   rw 15 q1 ∷
   re 13 3 (CS13⁻ ∷ []) ∷
   rw⁻ 14 q60 ∷
   rw 17 q1 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw⁻ 16 q59 ∷
   rw⁻ 17 q61 ∷
   rw 10 q1 ∷
   rw⁻ 11 q59 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q2 ∷
   rw⁻ 13 q60 ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q2 ∷
   rw⁻ 15 q60 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q2 ∷
   rw⁻ 17 q59 ∷
   rw⁻ 18 q61 ∷
   rw 11 q62 ∷
   re 11 8 (Toff102 ∷ []) ∷
   re 10 3 (Toff103 ∷ []) ∷
   rw 11 q5 ∷
   rw 12 q5 ∷
   rw 13 q2 ∷
   rw⁻ 12 q65 ∷
   rw 1 q66 ∷
   rw 4 q1 ∷
   rw 3 q9 ∷
   re 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 q59 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q60 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q60 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q59 ∷
   rw⁻ 9 q61 ∷
   rw 10 q2 ∷
   rw 9 q61 ∷
   rw 8 q59 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q2 ∷
   rw 6 q60 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   rw 4 q60 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q2 ∷
   rw 2 q59 ∷
   rw 3 q62 ∷
   re 3 8 (Toff102 ∷ []) ∷
   rw 1 q9 ∷
   rw 0 q9 ∷
   rw 1 q67 ∷
   re 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 0 q59 ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q60 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q60 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q59 ∷
   rw⁻ 7 q61 ∷
   rw 0 q1 ∷
   rw⁻ 1 q59 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q2 ∷
   rw⁻ 3 q60 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q2 ∷
   rw⁻ 5 q60 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q2 ∷
   rw⁻ 7 q59 ∷
   rw⁻ 8 q61 ∷
   rw 1 q62 ∷
   re 1 8 (Toff102 ∷ []) ∷
   re 0 3 (Toff103 ∷ []) ∷
   rw 1 q5 ∷
   rw 2 q2 ∷
   rw⁻ 1 q64 ∷
   rw 6 q1 ∷
   rw 5 q9 ∷
   re 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 4 q59 ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q60 ∷
   rw 9 q1 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q60 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q59 ∷
   rw⁻ 11 q61 ∷
   rw 12 q2 ∷
   rw 11 q61 ∷
   rw 10 q59 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q2 ∷
   rw 8 q60 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q2 ∷
   rw 6 q60 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   rw 4 q59 ∷
   rw 5 q62 ∷
   re 5 8 (Toff102 ∷ []) ∷
   rw 3 q9 ∷
   rw 2 q9 ∷
   rw 3 q67 ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 q59 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q60 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q60 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q59 ∷
   rw⁻ 9 q61 ∷
   rw 2 q1 ∷
   rw⁻ 3 q59 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q2 ∷
   rw⁻ 5 q60 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q2 ∷
   rw⁻ 7 q60 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   rw⁻ 9 q59 ∷
   rw⁻ 10 q61 ∷
   rw 3 q62 ∷
   re 3 8 (Toff102 ∷ []) ∷
   re 2 3 (Toff103 ∷ []) ∷
   rw 3 q5 ∷
   rw 4 q2 ∷
   rw⁻ 3 q65 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = eqn (CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-TOFF012-CS03-TOFF012-CSd03)
  q69 : Eqn
  q69 = eqn (CCZ013 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ013 ∷ []) (lem-pass-CCZ013-vs-TOFF012-CS03-TOFF012-CSd03)

-- MBi a0: 2 steps
lem-MBi-a0 : ⟪ (CCZ013 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ013 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-MBi-a0 = derive (CCZ013 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ013 ∷ CS03⁻ ∷ [])
  (rw 1 q68 ∷
   rw 0 q69 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = eqn (S0 ∷ K0 ∷ []) (CS02 ∷ CK20 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 2099 W)
  q71 : Eqn
  q71 = eqn (K0⁻ ∷ S0⁻ ∷ []) (X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ CK20⁻ ∷ CS02⁻ ∷ []) (wn 2100 W)
  q72 : Eqn
  q72 = eqn (X2 ∷ CK20 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012)
  q73 : Eqn
  q73 = eqn (X2 ∷ CS02 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012)
  q74 : Eqn
  q74 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) [] (wn 2101 W)

-- ca-split Gad(t=0, W=(), d=SK, e=-1) 2: 5 steps
lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2 : ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CK20 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CK20⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2 = derive (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (CS02 ∷ CK20 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CK20⁻ ∷ CS02⁻ ∷ [])
  (rw 0 q70 ∷
   rw 12 q71 ∷
   rw 5 q72 ∷
   rw 2 q73 ∷
   rw 6 q74 ∷ []) Eq.refl
