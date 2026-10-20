{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D725 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D513 W using (lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03 ; lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D701 W using (lem-pass-X2-CKd20-X2-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D702 W using (lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D707 W using (lem-pass-X2-CKd20-X2-vs-K0-S0-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-Sd0-Kd0)
open import Examples.Groups.Clifford+CS.Four.D.D708 W using (lem-pass-CCZ123-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 ; lem-pass-CK13-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 ; lem-pass-CKd13-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 ; lem-pass-X3-CS30-X3-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 ; lem-pass-X3-CSd30-X3-vs-X1-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X1)

private
  q1 : Eqn
  q1 = eqn (X2 ∷ CK20 ∷ X2 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 2197 W)
  q2 : Eqn
  q2 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-TOFF012-CS03-TOFF012-CSd03)
  q3 : Eqn
  q3 = eqn (X2 ∷ CS02 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03)
  q4 : Eqn
  q4 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 2198 W)

-- pass [X2 CK20 X2] [S0 Kd0 S0 S0 TOFF012 CS03 TOFF012 CSd03 Sd0 Sd0 K0 Sd0]: 7 steps
lem-pass-X2-CK20-X2-vs-S0-Kd0-S0-S0-TOFF012-CS03-TOFF012-CSd03-Sd0-Sd0-K0-Sd0 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK20-X2-vs-S0-Kd0-S0-S0-TOFF012-CS03-TOFF012-CSd03-Sd0-Sd0-K0-Sd0 = derive (X2 ∷ CK20 ∷ X2 ∷ S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ [])
  (rw 0 q1 ∷
   rw 16 q2 ∷
   rw 13 q3 ∷
   rw 10 q3 ∷
   rw 7 q2 ∷
   rw 4 q3 ∷
   rw 8 q4 ∷ []) Eq.refl

private
  q5 : Eqn
  q5 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (wn 2199 W)
  q6 : Eqn
  q6 = eqn (X1 ∷ CK10 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03)
  q7 : Eqn
  q7 = eqn (X1 ∷ CS01 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03)
  q8 : Eqn
  q8 = eqn (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 2200 W)

-- pass [X1 CSd10 X1] [Sd0 K0 S0 S0 K0 TOFF012 CS03 TOFF012 CSd03 Kd0 Sd0 Sd0 Kd0 S0]: 5 steps
lem-pass-X1-CSd10-X1-vs-Sd0-K0-S0-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-Sd0-Kd0-S0 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-Sd0-K0-S0-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-Sd0-Kd0-S0 = derive (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  (rw 0 q5 ∷
   rw 11 q6 ∷
   rw 8 q6 ∷
   rw 5 q7 ∷
   rw 9 q8 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = eqn (CK20 ∷ []) (K0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1459 W)
  q10 : Eqn
  q10 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-K0-S0-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0-Sd0-Kd0)
  q11 : Eqn
  q11 = eqn (K0 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ []) (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (wn 2201 W)
  q12 : Eqn
  q12 = eqn (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ []) (wn 2202 W)
  q13 : Eqn
  q13 = eqn (K0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (CK20 ∷ []) (wn 1461 W)

-- CA CK20 Gad(t=0, W=(), d=KSSK, e=1): 5 steps
lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡KSSK-e≡1⟩ : ⟪ (CK20 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ CK20 ∷ []) ⟫ʷ
lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡KSSK-e≡1⟩ = derive (CK20 ∷ K0 ∷ S0 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (S0 ∷ S0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ CK20 ∷ [])
  (rw 0 q9 ∷
   rw 1 q10 ∷
   rw 0 q11 ∷
   rw 9 q12 ∷
   rw 14 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ []) (S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (wn 2203 W)
  q15 : Eqn
  q15 = eqn (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 2204 W)

-- pass [X1 CSd10 X1] [Sd0 K0 Sd0 K0 K0 TOFF012 CS03 TOFF012 CSd03 Kd0 Kd0 S0 Kd0 S0]: 5 steps
lem-pass-X1-CSd10-X1-vs-Sd0-K0-Sd0-K0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Kd0-S0-Kd0-S0 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-Sd0-K0-Sd0-K0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Kd0-S0-Kd0-S0 = derive (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  (rw 0 q14 ∷
   rw 11 q6 ∷
   rw 8 q7 ∷
   rw 5 q7 ∷
   rw 9 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q17 : Eqn
  q17 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q18 : Eqn
  q18 = eqn (CS02⁻ ∷ []) (S0⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 1812 W)
  q19 : Eqn
  q19 = eqn (S0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑)))
  q20 : Eqn
  q20 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q21 : Eqn
  q21 = eqn (X3 ∷ CS03 ∷ X3 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1)
  q22 : Eqn
  q22 = eqn (S0⁻ ∷ X1 ∷ []) (X1 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) (X))
  q23 : Eqn
  q23 = eqn (S0⁻ ∷ []) (S0⁻ ∷ []) (wn 1813 W)
  q24 : Eqn
  q24 = eqn [] (S0 ∷ S0⁻ ∷ []) (wn 1732 W)
  q25 : Eqn
  q25 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q26 : Eqn
  q26 = eqn (S0⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) (CS02⁻ ∷ []) (wn 1814 W)

-- CA CSd30 Gad(t=0, W=(1,), d=1, e=1): 25 steps
lem-CA-CSd30-Gad⟨t≡0-W≡⟨1⟩-d≡1-e≡1⟩ : ⟪ (CS03⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X1 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-CA-CSd30-Gad⟨t≡0-W≡⟨1⟩-d≡1-e≡1⟩ = derive (CS03⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X1 ∷ CS03⁻ ∷ [])
  (rw 1 q16 ∷
   re 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q17 ∷
   rw 1 q18 ∷
   rw⁻ 0 q19 ∷
   rw 1 q20 ∷
   rw 4 q16 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q20 ∷
   rw 4 q17 ∷
   rw 1 q21 ∷
   rw 0 q22 ∷
   rw 1 q23 ∷
   rw 6 q24 ∷
   rw 7 q22 ∷
   rw 12 q16 ∷
   rw 11 q25 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q17 ∷
   rw 9 q25 ∷
   rw 8 q19 ∷
   rw 9 q26 ∷
   rw 10 q16 ∷
   re 8 3 (CS03⁻ ∷ []) ∷
   rw 9 q17 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = eqn (CS02 ∷ []) (S0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 1815 W)
  q28 : Eqn
  q28 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q29 : Eqn
  q29 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ X1 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X1 ∷ []) (X1 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X1 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-X1-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X1)
  q30 : Eqn
  q30 = eqn (S0 ∷ X1 ∷ []) (X1 ∷ S0 ∷ []) (low₁-comm (S) (X))
  q31 : Eqn
  q31 = eqn (S0 ∷ S0⁻ ∷ []) [] (wn 1728 W)
  q32 : Eqn
  q32 = eqn (S0 ∷ []) (S0 ∷ []) (wn 1727 W)
  q33 : Eqn
  q33 = eqn (S0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (CS02 ∷ []) (wn 1816 W)

-- CA CS30 Gad(t=0, W=(1,), d=Sd, e=1): 25 steps
lem-CA-CS30-Gad⟨t≡0-W≡⟨1⟩-d≡Sd-e≡1⟩ : ⟪ (CS03 ∷ X1 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS03 ∷ []) ⟫ʷ
lem-CA-CS30-Gad⟨t≡0-W≡⟨1⟩-d≡Sd-e≡1⟩ = derive (CS03 ∷ X1 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X1 ∷ []) (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS03 ∷ [])
  (rw 1 q16 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q17 ∷
   rw 1 q27 ∷
   rw⁻ 0 q28 ∷
   rw 1 q20 ∷
   rw 4 q16 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q20 ∷
   rw 4 q17 ∷
   rw 1 q29 ∷
   rw 0 q30 ∷
   rw 1 q31 ∷
   rw 5 q32 ∷
   rw 5 q30 ∷
   rw 10 q16 ∷
   rw 9 q25 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q17 ∷
   rw 7 q25 ∷
   rw 6 q28 ∷
   rw 7 q33 ∷
   rw 8 q16 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q17 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = eqn (CK10 ∷ X1 ∷ []) (X1 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (wn 2205 W)
  q35 : Eqn
  q35 = eqn (X1 ∷ CK10 ∷ X1 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ []) (wn 2206 W)

-- pass [CK10] [X1 TOFF012 CS03 TOFF012 CSd03 X1]: 3 steps
lem-pass-CK10-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : ⟪ (CK10 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CK10-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = derive (CK10 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK10 ∷ [])
  (rw 0 q34 ∷
   rw 1 q6 ∷
   rw 5 q35 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = eqn (CCZ123 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1)

-- CCZ(1,2,3) passes split Gad(t=0, W=(1,), d=1, e=1): 1 steps
lem-CCZ⟨123⟩-passes-split-Gad⟨t≡0-W≡⟨1⟩-d≡1-e≡1⟩ : ⟪ (CCZ123 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ⟨123⟩-passes-split-Gad⟨t≡0-W≡⟨1⟩-d≡1-e≡1⟩ = derive (CCZ123 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CCZ123 ∷ [])
  (rw 0 q36 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = eqn (Toff312 ∷ []) (CK13 ∷ CCZ123 ∷ CK13⁻ ∷ []) (wn 2207 W)
  q38 : Eqn
  q38 = eqn (CK13⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK13⁻ ∷ []) (lem-pass-CKd13-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1)
  q39 : Eqn
  q39 = eqn (CK13 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK13 ∷ []) (lem-pass-CK13-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1)
  q40 : Eqn
  q40 = eqn (CK13 ∷ CCZ123 ∷ CK13⁻ ∷ []) (Toff312 ∷ []) (wn 2208 W)

-- pass [TOFF312] [X1 TOFF012 CS03 TOFF012 CSd03 X1]: 5 steps
lem-pass-TOFF312-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : ⟪ (Toff312 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ Toff312 ∷ []) ⟫ʷ
lem-pass-TOFF312-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = derive (Toff312 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ Toff312 ∷ [])
  (rw 0 q37 ∷
   rw 2 q38 ∷
   rw 1 q36 ∷
   rw 0 q39 ∷
   rw 6 q40 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ K0⁻ ∷ []) (K0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (wn 2209 W)
  q42 : Eqn
  q42 = eqn (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ K0 ∷ []) (K0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 2210 W)

-- pass [X1 CSd10 X1] [Kd0 TOFF012 CS03 TOFF012 CSd03 K0]: 5 steps
lem-pass-X1-CSd10-X1-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 = derive (X1 ∷ CS01⁻ ∷ X1 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ []) (K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  (rw 0 q41 ∷
   rw 7 q7 ∷
   rw 4 q6 ∷
   rw 1 q7 ∷
   rw 5 q42 ∷ []) Eq.refl
