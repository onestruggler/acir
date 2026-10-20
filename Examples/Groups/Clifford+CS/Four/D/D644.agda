{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D644 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D009 W using (lem-pass-CSd13-vs-CS03 ; lem-pass-CSd13-vs-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D011 W using (lem-pass-CS03-vs-S1)
open import Examples.Groups.Clifford+CS.Four.D.D015 W using (lem-pass-CSd03-vs-S1)
open import Examples.Groups.Clifford+CS.Four.D.D380 W using (lem-pass-CS03-vs-CZ13 ; lem-pass-CSd03-vs-CZ13)
open import Examples.Groups.Clifford+CS.Four.D.D510 W using (lem-pass-CCZ123-vs-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D511 W using (lem-pass-CCZ123-vs-CS03)
open import Examples.Groups.Clifford+CS.Four.D.D588 W using (lem-pass-TOFF012-vs-CZ13)
open import Examples.Groups.Clifford+CS.Four.D.D596 W using (lem-pass-CCZ123-vs-TOFF012 ; lem-pass-CSd13-vs-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D613 W using (lem-pass-CS03-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2)
open import Examples.Groups.Clifford+CS.Four.D.D614 W using (lem-pass-CS03-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 ; lem-pass-CSd03-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 ; lem-pass-CSd03-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 ; lem-pass-TOFF012-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 ; lem-pass-TOFF012-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 ; lem-pass-X1-CS10-X1-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 ; lem-pass-X1-CSd10-X1-vs-X2-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2 ; lem-pass-X2-CS21-X2-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 ; lem-pass-X2-CSd21-X2-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 ; lem-pass-X3-CKd30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 ; lem-pass-X3-CKd30-X3-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2 ; lem-pass-X3-CKd31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0)
open import Examples.Groups.Clifford+CS.Four.D.D615 W using (lem-pass-CZ13-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102 ; lem-pass-X1-CSd10-X1-vs-Sd0-K0-K0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-Kd0-Kd0-S0 ; lem-pass-X1-CSd10-X1-vs-Sd0-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0-S0 ; lem-pass-X3-CKd31-X3-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2)

private
  q1 : Eqn
  q1 = eqn (CS13⁻ ∷ CS03 ∷ []) (CS03 ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-CS03)
  q2 : Eqn
  q2 = eqn (CS13⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-TOFF012)
  q3 : Eqn
  q3 = eqn (CS13⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS13⁻ ∷ []) (lem-pass-CSd13-vs-CSd03)

-- pass [CSd13] [CS03 TOFF012 CSd03 TOFF012]: 4 steps
lem-pass-CSd13-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-CSd13-vs-CS03-TOFF012-CSd03-TOFF012 = derive (CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS13⁻ ∷ [])
  (rw 0 q1 ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q2 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = eqn (CS03 ∷ S1 ∷ []) (S1 ∷ CS03 ∷ []) lem-pass-CS03-vs-S1
  q5 : Eqn
  q5 = eqn (S1 ∷ Toff012 ∷ []) (Toff012 ∷ S1 ∷ []) (wn 1418 W)
  q6 : Eqn
  q6 = eqn (CS03⁻ ∷ S1 ∷ []) (S1 ∷ CS03⁻ ∷ []) lem-pass-CSd03-vs-S1

-- pass [S1 CSd13] [CS03 TOFF012 CSd03 TOFF012]: 8 steps
lem-pass-S1-CSd13-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (S1 ∷ CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S1 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-S1-CSd13-vs-CS03-TOFF012-CSd03-TOFF012 = derive (S1 ∷ CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S1 ∷ CS13⁻ ∷ [])
  (rw 1 q1 ∷
   rw⁻ 0 q4 ∷
   rw 2 q2 ∷
   rw 1 q5 ∷
   rw 3 q3 ∷
   rw⁻ 2 q6 ∷
   rw 4 q2 ∷
   rw 3 q5 ∷ []) Eq.refl

private
  q7 : Eqn
  q7 = eqn (Toff012 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2)
  q8 : Eqn
  q8 = eqn (CS03⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2)
  q9 : Eqn
  q9 = eqn (CS03 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03 ∷ []) (lem-pass-CS03-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2)

-- pass [CS03 TOFF012 CSd03 TOFF012] [CS13 X2 TOFF102 X2 CSd13 X2 TOFF102 X2]: 4 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  (rw 3 q7 ∷
   rw 2 q8 ∷
   rw 1 q7 ∷
   rw 0 q9 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = eqn (Toff012 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ []) (lem-pass-TOFF012-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2)
  q11 : Eqn
  q11 = eqn (CS03⁻ ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03⁻ ∷ []) (lem-pass-CSd03-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2)
  q12 : Eqn
  q12 = eqn (CS03 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03 ∷ []) (lem-pass-CS03-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2)

-- pass [CS03 TOFF012 CSd03 TOFF012] [S1 CSd13 X2 TOFF102 X2 Sd1 CS13 X2 TOFF102 X2]: 4 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  (rw 3 q10 ∷
   rw 2 q11 ∷
   rw 1 q10 ∷
   rw 0 q12 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = eqn (CCZ123 ∷ CS03 ∷ []) (CS03 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CS03)
  q14 : Eqn
  q14 = eqn (CS03 ∷ CZ13 ∷ []) (CZ13 ∷ CS03 ∷ []) lem-pass-CS03-vs-CZ13
  q15 : Eqn
  q15 = eqn (CCZ123 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-TOFF012)
  q16 : Eqn
  q16 = eqn (Toff012 ∷ CZ13 ∷ []) (CZ13 ∷ Toff012 ∷ []) lem-pass-TOFF012-vs-CZ13
  q17 : Eqn
  q17 = eqn (CCZ123 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CSd03)
  q18 : Eqn
  q18 = eqn (CS03⁻ ∷ CZ13 ∷ []) (CZ13 ∷ CS03⁻ ∷ []) lem-pass-CSd03-vs-CZ13

-- pass [CZ13 CCZ123] [CS03 TOFF012 CSd03 TOFF012]: 8 steps
lem-pass-CZ13-CCZ123-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (CZ13 ∷ CCZ123 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CZ13 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CZ13-CCZ123-vs-CS03-TOFF012-CSd03-TOFF012 = derive (CZ13 ∷ CCZ123 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CZ13 ∷ CCZ123 ∷ [])
  (rw 1 q13 ∷
   rw⁻ 0 q14 ∷
   rw 2 q15 ∷
   rw⁻ 1 q16 ∷
   rw 3 q17 ∷
   rw⁻ 2 q18 ∷
   rw 4 q15 ∷
   rw⁻ 3 q16 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q20 : Eqn
  q20 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q21 : Eqn
  q21 = eqn (CK20 ∷ []) (K0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1459 W)
  q22 : Eqn
  q22 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q23 : Eqn
  q23 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q24 : Eqn
  q24 = eqn (X3 ∷ CK30⁻ ∷ X3 ∷ X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ []) (X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2)
  q25 : Eqn
  q25 = eqn (K0 ∷ X2 ∷ []) (X2 ∷ K0 ∷ []) (low₁-comm (K) ((X ↑)))
  q26 : Eqn
  q26 = eqn (K0 ∷ K0⁻ ∷ []) [] (wn 1846 W)
  q27 : Eqn
  q27 = eqn (K0 ∷ []) (K0 ∷ []) (wn 1460 W)
  q28 : Eqn
  q28 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q29 : Eqn
  q29 = eqn (K0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (CK20 ∷ []) (wn 1461 W)

-- CA CK30 Gad(t=0, W=(2,), d=Kd, e=-1): 25 steps
lem-CA-CK30-Gad⟨t≡0-W≡⟨2⟩-d≡Kd-e≡-1⟩ : ⟪ (CK30 ∷ X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK30 ∷ []) ⟫ʷ
lem-CA-CK30-Gad⟨t≡0-W≡⟨2⟩-d≡Kd-e≡-1⟩ = derive (CK30 ∷ X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK30 ∷ [])
  (rw 1 q19 ∷
   re 0 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 2 q20 ∷
   rw 1 q21 ∷
   rw⁻ 0 q22 ∷
   rw 1 q23 ∷
   rw 4 q19 ∷
   re 2 3 (CK30⁻ ∷ []) ∷
   rw 3 q23 ∷
   rw 4 q20 ∷
   rw 1 q24 ∷
   rw 0 q25 ∷
   rw 1 q26 ∷
   rw 5 q27 ∷
   rw 5 q25 ∷
   rw 10 q19 ∷
   rw 9 q28 ∷
   re 8 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q20 ∷
   rw 7 q28 ∷
   rw 6 q22 ∷
   rw 7 q29 ∷
   rw 8 q19 ∷
   re 6 3 (CK30 ∷ []) ∷
   rw 7 q20 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = eqn (CS01⁻ ∷ []) (S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (wn 1817 W)
  q31 : Eqn
  q31 = eqn (X1 ∷ CS01 ∷ X1 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2)
  q32 : Eqn
  q32 = eqn (S0⁻ ∷ X2 ∷ []) (X2 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑)))
  q33 : Eqn
  q33 = eqn (S0⁻ ∷ []) (S0⁻ ∷ []) (wn 1813 W)
  q34 : Eqn
  q34 = eqn [] (S0 ∷ S0⁻ ∷ []) (wn 1732 W)
  q35 : Eqn
  q35 = eqn (S0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (CS01⁻ ∷ []) (wn 1818 W)

-- CA CSd10 Gad(t=0, W=(2,), d=1, e=-1): 7 steps
lem-CA-CSd10-Gad⟨t≡0-W≡⟨2⟩-d≡1-e≡-1⟩ : ⟪ (CS01⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-CA-CSd10-Gad⟨t≡0-W≡⟨2⟩-d≡1-e≡-1⟩ = derive (CS01⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ CS01⁻ ∷ [])
  (rw 0 q30 ∷
   rw 1 q31 ∷
   rw 0 q32 ∷
   rw 1 q33 ∷
   rw 6 q34 ∷
   rw 7 q32 ∷
   rw 8 q35 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = eqn (CS01 ∷ []) (S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 1819 W)
  q37 : Eqn
  q37 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ []) (X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-X2-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2)
  q38 : Eqn
  q38 = eqn (S0 ∷ X2 ∷ []) (X2 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑)))
  q39 : Eqn
  q39 = eqn (S0 ∷ S0⁻ ∷ []) [] (wn 1728 W)
  q40 : Eqn
  q40 = eqn (S0 ∷ []) (S0 ∷ []) (wn 1727 W)
  q41 : Eqn
  q41 = eqn (S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (CS01 ∷ []) (wn 1820 W)

-- CA CS10 Gad(t=0, W=(2,), d=Sd, e=-1): 7 steps
lem-CA-CS10-Gad⟨t≡0-W≡⟨2⟩-d≡Sd-e≡-1⟩ : ⟪ (CS01 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS01 ∷ []) ⟫ʷ
lem-CA-CS10-Gad⟨t≡0-W≡⟨2⟩-d≡Sd-e≡-1⟩ = derive (CS01 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS01 ∷ [])
  (rw 0 q36 ∷
   rw 1 q37 ∷
   rw 0 q38 ∷
   rw 1 q39 ∷
   rw 5 q40 ∷
   rw 5 q38 ∷
   rw 6 q41 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q43 : Eqn
  q43 = eqn (CK20⁻ ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1464 W)
  q44 : Eqn
  q44 = eqn (X3 ∷ CK30⁻ ∷ X3 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2)
  q45 : Eqn
  q45 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK20⁻ ∷ []) (wn 1465 W)

-- pass [CKd30] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 25 steps
lem-pass-CKd30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (CK30⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ []) ⟫ʷ
lem-pass-CKd30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (CK30⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ [])
  (rw 1 q42 ∷
   rw 2 q19 ∷
   rw 1 q28 ∷
   re 0 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q20 ∷
   rw 1 q43 ∷
   rw 0 q23 ∷
   rw 1 q23 ∷
   rw 4 q19 ∷
   re 2 3 (CK30⁻ ∷ []) ∷
   rw 3 q23 ∷
   rw 4 q20 ∷
   rw 1 q44 ∷
   rw 11 q19 ∷
   rw 10 q28 ∷
   rw 9 q28 ∷
   re 8 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q20 ∷
   rw 7 q28 ∷
   rw 8 q45 ∷
   rw 7 q23 ∷
   rw 10 q19 ∷
   re 8 3 (CK30⁻ ∷ []) ∷
   rw 9 q20 ∷
   rw⁻ 0 q42 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = eqn (X0 ∷ X3 ∷ []) (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑)))
  q47 : Eqn
  q47 = eqn (CK31⁻ ∷ X3 ∷ []) (X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (wn 1940 W)
  q48 : Eqn
  q48 = eqn (X3 ∷ CK31⁻ ∷ X3 ∷ X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ []) (X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0)
  q49 : Eqn
  q49 = eqn (X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ []) (X3 ∷ CK31⁻ ∷ []) (wn 1941 W)

-- pass [CKd31] [X0 X3 CS13 TOFF102 CSd13 TOFF102 X0 X3]: 5 steps
lem-pass-CKd31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : ⟪ (CK31⁻ ∷ X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ CK31⁻ ∷ []) ⟫ʷ
lem-pass-CKd31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = derive (CK31⁻ ∷ X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ CK31⁻ ∷ [])
  (rw 1 q46 ∷
   rw 0 q47 ∷
   rw 1 q48 ∷
   rw 7 q49 ∷
   rw⁻ 0 q46 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = eqn (X0 ∷ X2 ∷ []) (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑)))
  q51 : Eqn
  q51 = eqn (CS12 ∷ X2 ∷ []) (X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (wn 1474 W)
  q52 : Eqn
  q52 = eqn (X2 ∷ CS12 ∷ X2 ∷ X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ []) (X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0)
  q53 : Eqn
  q53 = eqn (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ []) (wn 1475 W)

-- pass [CS21] [X0 X2 CS13 TOFF102 CSd13 TOFF102 X0 X2]: 5 steps
lem-pass-CS21-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 : ⟪ (CS12 ∷ X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS21-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 = derive (CS12 ∷ X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ []) (X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ CS12 ∷ [])
  (rw 1 q50 ∷
   rw 0 q51 ∷
   rw 1 q52 ∷
   rw 7 q53 ∷
   rw⁻ 0 q50 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = eqn (CS12⁻ ∷ X2 ∷ []) (X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (wn 1480 W)
  q55 : Eqn
  q55 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ []) (X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0)
  q56 : Eqn
  q56 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ []) (wn 1481 W)

-- pass [CSd21] [X0 X2 CS13 TOFF102 CSd13 TOFF102 X0 X2]: 5 steps
lem-pass-CSd21-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 : ⟪ (CS12⁻ ∷ X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-CSd21-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 = derive (CS12⁻ ∷ X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ []) (X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ CS12⁻ ∷ [])
  (rw 1 q50 ∷
   rw 0 q54 ∷
   rw 1 q55 ∷
   rw 7 q56 ∷
   rw⁻ 0 q50 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = eqn (CZ13 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CZ13 ∷ CCZ123 ∷ []) lem-pass-CZ13-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102

-- pass [CS13 TOFF102 CSd13 TOFF102] [CZ13 CCZ123]: 1 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-CZ13-CCZ123 : ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CZ13 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-CZ13-CCZ123 = derive (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CZ13 ∷ CCZ123 ∷ []) (CZ13 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ [])
  (rw⁻ 0 q57 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = eqn (X3 ∷ CK31⁻ ∷ X3 ∷ X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ []) (X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd31-X3-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2)

-- pass [CKd31] [X0 X2 X3 CS13 TOFF102 CSd13 TOFF102 X0 X2 X3]: 7 steps
lem-pass-CKd31-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : ⟪ (CK31⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CK31⁻ ∷ []) ⟫ʷ
lem-pass-CKd31-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = derive (CK31⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ X3 ∷ CK31⁻ ∷ [])
  (rw 2 q42 ∷
   rw 1 q46 ∷
   rw 0 q47 ∷
   rw 1 q58 ∷
   rw 9 q49 ∷
   rw⁻ 0 q46 ∷
   rw⁻ 1 q42 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-Sd0-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0-S0)
  q60 : Eqn
  q60 = eqn (S0 ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ []) (K0⁻ ∷ K0⁻ ∷ []) (wn 1942 W)
  q61 : Eqn
  q61 = eqn (K0 ∷ K0 ∷ S0 ∷ []) (K0 ∷ K0 ∷ S0 ∷ []) (wn 1943 W)

-- CA CS10 Gad(t=0, W=(), d=SdKdKd, e=-1): 5 steps
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdKd-e≡-1⟩ : ⟪ (CS01 ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ CS01 ∷ []) ⟫ʷ
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKdKd-e≡-1⟩ = derive (CS01 ∷ S0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ S0 ∷ []) (K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ CS01 ∷ [])
  (rw 0 q36 ∷
   rw 1 q59 ∷
   rw 0 q60 ∷
   rw 6 q61 ∷
   rw 8 q41 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-Sd0-K0-K0-K0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Kd0-Kd0-Kd0-S0)
  q63 : Eqn
  q63 = eqn (S0 ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (wn 1944 W)
  q64 : Eqn
  q64 = eqn (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) (wn 1945 W)

-- CA CS10 Gad(t=0, W=(), d=SdKKKK, e=-1): 5 steps
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKKKK-e≡-1⟩ : ⟪ (CS01 ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS01 ∷ []) ⟫ʷ
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SdKKKK-e≡-1⟩ = derive (CS01 ∷ S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ []) (K0 ∷ K0 ∷ K0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ CS01 ∷ [])
  (rw 0 q36 ∷
   rw 1 q62 ∷
   rw 0 q63 ∷
   rw 8 q64 ∷
   rw 12 q41 ∷ []) Eq.refl
