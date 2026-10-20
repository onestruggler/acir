{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D730 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D513 W using (lem-pass-CK31-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 ; lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D538 W using (lem-CA-CK30-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩ ; lem-pass-CCZ012-vs-TOFF012-CS03-TOFF012-CSd03 ; lem-pass-CK30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3)
open import Examples.Groups.Clifford+CS.Four.D.D539 W using (lem-pass-CK20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 ; lem-pass-CKd20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 ; lem-pass-CS20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 ; lem-pass-CSd20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 ; lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D541 W using (lem-pass-CK21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 ; lem-pass-CKd21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 ; lem-pass-CS21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 ; lem-pass-CS21-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 ; lem-pass-CSd21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 ; lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D542 W using (lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D596 W using (lem-pass-CK20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 ; lem-pass-CK21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 ; lem-pass-CKd20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 ; lem-pass-CKd21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 ; lem-pass-CS20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 ; lem-pass-CS20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 ; lem-pass-CS21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 ; lem-pass-CSd20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 ; lem-pass-CSd21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3)
open import Examples.Groups.Clifford+CS.Four.D.D651 W using (lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D677 W using (lem-S2-at1023)
open import Examples.Groups.Clifford+CS.Four.D.D681 W using (lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D682 W using (lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D701 W using (lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D702 W using (lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D711 W using (lem-C3d-A ; lem-pass-X3-K0-CS03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03 ; lem-pass-X3-K0-CSd03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D712 W using (lem-CA-CKd30-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ ; lem-CA-CS30-Gad⟨t≡0-W≡⟨⟩-d≡K-e≡1⟩ ; lem-CA-CS30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩ ; lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2 ; lem-pass-CS30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 ; lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF103-CS12-TOFF103-CSd12)
open import Examples.Groups.Clifford+CS.Four.D.D713 W using (lem-pass-CK20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 ; lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-CS03 ; lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-CS03-TOFF012-CSd03-TOFF012)
open import Examples.Groups.Clifford+CS.Four.D.D714 W using (lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-2 ; lem-pass-CK21-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 ; lem-pass-CS31-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 ; lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 ; lem-pass-X1-CK10-X1-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X2-CK20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 ; lem-pass-X2-CK21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 ; lem-pass-X2-CK21-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 ; lem-pass-X2-CKd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CSd21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 ; lem-pass-X2-TOFF012-CS03-TOFF012-CSd03-X2-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X3-CK31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 ; lem-pass-X3-CK31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 ; lem-pass-X3-CKd31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 ; lem-pass-X3-CKd31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 ; lem-pass-X3-CS31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 ; lem-pass-X3-CS31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 ; lem-pass-X3-CSd31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 ; lem-pass-X3-CSd31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1)
open import Examples.Groups.Clifford+CS.Four.D.D715 W using (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13 ; lem-pass-X2-CK21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 ; lem-pass-X2-CSd21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3)

private
  q1 : Eqn
  q1 = eqn (CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-C3d-A)

-- pass [CSd03] [TOFF012 CS03 TOFF012]: 1 steps
lem-pass-CSd03-vs-TOFF012-CS03-TOFF012 : ⟪ (CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-TOFF012-CS03-TOFF012 = derive (CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw 0 q1 ∷ []) Eq.refl

private
  q2 : Eqn
  q2 = eqn (X3 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ X3 ∷ []) (lem-pass-X3-K0-CSd03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03)
  q3 : Eqn
  q3 = eqn (CCZ012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-TOFF012-CS03-TOFF012-CSd03)
  q4 : Eqn
  q4 = eqn (X3 ∷ K0 ∷ CS03 ∷ K0⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ K0 ∷ CS03 ∷ K0⁻ ∷ X3 ∷ []) (lem-pass-X3-K0-CS03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03)

-- pass [CCZ012 X3 K0 CS03 Kd0 X3 CCZ012 X3 K0 CSd03 Kd0 X3] [TOFF012 CS03 TOFF012 CSd03]: 4 steps
lem-pass-CCZ012-X3-K0-CS03-Kd0-X3-CCZ012-X3-K0-CSd03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (CCZ012 ∷ X3 ∷ K0 ∷ CS03 ∷ K0⁻ ∷ X3 ∷ CCZ012 ∷ X3 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ012 ∷ X3 ∷ K0 ∷ CS03 ∷ K0⁻ ∷ X3 ∷ CCZ012 ∷ X3 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-CCZ012-X3-K0-CS03-Kd0-X3-CCZ012-X3-K0-CSd03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (CCZ012 ∷ X3 ∷ K0 ∷ CS03 ∷ K0⁻ ∷ X3 ∷ CCZ012 ∷ X3 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ012 ∷ X3 ∷ K0 ∷ CS03 ∷ K0⁻ ∷ X3 ∷ CCZ012 ∷ X3 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ X3 ∷ [])
  (rw 7 q2 ∷
   rw 6 q3 ∷
   rw 1 q4 ∷
   rw 0 q3 ∷ []) Eq.refl

private
  q5 : Eqn
  q5 = eqn (CK30 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ CK30 ∷ []) (lem-CA-CK30-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩)
  q6 : Eqn
  q6 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q7 : Eqn
  q7 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q8 : Eqn
  q8 = eqn (CK20 ∷ CK20⁻ ∷ []) [] (wn 1696 W)
  q9 : Eqn
  q9 = eqn (CS03 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ []) (S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ CS03 ∷ []) (lem-CA-CS30-Gad⟨t≡0-W≡⟨⟩-d≡K-e≡1⟩)
  q10 : Eqn
  q10 = eqn (CS02 ∷ CS02⁻ ∷ []) [] (wn 1342 W)
  q11 : Eqn
  q11 = eqn (CK30⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ CK30⁻ ∷ []) (lem-CA-CKd30-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩)
  q12 : Eqn
  q12 = eqn (CK20⁻ ∷ CK20 ∷ []) [] (wn 1356 W)

-- CAw KdSK Gad(t=0, W=(), d=1, e=1): 24 steps
lem-CAw-KdSK-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩ : ⟪ (CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ
lem-CAw-KdSK-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩ = derive (CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ [])
  (rw 2 q5 ∷
   rw 10 q6 ∷
   re 9 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   re 8 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 10 q7 ∷
   rw 9 q8 ∷
   rw 8 q7 ∷
   rw 1 q9 ∷
   rw 11 q6 ∷
   re 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q7 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   rw 10 q10 ∷
   rw 9 q7 ∷
   rw 0 q11 ∷
   rw 12 q6 ∷
   re 11 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 13 q7 ∷
   re 10 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q7 ∷
   rw 11 q12 ∷
   rw 10 q7 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = eqn (CS03 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) (K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ CS03 ∷ []) (lem-CA-CS30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩)

-- CAw S Gad(t=0, W=(), d=SdKdSd, e=1): 8 steps
lem-CAw-S-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩ : ⟪ (CS03 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ []) ⟫ʷ
lem-CAw-S-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩ = derive (CS03 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ CS03⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ [])
  (rw 0 q13 ∷
   rw 10 q6 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q7 ∷
   rw 9 q10 ∷
   rw 8 q7 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q15 : Eqn
  q15 = eqn (K0 ∷ X3 ∷ []) (X3 ∷ K0 ∷ []) (low₁-comm (K) ((X ↑ ↑)))
  q16 : Eqn
  q16 = eqn (S0⁻ ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑ ↑)))
  q17 : Eqn
  q17 = eqn (K0⁻ ∷ X3 ∷ []) (X3 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((X ↑ ↑)))
  q18 : Eqn
  q18 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q19 : Eqn
  q19 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q20 : Eqn
  q20 = eqn (S0 ∷ K0 ∷ []) (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ CS02 ∷ CK20 ∷ []) (wn 2222 W)
  q21 : Eqn
  q21 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q22 : Eqn
  q22 = eqn (S0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑)))
  q23 : Eqn
  q23 = eqn (K0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑)))
  q24 : Eqn
  q24 = eqn (K0⁻ ∷ S0⁻ ∷ []) (CK20⁻ ∷ CS02⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 2223 W)
  q25 : Eqn
  q25 = eqn (CK30 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30 ∷ []) (lem-pass-CK30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3)
  q26 : Eqn
  q26 = eqn (CS03 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ []) (lem-pass-CS30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3)
  q27 : Eqn
  q27 = eqn (CS02 ∷ CK20 ∷ CK20⁻ ∷ CS02⁻ ∷ []) [] (wn 2224 W)

-- ca-split Gad(t=0, W=(3,), d=SK, e=-1) 3: 51 steps
lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3 : ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3 = derive (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw⁻ 0 q14 ∷
   rw⁻ 1 q15 ∷
   rw 8 q16 ∷
   rw 7 q17 ∷
   rw 2 q6 ∷
   rw 1 q18 ∷
   rw 0 q19 ∷
   rw 1 q20 ∷
   rw 0 q21 ∷
   rw 3 q6 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q21 ∷
   rw 3 q21 ∷
   rw 6 q6 ∷
   re 4 3 (CK30 ∷ []) ∷
   rw 5 q21 ∷
   rw 8 q6 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 9 q6 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 8 q7 ∷
   rw 16 q6 ∷
   rw 15 q22 ∷
   rw 14 q23 ∷
   rw 15 q24 ∷
   rw 16 q6 ∷
   re 14 3 (CK30⁻ ∷ []) ∷
   rw 17 q6 ∷
   re 15 3 (CS03⁻ ∷ []) ∷
   rw 16 q21 ∷
   rw 19 q6 ∷
   re 17 3 (CK30⁻ ∷ []) ∷
   rw 18 q21 ∷
   rw 19 q21 ∷
   rw 22 q6 ∷
   re 20 3 (CS03⁻ ∷ []) ∷
   rw 21 q21 ∷
   rw 22 q7 ∷
   rw 7 q25 ∷
   rw 6 q26 ∷
   rw 16 q6 ∷
   re 15 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q7 ∷
   re 14 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q7 ∷
   re 13 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 15 q7 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q7 ∷
   rw 13 q27 ∷
   rw 12 q7 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (lem-S2-at1023)
  q29 : Eqn
  q29 = eqn (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF103-CS12-TOFF103-CSd12)
  q30 : Eqn
  q30 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) lem-S2-at1023

-- pass [X3 TOFF012 CS03 TOFF012 CSd03 X3] [TOFF102 CS13 TOFF102 CSd13]: 3 steps
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 6 q28 ∷
   rw 0 q29 ∷
   rw⁻ 0 q30 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = eqn (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (CS02 ∷ CK20 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CK20⁻ ∷ CS02⁻ ∷ []) (lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2)
  q32 : Eqn
  q32 = eqn (CS02 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS02 ∷ []) lem-pass-CS20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2
  q33 : Eqn
  q33 = eqn (CK20 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK20 ∷ []) lem-pass-CK20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2
  q34 : Eqn
  q34 = eqn (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-CS03-TOFF012-CSd03-TOFF012)
  q35 : Eqn
  q35 = eqn (CK20⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK20⁻ ∷ []) lem-pass-CKd20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2
  q36 : Eqn
  q36 = eqn (CS02⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS02⁻ ∷ []) lem-pass-CSd20-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2
  q37 : Eqn
  q37 = eqn (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (CS02 ∷ CK20 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CK20⁻ ∷ CS02⁻ ∷ []) lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2

-- pass [X2 TOFF102 CS13 TOFF102 CSd13 X2] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 7 steps
lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ [])
  (rw 6 q31 ∷
   rw⁻ 0 q32 ∷
   rw⁻ 1 q33 ∷
   rw 2 q34 ∷
   rw⁻ 6 q35 ∷
   rw⁻ 7 q36 ∷
   rw⁻ 0 q37 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = eqn (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ []) (CS03 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-CS03

-- pass [CS03] [X3 TOFF012 CS03 TOFF012 CSd03 X3]: 1 steps
lem-pass-CS03-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : ⟪ (CS03 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = derive (CS03 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ [])
  (rw⁻ 0 q38 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = eqn [] (X3 ∷ X3 ∷ []) (wn 225 W)
  q40 : Eqn
  q40 = eqn [] (Toff012 ∷ Toff012 ∷ []) (wn 45 W)
  q41 : Eqn
  q41 = eqn [] (CS02 ∷ CS02⁻ ∷ []) (wn 1357 W)
  q42 : Eqn
  q42 = eqn [] (CS02⁻ ∷ CS02 ∷ []) (wn 231 W)
  q43 : Eqn
  q43 = eqn (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q44 : Eqn
  q44 = eqn (X3 ∷ X3 ∷ []) [] (wn 390 W)
  q45 : Eqn
  q45 = eqn (Toff012 ∷ Toff012 ∷ []) [] (wn 227 W)
  q46 : Eqn
  q46 = eqn (CS02⁻ ∷ CS02 ∷ []) [] (wn 1358 W)

-- pass [X3 CS03 TOFF012 CSd03 TOFF012 X3] [CS03 TOFF012 CSd03 TOFF012]: 37 steps
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ [])
  (rw 10 q39 ∷
   rw 11 q40 ∷
   rw 12 q6 ∷
   rw 13 q41 ∷
   rw 14 q6 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 15 q6 ∷
   re 13 3 (CS03⁻ ∷ []) ∷
   rw 14 q7 ∷
   rw 13 q40 ∷
   rw 14 q6 ∷
   rw 15 q42 ∷
   rw 16 q6 ∷
   re 14 3 (CS03⁻ ∷ []) ∷
   rw 17 q6 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 16 q7 ∷
   rw 15 q39 ∷
   rw⁻ 6 q43 ∷
   rw 5 q44 ∷
   rw 4 q45 ∷
   rw 5 q6 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw 4 q46 ∷
   rw 3 q7 ∷
   rw 2 q45 ∷
   rw 3 q6 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   rw 2 q10 ∷
   rw 1 q7 ∷
   rw 0 q44 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = eqn (S0 ∷ X2 ∷ []) (X2 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑)))
  q48 : Eqn
  q48 = eqn (K0 ∷ X2 ∷ []) (X2 ∷ K0 ∷ []) (low₁-comm (K) ((X ↑)))
  q49 : Eqn
  q49 = eqn (S0⁻ ∷ X2 ∷ []) (X2 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑)))
  q50 : Eqn
  q50 = eqn (K0⁻ ∷ X2 ∷ []) (X2 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((X ↑)))
  q51 : Eqn
  q51 = eqn (CK20 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20 ∷ []) (lem-pass-CK20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2)
  q52 : Eqn
  q52 = eqn (CS02 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02 ∷ []) (lem-pass-CS20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2)

-- ca-split Gad(t=0, W=(2,), d=SK, e=-1) 2: 9 steps
lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩-2 : ⟪ (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩-2 = derive (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  (rw⁻ 0 q47 ∷
   rw⁻ 1 q48 ∷
   rw 8 q49 ∷
   rw 7 q50 ∷
   rw 0 q20 ∷
   rw 14 q24 ∷
   rw 7 q51 ∷
   rw 6 q52 ∷
   rw 12 q27 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = eqn [] (X2 ∷ X2 ∷ []) (wn 871 W)
  q54 : Eqn
  q54 = eqn (X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ []) lem-pass-X2-TOFF012-CS03-TOFF012-CSd03-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q55 : Eqn
  q55 = eqn (X2 ∷ X2 ∷ []) [] (wn 389 W)

-- pass [X2 CS03 TOFF012 CSd03 TOFF012 X2] [CS03 TOFF012 CSd03 TOFF012]: 37 steps
lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ [])
  (rw 10 q53 ∷
   rw 11 q40 ∷
   rw 12 q6 ∷
   rw 13 q41 ∷
   rw 14 q6 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 15 q6 ∷
   re 13 3 (CS03⁻ ∷ []) ∷
   rw 14 q7 ∷
   rw 13 q40 ∷
   rw 14 q6 ∷
   rw 15 q42 ∷
   rw 16 q6 ∷
   re 14 3 (CS03⁻ ∷ []) ∷
   rw 17 q6 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 16 q7 ∷
   rw 15 q53 ∷
   rw⁻ 6 q54 ∷
   rw 5 q55 ∷
   rw 4 q45 ∷
   rw 5 q6 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw 4 q46 ∷
   rw 3 q7 ∷
   rw 2 q45 ∷
   rw 3 q6 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   rw 2 q10 ∷
   rw 1 q7 ∷
   rw 0 q55 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = eqn (CK20⁻ ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1464 W)
  q57 : Eqn
  q57 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-CS03-TOFF012-CSd03-TOFF012)
  q58 : Eqn
  q58 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK20⁻ ∷ []) (wn 1465 W)

-- pass [CKd20] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 3 steps
lem-pass-CKd20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (CK20⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20⁻ ∷ []) ⟫ʷ
lem-pass-CKd20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = derive (CK20⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20⁻ ∷ [])
  (rw 0 q56 ∷
   rw 1 q57 ∷
   rw 5 q58 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ S0 ∷ K0 ∷ []) (S0 ∷ K0 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 2104 W)
  q60 : Eqn
  q60 = eqn (X2 ∷ CS02 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012)
  q61 : Eqn
  q61 = eqn (X2 ∷ CK20 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012)
  q62 : Eqn
  q62 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 2105 W)

-- pass [X2 CKd20 X2] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 7 steps
lem-pass-X2-CKd20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X2 ∷ CK20⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  (rw 0 q59 ∷
   rw 14 q57 ∷
   rw 11 q60 ∷
   rw 8 q60 ∷
   rw 5 q61 ∷
   rw 2 q60 ∷
   rw 6 q62 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = eqn (X2 ∷ CS02 ∷ X2 ∷ S0 ∷ K0 ∷ []) (S0 ∷ K0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 2106 W)
  q64 : Eqn
  q64 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012)
  q65 : Eqn
  q65 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 2107 W)

-- pass [X2 CS20 X2] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 5 steps
lem-pass-X2-CS20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X2 ∷ CS02 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ [])
  (rw 0 q63 ∷
   rw 8 q64 ∷
   rw 5 q57 ∷
   rw 2 q64 ∷
   rw 6 q65 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = eqn (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (CS12 ∷ CK21 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ []) (lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-2)
  q67 : Eqn
  q67 = eqn (CS12 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS12 ∷ []) lem-pass-CS21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q68 : Eqn
  q68 = eqn (CK21 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21 ∷ []) lem-pass-CK21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q69 : Eqn
  q69 = eqn (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-TOFF102-CS13-TOFF102-CSd13)
  q70 : Eqn
  q70 = eqn (CK21⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK21⁻ ∷ []) lem-pass-CKd21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q71 : Eqn
  q71 = eqn (CS12⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS12⁻ ∷ []) lem-pass-CSd21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q72 : Eqn
  q72 = eqn (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (CS12 ∷ CK21 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ []) lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-2

-- pass [X2 CS03 TOFF012 CSd03 TOFF012 X2] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 7 steps
lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ [])
  (rw 6 q66 ∷
   rw⁻ 0 q67 ∷
   rw⁻ 1 q68 ∷
   rw 2 q69 ∷
   rw⁻ 6 q70 ∷
   rw⁻ 7 q71 ∷
   rw⁻ 0 q72 ∷ []) Eq.refl

private
  q73 : Eqn
  q73 = eqn (CK20 ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 1407 W)
  q74 : Eqn
  q74 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q75 : Eqn
  q75 = eqn (X2 ∷ CK20 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3)
  q76 : Eqn
  q76 = eqn (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK20 ∷ []) (wn 1408 W)

-- pass [CK20] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 5 steps
lem-pass-CK20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (CK20 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CK20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (CK20 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK20 ∷ [])
  (rw 0 q73 ∷
   rw 9 q74 ∷
   rw 1 q75 ∷
   rw 7 q76 ∷
   rw⁻ 6 q74 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = eqn (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) lem-pass-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3] [CS03 TOFF012 CSd03 TOFF012]: 45 steps
lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ [])
  (rw 12 q53 ∷
   rw 13 q39 ∷
   rw 14 q40 ∷
   rw 15 q6 ∷
   rw 16 q41 ∷
   rw 17 q6 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 18 q6 ∷
   re 16 3 (CS03⁻ ∷ []) ∷
   rw 17 q7 ∷
   rw 16 q40 ∷
   rw 17 q6 ∷
   rw 18 q42 ∷
   rw 19 q6 ∷
   re 17 3 (CS03⁻ ∷ []) ∷
   rw 20 q6 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 19 q7 ∷
   rw 18 q53 ∷
   rw 19 q39 ∷
   rw⁻ 20 q74 ∷
   rw⁻ 26 q74 ∷
   rw⁻ 8 q77 ∷
   rw 8 q74 ∷
   rw 14 q74 ∷
   rw 7 q44 ∷
   rw 6 q55 ∷
   rw 5 q45 ∷
   rw 6 q6 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   re 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 5 q46 ∷
   rw 4 q7 ∷
   rw 3 q45 ∷
   rw 4 q6 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw 3 q10 ∷
   rw 2 q7 ∷
   rw 1 q44 ∷
   rw 0 q55 ∷ []) Eq.refl

private
  q78 : Eqn
  q78 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q79 : Eqn
  q79 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q80 : Eqn
  q80 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q81 : Eqn
  q81 = eqn (CK20⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK21⁻ ∷ []) (wn 137 W)
  q82 : Eqn
  q82 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (wn 1497 W)
  q83 : Eqn
  q83 = eqn (Sw01 ∷ CK21⁻ ∷ []) (CK20⁻ ∷ Sw01 ∷ []) (wn 139 W)
  q84 : Eqn
  q84 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q85 : Eqn
  q85 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ []) (X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1485 W)

-- pass [X2 CKd20 X2] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 25 steps
lem-pass-X2-CKd20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (X2 ∷ CK20⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  (rw 4 q78 ∷
   rw⁻ 3 q79 ∷
   rw⁻ 2 q80 ∷
   rw 1 q81 ∷
   rw⁻ 0 q80 ∷
   rw 1 q82 ∷
   rw 0 q79 ∷
   rw 1 q80 ∷
   rw 2 q83 ∷
   rw 3 q80 ∷
   rw 4 q84 ∷
   rw 1 q85 ∷
   rw 1 q57 ∷
   rw 5 q85 ∷
   rw 9 q78 ∷
   rw⁻ 8 q79 ∷
   rw⁻ 7 q80 ∷
   rw 6 q81 ∷
   rw⁻ 5 q80 ∷
   rw 6 q82 ∷
   rw 5 q79 ∷
   rw 6 q80 ∷
   rw 7 q83 ∷
   rw 8 q80 ∷
   rw 9 q84 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = eqn (CS12 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS12 ∷ []) lem-pass-CS21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q87 : Eqn
  q87 = eqn (CK21 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK21 ∷ []) lem-pass-CK21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q88 : Eqn
  q88 = eqn (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-TOFF102-CS13-TOFF102-CSd13)
  q89 : Eqn
  q89 = eqn (CK21⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK21⁻ ∷ []) lem-pass-CKd21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q90 : Eqn
  q90 = eqn (CS12⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS12⁻ ∷ []) lem-pass-CSd21-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3

-- pass [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 7 steps
lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ [])
  (rw 8 q66 ∷
   rw⁻ 0 q86 ∷
   rw⁻ 1 q87 ∷
   rw 2 q88 ∷
   rw⁻ 6 q89 ∷
   rw⁻ 7 q90 ∷
   rw⁻ 0 q72 ∷ []) Eq.refl

private
  q91 : Eqn
  q91 = eqn (S1 ∷ X3 ∷ []) (X3 ∷ S1 ∷ []) (low-comm ((S ↑)) ((X ↑)))
  q92 : Eqn
  q92 = eqn (K1 ∷ X3 ∷ []) (X3 ∷ K1 ∷ []) (low-comm ((K ↑)) ((X ↑)))
  q93 : Eqn
  q93 = eqn (S1⁻ ∷ X3 ∷ []) (X3 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) ((X ↑)))
  q94 : Eqn
  q94 = eqn (K1⁻ ∷ X3 ∷ []) (X3 ∷ K1⁻ ∷ []) (low-comm (((K • iI) ↑)) ((X ↑)))
  q95 : Eqn
  q95 = eqn (S1 ∷ K1 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ CS13 ∷ CK31 ∷ []) (wn 2225 W)
  q96 : Eqn
  q96 = eqn (K1⁻ ∷ S1⁻ ∷ []) (CK31⁻ ∷ CS13⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (wn 2226 W)
  q97 : Eqn
  q97 = eqn (CK31 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK31 ∷ []) (lem-pass-CK31-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3)
  q98 : Eqn
  q98 = eqn (CS13 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS13 ∷ []) (lem-pass-CS31-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3)
  q99 : Eqn
  q99 = eqn (CS13 ∷ CK31 ∷ CK31⁻ ∷ CS13⁻ ∷ []) [] (wn 2227 W)

-- ca-split Gad(t=1, W=(3,), d=SK, e=1) 3: 9 steps
lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡1⟩-3 : ⟪ (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡1⟩-3 = derive (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ [])
  (rw⁻ 0 q91 ∷
   rw⁻ 1 q92 ∷
   rw 8 q93 ∷
   rw 7 q94 ∷
   rw 0 q95 ∷
   rw 14 q96 ∷
   rw 7 q97 ∷
   rw 6 q98 ∷
   rw 12 q99 ∷ []) Eq.refl

private
  q100 : Eqn
  q100 = eqn (S1 ∷ X2 ∷ []) (X2 ∷ S1 ∷ []) (low-comm ((S ↑)) (X))
  q101 : Eqn
  q101 = eqn (K1 ∷ X2 ∷ []) (X2 ∷ K1 ∷ []) (low-comm ((K ↑)) (X))
  q102 : Eqn
  q102 = eqn (S1⁻ ∷ X2 ∷ []) (X2 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (X))
  q103 : Eqn
  q103 = eqn (K1⁻ ∷ X2 ∷ []) (X2 ∷ K1⁻ ∷ []) (low-comm (((K • iI) ↑)) (X))
  q104 : Eqn
  q104 = eqn (S1 ∷ K1 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ CS12 ∷ CK21 ∷ []) (wn 2228 W)
  q105 : Eqn
  q105 = eqn (K1⁻ ∷ S1⁻ ∷ []) (CK21⁻ ∷ CS12⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (wn 2229 W)
  q106 : Eqn
  q106 = eqn (CK21 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK21 ∷ []) (lem-pass-CK21-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2)
  q107 : Eqn
  q107 = eqn (CS12 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12 ∷ []) (lem-pass-CS21-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2)
  q108 : Eqn
  q108 = eqn (CS12 ∷ CK21 ∷ CK21⁻ ∷ CS12⁻ ∷ []) [] (wn 2230 W)

-- ca-split Gad(t=1, W=(2,), d=SK, e=1) 2: 9 steps
lem-ca-split-Gad⟨t≡1-W≡⟨2⟩-d≡SK-e≡1⟩-2 : ⟪ (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-ca-split-Gad⟨t≡1-W≡⟨2⟩-d≡SK-e≡1⟩-2 = derive (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  (rw⁻ 0 q100 ∷
   rw⁻ 1 q101 ∷
   rw 8 q102 ∷
   rw 7 q103 ∷
   rw 0 q104 ∷
   rw 14 q105 ∷
   rw 7 q106 ∷
   rw 6 q107 ∷
   rw 12 q108 ∷ []) Eq.refl

private
  q109 : Eqn
  q109 = eqn (CK21 ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (wn 1476 W)
  q110 : Eqn
  q110 = eqn (X2 ∷ CK21 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3)
  q111 : Eqn
  q111 = eqn (X2 ∷ CK21 ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK21 ∷ []) (wn 1477 W)

-- pass [CK21] [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3]: 5 steps
lem-pass-CK21-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : ⟪ (CK21 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CK21 ∷ []) ⟫ʷ
lem-pass-CK21-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = derive (CK21 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CK21 ∷ [])
  (rw 0 q109 ∷
   rw 9 q74 ∷
   rw 1 q110 ∷
   rw 7 q111 ∷
   rw⁻ 6 q74 ∷ []) Eq.refl

private
  q112 : Eqn
  q112 = eqn (CS02 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ []) lem-pass-CS20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3
  q113 : Eqn
  q113 = eqn (CK20 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CK20 ∷ []) lem-pass-CK20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3
  q114 : Eqn
  q114 = eqn (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) (lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012)
  q115 : Eqn
  q115 = eqn (CK20⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CK20⁻ ∷ []) lem-pass-CKd20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3
  q116 : Eqn
  q116 = eqn (CS02⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS02⁻ ∷ []) lem-pass-CSd20-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3

-- pass [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 7 steps
lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ [])
  (rw 8 q31 ∷
   rw⁻ 0 q112 ∷
   rw⁻ 1 q113 ∷
   rw 2 q114 ∷
   rw⁻ 6 q115 ∷
   rw⁻ 7 q116 ∷
   rw⁻ 0 q37 ∷ []) Eq.refl

private
  q117 : Eqn
  q117 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ K0 ∷ []) (S0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (wn 2231 W)
  q118 : Eqn
  q118 = eqn (X1 ∷ CS01 ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012)
  q119 : Eqn
  q119 = eqn (X1 ∷ CK10 ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (lem-pass-X1-CK10-X1-vs-CS03-TOFF012-CSd03-TOFF012)
  q120 : Eqn
  q120 = eqn (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 2232 W)

-- pass [X1 CSd10 X1] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 5 steps
lem-pass-X1-CSd10-X1-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  (rw 0 q117 ∷
   rw 8 q118 ∷
   rw 5 q119 ∷
   rw 2 q118 ∷
   rw 6 q120 ∷ []) Eq.refl

private
  q121 : Eqn
  q121 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ S0 ∷ K0 ∷ []) (S0 ∷ S0 ∷ K0 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (wn 2233 W)
  q122 : Eqn
  q122 = eqn (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 2234 W)

-- pass [X1 CSd10 X1] [S0 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 Sd0]: 5 steps
lem-pass-X1-CSd10-X1-vs-S0-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-Sd0 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-S0-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-Sd0 = derive (X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  (rw 0 q121 ∷
   rw 9 q118 ∷
   rw 6 q119 ∷
   rw 3 q118 ∷
   rw 7 q122 ∷ []) Eq.refl

private
  q123 : Eqn
  q123 = eqn (CS13⁻ ∷ X3 ∷ []) (X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (wn 2113 W)
  q124 : Eqn
  q124 = eqn (X3 ∷ CS13⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q125 : Eqn
  q125 = eqn (X3 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ []) (wn 2114 W)

-- pass [CSd31] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 3 steps
lem-pass-CSd31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (CS13⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-CSd31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (CS13⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS13⁻ ∷ [])
  (rw 0 q123 ∷
   rw 1 q124 ∷
   rw 9 q125 ∷ []) Eq.refl

private
  q126 : Eqn
  q126 = eqn (CK31⁻ ∷ X3 ∷ []) (X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (wn 1940 W)
  q127 : Eqn
  q127 = eqn (X3 ∷ CK31⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q128 : Eqn
  q128 = eqn (X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ []) (X3 ∷ CK31⁻ ∷ []) (wn 1941 W)

-- pass [CKd31] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 3 steps
lem-pass-CKd31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (CK31⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK31⁻ ∷ []) ⟫ʷ
lem-pass-CKd31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (CK31⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK31⁻ ∷ [])
  (rw 0 q126 ∷
   rw 1 q127 ∷
   rw 9 q128 ∷ []) Eq.refl

private
  q129 : Eqn
  q129 = eqn (CK31 ∷ X3 ∷ []) (X3 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (wn 1366 W)
  q130 : Eqn
  q130 = eqn (X3 ∷ CK31 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) (lem-pass-X3-CK31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q131 : Eqn
  q131 = eqn (X3 ∷ CK31 ∷ X3 ∷ X3 ∷ []) (X3 ∷ CK31 ∷ []) (wn 1367 W)

-- pass [CK31] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 3 steps
lem-pass-CK31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (CK31 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK31 ∷ []) ⟫ʷ
lem-pass-CK31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (CK31 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK31 ∷ [])
  (rw 0 q129 ∷
   rw 1 q130 ∷
   rw 9 q131 ∷ []) Eq.refl

private
  q132 : Eqn
  q132 = eqn (CS13 ∷ X3 ∷ []) (X3 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (wn 2111 W)
  q133 : Eqn
  q133 = eqn (X3 ∷ CS13 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) (lem-pass-X3-CS31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q134 : Eqn
  q134 = eqn (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ []) (wn 2112 W)

-- pass [CS31] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 3 steps
lem-pass-CS31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (CS13 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (CS13 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS13 ∷ [])
  (rw 0 q132 ∷
   rw 1 q133 ∷
   rw 9 q134 ∷ []) Eq.refl

private
  q135 : Eqn
  q135 = eqn (X3 ∷ CS13⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1)

-- pass [CSd31] [X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X3]: 3 steps
lem-pass-CSd31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : ⟪ (CS13⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-CSd31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = derive (CS13⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS13⁻ ∷ [])
  (rw 0 q123 ∷
   rw 1 q135 ∷
   rw 9 q125 ∷ []) Eq.refl

private
  q136 : Eqn
  q136 = eqn (X3 ∷ CK31⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1)

-- pass [CKd31] [X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X3]: 3 steps
lem-pass-CKd31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : ⟪ (CK31⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CK31⁻ ∷ []) ⟫ʷ
lem-pass-CKd31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = derive (CK31⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CK31⁻ ∷ [])
  (rw 0 q126 ∷
   rw 1 q136 ∷
   rw 9 q128 ∷ []) Eq.refl

private
  q137 : Eqn
  q137 = eqn (X3 ∷ CK31 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) (lem-pass-X3-CK31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1)

-- pass [CK31] [X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X3]: 3 steps
lem-pass-CK31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : ⟪ (CK31 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CK31 ∷ []) ⟫ʷ
lem-pass-CK31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = derive (CK31 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CK31 ∷ [])
  (rw 0 q129 ∷
   rw 1 q137 ∷
   rw 9 q131 ∷ []) Eq.refl

private
  q138 : Eqn
  q138 = eqn (X3 ∷ CS13 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) (lem-pass-X3-CS31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1)

-- pass [CS31] [X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X3]: 3 steps
lem-pass-CS31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : ⟪ (CS13 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS31-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = derive (CS13 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS13 ∷ [])
  (rw 0 q132 ∷
   rw 1 q138 ∷
   rw 9 q134 ∷ []) Eq.refl

private
  q139 : Eqn
  q139 = eqn (X2 ∷ Toff102 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ X2 ∷ []) (wn 1778 W)
  q140 : Eqn
  q140 = eqn (X2 ∷ CS13 ∷ []) (CS13 ∷ X2 ∷ []) (wn 257 W)
  q141 : Eqn
  q141 = eqn (X2 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X2 ∷ []) (wn 258 W)
  q142 : Eqn
  q142 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13)
  q143 : Eqn
  q143 = eqn (X2 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (Toff102 ∷ X2 ∷ []) (wn 1777 W)

-- pass [X2 TOFF102 CS13 TOFF102 CSd13 X2] [TOFF102 CS13 TOFF102 CSd13]: 9 steps
lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-TOFF102-CS13-TOFF102-CSd13 = derive (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ [])
  (rw 5 q139 ∷
   rw 8 q140 ∷
   rw 9 q139 ∷
   rw 12 q141 ∷
   rw 1 q142 ∷
   rw 0 q143 ∷
   rw 1 q140 ∷
   rw 2 q143 ∷
   rw 3 q141 ∷ []) Eq.refl

private
  q144 : Eqn
  q144 = eqn (CS12⁻ ∷ X2 ∷ []) (X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (wn 1480 W)
  q145 : Eqn
  q145 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1)
  q146 : Eqn
  q146 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ []) (wn 1481 W)

-- pass [CSd21] [X2 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2]: 3 steps
lem-pass-CSd21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 : ⟪ (CS12⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-CSd21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 = derive (CS12⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ []) (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS12⁻ ∷ [])
  (rw 0 q144 ∷
   rw 1 q145 ∷
   rw 9 q146 ∷ []) Eq.refl

private
  q147 : Eqn
  q147 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ S1 ∷ K1 ∷ []) (S1 ∷ K1 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (wn 2235 W)
  q148 : Eqn
  q148 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13)
  q149 : Eqn
  q149 = eqn (X2 ∷ CS12 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13)
  q150 : Eqn
  q150 = eqn (X2 ∷ CK21 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13)
  q151 : Eqn
  q151 = eqn (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ K1⁻ ∷ S1⁻ ∷ []) (K1⁻ ∷ S1⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (wn 2236 W)

-- pass [X2 CKd21 X2] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 7 steps
lem-pass-X2-CKd21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (X2 ∷ CK21⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  (rw 0 q147 ∷
   rw 14 q148 ∷
   rw 11 q149 ∷
   rw 8 q149 ∷
   rw 5 q150 ∷
   rw 2 q149 ∷
   rw 6 q151 ∷ []) Eq.refl

private
  q152 : Eqn
  q152 = eqn (X2 ∷ CK21 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1)

-- pass [CK21] [X2 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2]: 3 steps
lem-pass-CK21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 : ⟪ (CK21 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK21 ∷ []) ⟫ʷ
lem-pass-CK21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 = derive (CK21 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ []) (X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK21 ∷ [])
  (rw 0 q109 ∷
   rw 1 q152 ∷
   rw 9 q111 ∷ []) Eq.refl

private
  q153 : Eqn
  q153 = eqn (X2 ∷ CS12 ∷ X2 ∷ S1 ∷ K1 ∷ []) (S1 ∷ K1 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (wn 2237 W)
  q154 : Eqn
  q154 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13)
  q155 : Eqn
  q155 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ K1⁻ ∷ S1⁻ ∷ []) (K1⁻ ∷ S1⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) (wn 2238 W)

-- pass [X2 CS21 X2] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 5 steps
lem-pass-X2-CS21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (X2 ∷ CS12 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ [])
  (rw 0 q153 ∷
   rw 8 q154 ∷
   rw 5 q148 ∷
   rw 2 q154 ∷
   rw 6 q155 ∷ []) Eq.refl

private
  q156 : Eqn
  q156 = eqn (Toff102 ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ []) (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))
  q157 : Eqn
  q157 = eqn (X3 ∷ CS13 ∷ []) (S1 ∷ CS13⁻ ∷ X3 ∷ []) (wn 1958 W)
  q158 : Eqn
  q158 = eqn (X3 ∷ CS13⁻ ∷ []) (S1⁻ ∷ CS13 ∷ X3 ∷ []) (wn 1959 W)
  q159 : Eqn
  q159 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2-S1-CSd13-X2-TOFF102-X2-Sd1-CS13)
  q160 : Eqn
  q160 = eqn (S1 ∷ S1⁻ ∷ CS13 ∷ []) (CS13 ∷ []) (wn 1960 W)
  q161 : Eqn
  q161 = eqn (S1⁻ ∷ S1 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ []) (wn 1961 W)

-- pass [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3] [TOFF102 CS13 TOFF102 CSd13]: 31 steps
lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 7 q156 ∷
   rw 8 q157 ∷
   rw⁻ 10 q156 ∷
   rw 11 q158 ∷
   rw 6 q139 ∷
   rw⁻ 9 q100 ∷
   rw 10 q141 ∷
   rw 11 q139 ∷
   rw⁻ 14 q102 ∷
   rw 15 q140 ∷
   rw 2 q159 ∷
   rw⁻ 1 q74 ∷
   rw⁻ 2 q156 ∷
   rw⁻ 3 q74 ∷
   rw⁻ 4 q91 ∷
   rw 5 q158 ∷
   rw⁻ 7 q74 ∷
   rw⁻ 8 q156 ∷
   rw⁻ 9 q74 ∷
   rw⁻ 10 q93 ∷
   rw 11 q157 ∷
   rw 0 q143 ∷
   rw⁻ 1 q100 ∷
   rw⁻ 2 q102 ∷
   rw 3 q140 ∷
   rw 4 q143 ∷
   rw⁻ 5 q102 ∷
   rw⁻ 6 q100 ∷
   rw 7 q141 ∷
   rw 1 q160 ∷
   rw 3 q161 ∷ []) Eq.refl

private
  q162 : Eqn
  q162 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3)

-- pass [CSd21] [X2 X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2 X3]: 5 steps
lem-pass-CSd21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 : ⟪ (CS12⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-CSd21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 = derive (CS12⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CS12⁻ ∷ [])
  (rw 0 q144 ∷
   rw 13 q74 ∷
   rw 1 q162 ∷
   rw 11 q146 ∷
   rw⁻ 10 q74 ∷ []) Eq.refl

-- pass [X2 CKd21 X2] [X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X3]: 9 steps
lem-pass-X2-CKd21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = derive (X2 ∷ CK21⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  (rw 0 q82 ∷
   rw 1 q147 ∷
   rw 15 q148 ∷
   rw 12 q149 ∷
   rw 9 q149 ∷
   rw 6 q150 ∷
   rw 3 q149 ∷
   rw 7 q151 ∷
   rw 9 q82 ∷ []) Eq.refl

private
  q163 : Eqn
  q163 = eqn (X2 ∷ CK21 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (lem-pass-X2-CK21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3)

-- pass [CK21] [X2 X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2 X3]: 5 steps
lem-pass-CK21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 : ⟪ (CK21 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CK21 ∷ []) ⟫ʷ
lem-pass-CK21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 = derive (CK21 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CK21 ∷ [])
  (rw 0 q109 ∷
   rw 13 q74 ∷
   rw 1 q163 ∷
   rw 11 q111 ∷
   rw⁻ 10 q74 ∷ []) Eq.refl

private
  q164 : Eqn
  q164 = eqn (X2 ∷ CS12 ∷ X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (wn 1493 W)

-- pass [X2 CS21 X2] [X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X3]: 7 steps
lem-pass-X2-CS21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = derive (X2 ∷ CS12 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ [])
  (rw 0 q164 ∷
   rw 1 q153 ∷
   rw 9 q154 ∷
   rw 6 q148 ∷
   rw 3 q154 ∷
   rw 7 q155 ∷
   rw 9 q164 ∷ []) Eq.refl
