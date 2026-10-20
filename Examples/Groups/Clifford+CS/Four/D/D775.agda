{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D775 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D682 W using (lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D712 W using (lem-MBi-a0)
open import Examples.Groups.Clifford+CS.Four.D.D714 W using (lem-pass-X3-CK31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 ; lem-pass-X3-CKd31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 ; lem-pass-X3-CS31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 ; lem-pass-X3-CSd31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
open import Examples.Groups.Clifford+CS.Four.D.D730 W using (lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡1⟩-3 ; lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
open import Examples.Groups.Clifford+CS.Four.D.D743 W using (lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D760 W using (lem-CI-MB-MA ; lem-merge-R0)
open import Examples.Groups.Clifford+CS.Four.D.D765 W using (lem-split-R)
open import Examples.Groups.Clifford+CS.Four.D.D771 W using (lem-a0-Ri-≡-Ri-a0ᵖ-1 ; lem-pass-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-MBi ; lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 ; lem-split-b)

private
  q1 : Eqn
  q1 = eqn (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CCZ013 ∷ CS03⁻ ∷ []) (lem-split-b)
  q2 : Eqn
  q2 = eqn (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (lem-split-R)
  q3 : Eqn
  q3 = eqn (CCZ013 ∷ CS03⁻ ∷ CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ CCZ013 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-CI-MB-MA)
  q4 : Eqn
  q4 = eqn (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) lem-merge-R0
  q5 : Eqn
  q5 = eqn (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CCZ013 ∷ CS03⁻ ∷ []) (CCZ013 ∷ CS03⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (lem-pass-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-MBi)
  q6 : Eqn
  q6 = eqn (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-TOFF012-CS03-TOFF012-CSd03)
  q7 : Eqn
  q7 = eqn (X3 ∷ X3 ∷ []) [] (wn 390 W)
  q8 : Eqn
  q8 = eqn (S0⁻ ∷ S0 ∷ []) [] (wn 2487 W)
  q9 : Eqn
  q9 = eqn (K0⁻ ∷ K0 ∷ []) [] (wn 1339 W)
  q10 : Eqn
  q10 = eqn (Toff012 ∷ Toff012 ∷ []) [] (wn 227 W)
  q11 : Eqn
  q11 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q12 : Eqn
  q12 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q13 : Eqn
  q13 = eqn (CS02⁻ ∷ CS02 ∷ []) [] (wn 1358 W)
  q14 : Eqn
  q14 = eqn (CS02 ∷ CS02⁻ ∷ []) [] (wn 1342 W)
  q15 : Eqn
  q15 = eqn (K0 ∷ K0⁻ ∷ []) [] (wn 1846 W)
  q16 : Eqn
  q16 = eqn (S0 ∷ S0⁻ ∷ []) [] (wn 1728 W)
  q17 : Eqn
  q17 = eqn (CCZ013 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ013 ∷ CS03⁻ ∷ []) (lem-MBi-a0)
  q18 : Eqn
  q18 = eqn (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q19 : Eqn
  q19 = eqn (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-TOFF012-CS03-TOFF012-CSd03)
  q20 : Eqn
  q20 = eqn (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CCZ013 ∷ CS03⁻ ∷ []) lem-split-b

-- F7a gad: 32 steps
lem-F7a-gad : ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ
lem-F7a-gad = derive (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ [])
  (rw 0 q1 ∷
   rw 8 q2 ∷
   rw 6 q3 ∷
   rw⁻ 6 q4 ∷
   rw 14 q5 ∷
   rw 16 q6 ∷
   rw 29 q7 ∷
   rw 28 q8 ∷
   rw 27 q9 ∷
   rw 26 q10 ∷
   rw 27 q11 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q12 ∷
   re 25 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 27 q12 ∷
   rw 26 q13 ∷
   rw 25 q12 ∷
   rw 24 q10 ∷
   rw 25 q11 ∷
   re 24 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 26 q12 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q12 ∷
   rw 24 q14 ∷
   rw 23 q12 ∷
   rw 22 q15 ∷
   rw 21 q16 ∷
   rw 20 q7 ∷
   rw 14 q17 ∷
   rw 0 q18 ∷
   rw 8 q19 ∷
   rw⁻ 12 q20 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q22 : Eqn
  q22 = eqn (S1⁻ ∷ Sw01 ∷ []) (Sw01 ∷ S0⁻ ∷ []) (wn 2549 W)
  q23 : Eqn
  q23 = eqn (K1⁻ ∷ Sw01 ∷ []) (Sw01 ∷ K0⁻ ∷ []) (wn 1731 W)
  q24 : Eqn
  q24 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q25 : Eqn
  q25 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wn 9 W)
  q26 : Eqn
  q26 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q27 : Eqn
  q27 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wn 271 W)
  q28 : Eqn
  q28 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q29 : Eqn
  q29 = eqn (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) (wn 8 W)
  q30 : Eqn
  q30 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wn 10 W)
  q31 : Eqn
  q31 = eqn (K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 272 W)
  q32 : Eqn
  q32 = eqn (S1 ∷ Sw01 ∷ []) (Sw01 ∷ S0 ∷ []) (wn 1207 W)
  q33 : Eqn
  q33 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (lem-a0-Ri-≡-Ri-a0ᵖ-1)
  q34 : Eqn
  q34 = eqn (Sw01 ∷ S0 ∷ []) (S1 ∷ Sw01 ∷ []) (wn 311 W)
  q35 : Eqn
  q35 = eqn (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) (wn 123 W)
  q36 : Eqn
  q36 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q37 : Eqn
  q37 = eqn (Sw01 ∷ CX01 ∷ []) (CX10 ∷ Sw01 ∷ []) (wn 28 W)
  q38 : Eqn
  q38 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q39 : Eqn
  q39 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q40 : Eqn
  q40 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)
  q41 : Eqn
  q41 = eqn (K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ ι1 ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wn 274 W)
  q42 : Eqn
  q42 = eqn (Sw01 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ Sw01 ∷ []) (wn 322 W)
  q43 : Eqn
  q43 = eqn (Sw01 ∷ K0⁻ ∷ []) (K1⁻ ∷ Sw01 ∷ []) (wn 313 W)
  q44 : Eqn
  q44 = eqn (Sw01 ∷ S0⁻ ∷ []) (S1⁻ ∷ Sw01 ∷ []) (wn 312 W)
  q45 : Eqn
  q45 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)

-- a0 Ri = Ri a0^-1 @1023: 139 steps
lem-a0-Ri-≡-Ri-a0ᵖ-1-at1023 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ
lem-a0-Ri-≡-Ri-a0ᵖ-1-at1023 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ [])
  (rw 12 q21 ∷
   rw 11 q22 ∷
   rw 10 q23 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q24 ∷
   rw 10 q25 ∷
   rw⁻ 9 q24 ∷
   re 10 3 (CS03⁻ ∷ []) ∷
   re 8 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 15 q26 ∷
   rw 14 q27 ∷
   rw 13 q28 ∷
   rw 12 q29 ∷
   rw 11 q25 ∷
   rw 10 q29 ∷
   rw 9 q30 ∷
   rw 8 q27 ∷
   rw 9 q31 ∷
   re 9 8 (Toff012 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q24 ∷
   rw 8 q30 ∷
   rw⁻ 7 q24 ∷
   re 8 3 (CS03 ∷ []) ∷
   re 6 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 13 q26 ∷
   rw 12 q27 ∷
   rw 11 q28 ∷
   rw 10 q29 ∷
   rw 9 q25 ∷
   rw 8 q29 ∷
   rw 7 q30 ∷
   rw 6 q27 ∷
   rw 7 q31 ∷
   re 7 8 (Toff012 ∷ []) ∷
   rw 5 q27 ∷
   rw 4 q32 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q24 ∷
   rw 4 q25 ∷
   rw⁻ 3 q24 ∷
   re 4 3 (CS03⁻ ∷ []) ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 9 q26 ∷
   rw 8 q27 ∷
   rw 7 q28 ∷
   rw 6 q29 ∷
   rw 5 q25 ∷
   rw 4 q29 ∷
   rw 3 q30 ∷
   rw 2 q27 ∷
   rw 3 q31 ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q24 ∷
   rw 2 q30 ∷
   rw⁻ 1 q24 ∷
   re 2 3 (CS03 ∷ []) ∷
   re 0 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 7 q26 ∷
   rw 6 q27 ∷
   rw 5 q28 ∷
   rw 4 q29 ∷
   rw 3 q25 ∷
   rw 2 q29 ∷
   rw 1 q30 ∷
   rw 0 q27 ∷
   rw 1 q31 ∷
   re 1 8 (Toff012 ∷ []) ∷
   rw 1 q33 ∷
   rw 0 q34 ∷
   rw 1 q35 ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 2 q35 ∷
   rw 3 q36 ∷
   rw 4 q37 ∷
   rw 5 q38 ∷
   rw 6 q37 ∷
   rw 7 q39 ∷
   rw 8 q35 ∷
   rw 9 q40 ∷
   rw 2 q41 ∷
   re 2 8 (Toff102 ∷ []) ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q24 ∷
   rw 4 q39 ∷
   rw 5 q24 ∷
   re 3 3 (CS13 ∷ []) ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 4 q35 ∷
   rw 5 q36 ∷
   rw 6 q37 ∷
   rw 7 q38 ∷
   rw 8 q37 ∷
   rw 9 q39 ∷
   rw 10 q35 ∷
   rw 11 q40 ∷
   rw 4 q41 ∷
   re 4 8 (Toff102 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q24 ∷
   rw 6 q42 ∷
   rw 7 q24 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw 6 q43 ∷
   rw 7 q44 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q24 ∷
   rw 9 q39 ∷
   rw 10 q24 ∷
   re 8 3 (CS13 ∷ []) ∷
   re 10 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 9 q35 ∷
   rw 10 q36 ∷
   rw 11 q37 ∷
   rw 12 q38 ∷
   rw 13 q37 ∷
   rw 14 q39 ∷
   rw 15 q35 ∷
   rw 16 q40 ∷
   rw 9 q41 ∷
   re 9 8 (Toff102 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q24 ∷
   rw 11 q42 ∷
   rw 12 q24 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   re 12 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 11 q35 ∷
   rw 12 q36 ∷
   rw 13 q37 ∷
   rw 14 q38 ∷
   rw 15 q37 ∷
   rw 16 q39 ∷
   rw 17 q35 ∷
   rw 18 q40 ∷
   rw 11 q41 ∷
   re 11 8 (Toff102 ∷ []) ∷
   rw 12 q45 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = eqn (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡1⟩-3)
  q47 : Eqn
  q47 = eqn (X3 ∷ CS13⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q48 : Eqn
  q48 = eqn (X3 ∷ CK31⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q49 : Eqn
  q49 = eqn (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q50 : Eqn
  q50 = eqn (X3 ∷ CK31 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) (lem-pass-X3-CK31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q51 : Eqn
  q51 = eqn (X3 ∷ CS13 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) (lem-pass-X3-CS31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0)
  q52 : Eqn
  q52 = eqn (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡1⟩-3

-- pass [X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X3] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 7 steps
lem-pass-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ [])
  (rw 0 q46 ∷
   rw 15 q47 ∷
   rw 12 q48 ∷
   rw 6 q49 ∷
   rw 3 q50 ∷
   rw 0 q51 ∷
   rw⁻ 8 q52 ∷ []) Eq.refl
