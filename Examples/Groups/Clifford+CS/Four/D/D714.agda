{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD714 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D714 (W : Ws) (Sᴰ : SD714) where

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
  lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 88
  lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 0 Sᴰ
  lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 869
  lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 1 Sᴰ
  lem-pass-X3-CKd31-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 1051
  lem-pass-X3-CKd31-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 2 Sᴰ
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 1131
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 3 Sᴰ
  lem-S2-at1023 : St 1918
  lem-S2-at1023 = pickᴰ 4 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2 : St 2051
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2 = pickᴰ 5 Sᴰ
  lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 2034
  lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 6 Sᴰ
  lem-pass-X2-CKd20-X2-vs-TOFF012-CS03-TOFF012-CSd03 : St 2052
  lem-pass-X2-CKd20-X2-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 7 Sᴰ
  lem-pass-X3-CK30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2036
  lem-pass-X3-CK30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 8 Sᴰ
  lem-pass-X3-CK31-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2045
  lem-pass-X3-CK31-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 9 Sᴰ
  lem-pass-X3-CKd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2037
  lem-pass-X3-CKd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 10 Sᴰ
  lem-pass-X3-CKd31-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2046
  lem-pass-X3-CKd31-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 11 Sᴰ
  lem-pass-X3-CS30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2039
  lem-pass-X3-CS30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 12 Sᴰ
  lem-pass-X3-CS31-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2047
  lem-pass-X3-CS31-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 13 Sᴰ
  lem-pass-X3-CS31-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2048
  lem-pass-X3-CS31-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 14 Sᴰ
  lem-pass-X3-CSd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2042
  lem-pass-X3-CSd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 15 Sᴰ
  lem-pass-X3-CSd31-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2050
  lem-pass-X3-CSd31-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 16 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 : St 2053
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 = pickᴰ 17 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS13 : St 2054
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS13 = pickᴰ 18 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd13 : St 2055
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd13 = pickᴰ 19 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2 : St 2056
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2 = pickᴰ 20 Sᴰ
  lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : St 2057
  lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = pickᴰ 21 Sᴰ
  lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 2058
  lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 22 Sᴰ
  lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 2059
  lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 23 Sᴰ
  lem-pass-X3-CSd31-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2060
  lem-pass-X3-CSd31-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 24 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = wE 7 W
  q4 : Eqn
  q4 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q5 : Eqn
  q5 = wE 257 W
  q6 : Eqn
  q6 = wE 27 W
  q7 : Eqn
  q7 = wE 31 W
  q8 : Eqn
  q8 = wE 2016 W
  q9 : Eqn
  q9 = wE 76 W
  q10 : Eqn
  q10 = wE 258 W
  q11 : Eqn
  q11 = wE 29 W
  q12 : Eqn
  q12 = sE 2051 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2
  q13 : Eqn
  q13 = wE 2017 W

-- pass [X2 TOFF012 CS03 TOFF012 CSd03 X2] [CS03 TOFF012 CSd03 TOFF012]: 65 steps
lem-pass-X2-TOFF012-CS03-TOFF012-CSd03-X2-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-TOFF012-CS03-TOFF012-CSd03-X2-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ [])
  (rw 7 q1 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q2 ∷
   rw 7 q3 ∷
   rw⁻ 6 q2 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 6 q5 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q2 ∷
   rw 6 q6 ∷
   rw 7 q2 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q4 ∷
   rw 7 q7 ∷
   rw 6 q8 ∷
   rw 11 q1 ∷
   re 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q2 ∷
   rw 11 q9 ∷
   rw⁻ 10 q2 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q4 ∷
   rw 10 q10 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q2 ∷
   rw 10 q11 ∷
   rw 11 q2 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   rw 10 q4 ∷
   rw 11 q7 ∷
   rw 10 q8 ∷
   rw 1 q12 ∷
   rw 2 q1 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q2 ∷
   rw 2 q3 ∷
   rw⁻ 1 q2 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 0 q4 ∷
   rw 1 q5 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 q2 ∷
   rw 1 q6 ∷
   rw 2 q2 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 1 q4 ∷
   rw 2 q7 ∷
   rw 1 q13 ∷
   rw 4 q1 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q2 ∷
   rw 4 q9 ∷
   rw⁻ 3 q2 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 3 q10 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q2 ∷
   rw 3 q11 ∷
   rw 4 q2 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q4 ∷
   rw 4 q7 ∷
   rw 3 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = wE 1 W
  q15 : Eqn
  q15 = wE 1357 W
  q16 : Eqn
  q16 = wE 3 W
  q17 : Eqn
  q17 = wE 45 W
  q18 : Eqn
  q18 = wE 231 W
  q19 : Eqn
  q19 = sE 2052 lem-pass-X2-CKd20-X2-vs-TOFF012-CS03-TOFF012-CSd03
  q20 : Eqn
  q20 = wE 1358 W
  q21 : Eqn
  q21 = wE 227 W
  q22 : Eqn
  q22 = wE 1342 W

-- pass [X2 CKd20 X2] [CS03 TOFF012 CSd03 TOFF012]: 33 steps
lem-pass-X2-CKd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X2 ∷ CK20⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  (rw 0 q14 ∷
   rw 1 q15 ∷
   rw 2 q14 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 3 q14 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q16 ∷
   rw 1 q17 ∷
   rw 2 q14 ∷
   rw 3 q18 ∷
   rw 4 q14 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 5 q14 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q16 ∷
   rw 3 q17 ∷
   rw⁻ 4 q19 ∷
   rw 12 q14 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q16 ∷
   re 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q16 ∷
   rw 11 q20 ∷
   rw 10 q16 ∷
   rw 9 q21 ∷
   rw 10 q14 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q16 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q16 ∷
   rw 9 q22 ∷
   rw 8 q16 ∷
   rw 7 q21 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = wE 2102 W
  q24 : Eqn
  q24 = sE 1131 lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q25 : Eqn
  q25 = sE 2034 lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q26 : Eqn
  q26 = wE 2103 W

-- pass [X2 CSd20 X2] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 5 steps
lem-pass-X2-CSd20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X2 ∷ CS02⁻ ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  (rw 0 q23 ∷
   rw 8 q24 ∷
   rw 5 q25 ∷
   rw 2 q24 ∷
   rw 6 q26 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = wE 2045 W
  q28 : Eqn
  q28 = wE 2046 W

-- pass [X2 CK20 X2] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 7 steps
lem-pass-X2-CK20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK20-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X2 ∷ CK20 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ [])
  (rw 0 q27 ∷
   rw 14 q25 ∷
   rw 11 q24 ∷
   rw 8 q24 ∷
   rw 5 q25 ∷
   rw 2 q24 ∷
   rw 6 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 2115 W
  q30 : Eqn
  q30 = wE 2116 W
  q31 : Eqn
  q31 = sE 2059 lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q32 : Eqn
  q32 = sE 869 lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q33 : Eqn
  q33 = wE 2117 W

-- ca-split Gad(t=1, W=(), d=SK, e=1) 2: 5 steps
lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-2 : ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CK21 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-2 = derive (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (CS12 ∷ CK21 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ [])
  (rw 0 q29 ∷
   rw 12 q30 ∷
   rw 5 q31 ∷
   rw 2 q32 ∷
   rw 6 q33 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q35 : Eqn
  q35 = wE 140 W
  q36 : Eqn
  q36 = wE 1495 W
  q37 : Eqn
  q37 = wE 142 W
  q38 : Eqn
  q38 = wE 1413 W

-- pass [X2 CK20 X2] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 25 steps
lem-pass-X2-CK20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (X2 ∷ CK20 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ [])
  (rw 4 q1 ∷
   rw⁻ 3 q34 ∷
   rw⁻ 2 q4 ∷
   rw 1 q35 ∷
   rw⁻ 0 q4 ∷
   rw 1 q36 ∷
   rw 0 q34 ∷
   rw 1 q4 ∷
   rw 2 q37 ∷
   rw 3 q4 ∷
   rw 4 q7 ∷
   rw 1 q38 ∷
   rw 1 q25 ∷
   rw 5 q38 ∷
   rw 9 q1 ∷
   rw⁻ 8 q34 ∷
   rw⁻ 7 q4 ∷
   rw 6 q35 ∷
   rw⁻ 5 q4 ∷
   rw 6 q36 ∷
   rw 5 q34 ∷
   rw 6 q4 ∷
   rw 7 q37 ∷
   rw 8 q4 ∷
   rw 9 q7 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = wE 173 W
  q40 : Eqn
  q40 = wE 1962 W
  q41 : Eqn
  q41 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q42 : Eqn
  q42 = wE 175 W
  q43 : Eqn
  q43 = eqn (Toff012 ∷ X3 ∷ []) (X3 ∷ Toff012 ∷ []) (low₃-comm (Toff) (X))
  q44 : Eqn
  q44 = wE 1963 W
  q45 : Eqn
  q45 = eqn (S0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑)))
  q46 : Eqn
  q46 = eqn (S0 ∷ X2 ∷ []) (X2 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑)))
  q47 : Eqn
  q47 = eqn (S0⁻ ∷ X2 ∷ []) (X2 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑)))
  q48 : Eqn
  q48 = sE 2053 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2
  q49 : Eqn
  q49 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q50 : Eqn
  q50 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q51 : Eqn
  q51 = eqn (S0⁻ ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑ ↑)))
  q52 : Eqn
  q52 = wE 1964 W
  q53 : Eqn
  q53 = wE 2018 W

-- pass [X2 X3 TOFF012 CS03 TOFF012 CSd03 X2 X3] [CS03 TOFF012 CSd03 TOFF012]: 139 steps
lem-pass-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ [])
  (rw 9 q14 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q16 ∷
   rw 7 q39 ∷
   rw 8 q40 ∷
   rw⁻ 7 q41 ∷
   rw 10 q14 ∷
   re 8 3 (CS03⁻ ∷ []) ∷
   rw 9 q42 ∷
   rw 10 q16 ∷
   rw⁻ 9 q43 ∷
   rw 12 q14 ∷
   re 11 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q16 ∷
   rw 10 q39 ∷
   rw 11 q44 ∷
   rw⁻ 10 q45 ∷
   rw 13 q14 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q42 ∷
   rw 13 q16 ∷
   rw⁻ 12 q43 ∷
   rw⁻ 6 q46 ∷
   rw 9 q1 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q2 ∷
   rw 9 q9 ∷
   rw⁻ 8 q2 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q4 ∷
   rw 8 q10 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   rw 8 q11 ∷
   rw 9 q2 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw 8 q4 ∷
   rw 9 q7 ∷
   rw 8 q8 ∷
   rw⁻ 11 q47 ∷
   rw 14 q1 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q2 ∷
   rw 14 q3 ∷
   rw⁻ 13 q2 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw⁻ 12 q4 ∷
   rw 13 q5 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q2 ∷
   rw 13 q6 ∷
   rw 14 q2 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q4 ∷
   rw 14 q7 ∷
   rw 13 q8 ∷
   rw 2 q48 ∷
   rw⁻ 1 q49 ∷
   rw 4 q14 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q16 ∷
   rw 2 q39 ∷
   rw 3 q44 ∷
   rw⁻ 2 q45 ∷
   rw 5 q14 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q42 ∷
   rw 5 q16 ∷
   rw⁻ 4 q50 ∷
   rw⁻ 5 q43 ∷
   rw⁻ 6 q50 ∷
   rw⁻ 7 q51 ∷
   rw 10 q14 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q16 ∷
   rw 8 q39 ∷
   rw 9 q40 ∷
   rw⁻ 8 q41 ∷
   rw 11 q14 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   rw 10 q42 ∷
   rw 11 q16 ∷
   rw⁻ 10 q50 ∷
   rw⁻ 11 q43 ∷
   rw⁻ 12 q50 ∷
   rw⁻ 0 q46 ∷
   rw⁻ 1 q47 ∷
   rw 4 q1 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q2 ∷
   rw 4 q3 ∷
   rw⁻ 3 q2 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 3 q5 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q2 ∷
   rw 3 q6 ∷
   rw 4 q2 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q4 ∷
   rw 4 q7 ∷
   rw 3 q13 ∷
   rw⁻ 4 q47 ∷
   rw⁻ 5 q46 ∷
   rw 8 q1 ∷
   re 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q2 ∷
   rw 8 q9 ∷
   rw⁻ 7 q2 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 7 q10 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q2 ∷
   rw 7 q11 ∷
   rw 8 q2 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   rw 7 q4 ∷
   rw 8 q7 ∷
   rw 7 q13 ∷
   rw 3 q14 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q16 ∷
   rw 1 q45 ∷
   rw 0 q41 ∷
   rw 1 q52 ∷
   rw 2 q14 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 1 q16 ∷
   rw 5 q14 ∷
   re 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q16 ∷
   rw 3 q41 ∷
   rw 2 q45 ∷
   rw 3 q53 ∷
   rw 4 q14 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q16 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = wE 2111 W
  q55 : Eqn
  q55 = sE 2048 lem-pass-X3-CS31-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q56 : Eqn
  q56 = wE 2112 W

-- pass [CS31] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 3 steps
lem-pass-CS31-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (CS13 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS31-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (CS13 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS13 ∷ [])
  (rw 0 q54 ∷
   rw 1 q55 ∷
   rw 5 q56 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = wE 1462 W
  q58 : Eqn
  q58 = sE 2039 lem-pass-X3-CS30-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q59 : Eqn
  q59 = wE 1463 W

-- pass [CS30] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 23 steps
lem-pass-CS30-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (CS03 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS30-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (CS03 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ [])
  (rw 2 q14 ∷
   rw 1 q39 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q16 ∷
   rw 1 q57 ∷
   rw 0 q42 ∷
   rw 1 q42 ∷
   rw 4 q14 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q42 ∷
   rw 4 q16 ∷
   rw 1 q58 ∷
   rw 9 q14 ∷
   rw 8 q39 ∷
   rw 7 q39 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q16 ∷
   rw 5 q39 ∷
   rw 6 q59 ∷
   rw 5 q42 ∷
   rw 8 q14 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q16 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = wE 1407 W
  q61 : Eqn
  q61 = sE 2036 lem-pass-X3-CK30-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q62 : Eqn
  q62 = wE 1408 W

-- pass [CK30] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 23 steps
lem-pass-CK30-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (CK30 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CK30-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (CK30 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK30 ∷ [])
  (rw 2 q14 ∷
   rw 1 q39 ∷
   re 0 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 2 q16 ∷
   rw 1 q60 ∷
   rw 0 q42 ∷
   rw 1 q42 ∷
   rw 4 q14 ∷
   re 2 3 (CK30 ∷ []) ∷
   rw 3 q42 ∷
   rw 4 q16 ∷
   rw 1 q61 ∷
   rw 9 q14 ∷
   rw 8 q39 ∷
   rw 7 q39 ∷
   re 6 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 8 q16 ∷
   rw 5 q39 ∷
   rw 6 q62 ∷
   rw 5 q42 ∷
   rw 8 q14 ∷
   re 6 3 (CK30 ∷ []) ∷
   rw 7 q16 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = wE 1464 W
  q64 : Eqn
  q64 = sE 2037 lem-pass-X3-CKd30-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q65 : Eqn
  q65 = wE 1465 W

-- pass [CKd30] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 23 steps
lem-pass-CKd30-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (CK30⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK30⁻ ∷ []) ⟫ʷ
lem-pass-CKd30-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (CK30⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK30⁻ ∷ [])
  (rw 2 q14 ∷
   rw 1 q39 ∷
   re 0 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q16 ∷
   rw 1 q63 ∷
   rw 0 q42 ∷
   rw 1 q42 ∷
   rw 4 q14 ∷
   re 2 3 (CK30⁻ ∷ []) ∷
   rw 3 q42 ∷
   rw 4 q16 ∷
   rw 1 q64 ∷
   rw 9 q14 ∷
   rw 8 q39 ∷
   rw 7 q39 ∷
   re 6 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q16 ∷
   rw 5 q39 ∷
   rw 6 q65 ∷
   rw 5 q42 ∷
   rw 8 q14 ∷
   re 6 3 (CK30⁻ ∷ []) ∷
   rw 7 q16 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = wE 1466 W
  q67 : Eqn
  q67 = sE 2042 lem-pass-X3-CSd30-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q68 : Eqn
  q68 = wE 1467 W

-- pass [CSd30] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 23 steps
lem-pass-CSd30-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (CS03⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd30-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (CS03⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03⁻ ∷ [])
  (rw 2 q14 ∷
   rw 1 q39 ∷
   re 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q16 ∷
   rw 1 q66 ∷
   rw 0 q42 ∷
   rw 1 q42 ∷
   rw 4 q14 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q42 ∷
   rw 4 q16 ∷
   rw 1 q67 ∷
   rw 9 q14 ∷
   rw 8 q39 ∷
   rw 7 q39 ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q16 ∷
   rw 5 q39 ∷
   rw 6 q68 ∷
   rw 5 q42 ∷
   rw 8 q14 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   rw 7 q16 ∷ []) Eq.refl

private
  q69 : Eqn
  q69 = wE 2118 W
  q70 : Eqn
  q70 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q71 : Eqn
  q71 = wE 1501 W
  q72 : Eqn
  q72 = sE 2050 lem-pass-X3-CSd31-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q73 : Eqn
  q73 = eqn (K0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑)))
  q74 : Eqn
  q74 = wE 1502 W

-- pass [X3 CSd31 X3] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 33 steps
lem-pass-X3-CSd31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X3 ∷ CS13⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ [])
  (rw 0 q69 ∷
   rw 5 q14 ∷
   rw 4 q70 ∷
   rw 3 q41 ∷
   rw 2 q39 ∷
   re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q16 ∷
   rw 0 q39 ∷
   rw 1 q71 ∷
   rw⁻ 0 q41 ∷
   rw⁻ 1 q70 ∷
   rw 2 q42 ∷
   rw 5 q14 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw 4 q42 ∷
   rw 5 q16 ∷
   rw 2 q72 ∷
   rw 11 q14 ∷
   rw 10 q45 ∷
   rw 9 q73 ∷
   rw 8 q39 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q16 ∷
   rw 6 q39 ∷
   rw 7 q74 ∷
   rw⁻ 6 q73 ∷
   rw⁻ 7 q45 ∷
   rw 8 q42 ∷
   rw 11 q14 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw 10 q42 ∷
   rw 11 q16 ∷
   rw 8 q69 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = wE 1834 W
  q76 : Eqn
  q76 = wE 1503 W
  q77 : Eqn
  q77 = sE 2046 lem-pass-X3-CKd31-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q78 : Eqn
  q78 = wE 1504 W

-- pass [X3 CKd31 X3] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 33 steps
lem-pass-X3-CKd31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X3 ∷ CK31⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ [])
  (rw 0 q75 ∷
   rw 5 q14 ∷
   rw 4 q70 ∷
   rw 3 q41 ∷
   rw 2 q39 ∷
   re 1 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q16 ∷
   rw 0 q39 ∷
   rw 1 q76 ∷
   rw⁻ 0 q41 ∷
   rw⁻ 1 q70 ∷
   rw 2 q42 ∷
   rw 5 q14 ∷
   re 3 3 (CK31⁻ ∷ []) ∷
   rw 4 q42 ∷
   rw 5 q16 ∷
   rw 2 q77 ∷
   rw 11 q14 ∷
   rw 10 q45 ∷
   rw 9 q73 ∷
   rw 8 q39 ∷
   re 7 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q16 ∷
   rw 6 q39 ∷
   rw 7 q78 ∷
   rw⁻ 6 q73 ∷
   rw⁻ 7 q45 ∷
   rw 8 q42 ∷
   rw 11 q14 ∷
   re 9 3 (CK31⁻ ∷ []) ∷
   rw 10 q42 ∷
   rw 11 q16 ∷
   rw 8 q75 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = wE 1534 W
  q80 : Eqn
  q80 = wE 1505 W
  q81 : Eqn
  q81 = sE 2045 lem-pass-X3-CK31-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q82 : Eqn
  q82 = wE 1506 W

-- pass [X3 CK31 X3] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 33 steps
lem-pass-X3-CK31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X3 ∷ CK31 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ [])
  (rw 0 q79 ∷
   rw 5 q14 ∷
   rw 4 q70 ∷
   rw 3 q41 ∷
   rw 2 q39 ∷
   re 1 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 3 q16 ∷
   rw 0 q39 ∷
   rw 1 q80 ∷
   rw⁻ 0 q41 ∷
   rw⁻ 1 q70 ∷
   rw 2 q42 ∷
   rw 5 q14 ∷
   re 3 3 (CK31 ∷ []) ∷
   rw 4 q42 ∷
   rw 5 q16 ∷
   rw 2 q81 ∷
   rw 11 q14 ∷
   rw 10 q45 ∷
   rw 9 q73 ∷
   rw 8 q39 ∷
   re 7 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 9 q16 ∷
   rw 6 q39 ∷
   rw 7 q82 ∷
   rw⁻ 6 q73 ∷
   rw⁻ 7 q45 ∷
   rw 8 q42 ∷
   rw 11 q14 ∷
   re 9 3 (CK31 ∷ []) ∷
   rw 10 q42 ∷
   rw 11 q16 ∷
   rw 8 q79 ∷ []) Eq.refl

private
  q83 : Eqn
  q83 = wE 2119 W
  q84 : Eqn
  q84 = wE 1507 W
  q85 : Eqn
  q85 = sE 2047 lem-pass-X3-CS31-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q86 : Eqn
  q86 = wE 1508 W

-- pass [X3 CS31 X3] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 33 steps
lem-pass-X3-CS31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS31-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X3 ∷ CS13 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ [])
  (rw 0 q83 ∷
   rw 5 q14 ∷
   rw 4 q70 ∷
   rw 3 q41 ∷
   rw 2 q39 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q16 ∷
   rw 0 q39 ∷
   rw 1 q84 ∷
   rw⁻ 0 q41 ∷
   rw⁻ 1 q70 ∷
   rw 2 q42 ∷
   rw 5 q14 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw 4 q42 ∷
   rw 5 q16 ∷
   rw 2 q85 ∷
   rw 11 q14 ∷
   rw 10 q45 ∷
   rw 9 q73 ∷
   rw 8 q39 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q16 ∷
   rw 6 q39 ∷
   rw 7 q86 ∷
   rw⁻ 6 q73 ∷
   rw⁻ 7 q45 ∷
   rw 8 q42 ∷
   rw 11 q14 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 10 q42 ∷
   rw 11 q16 ∷
   rw 8 q83 ∷ []) Eq.refl

private
  q87 : Eqn
  q87 = wE 1476 W
  q88 : Eqn
  q88 = wE 1477 W

-- pass [CK21] [X2 TOFF102 CS13 TOFF102 CSd13 X2]: 3 steps
lem-pass-CK21-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : ⟪ (CK21 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK21 ∷ []) ⟫ʷ
lem-pass-CK21-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = derive (CK21 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK21 ∷ [])
  (rw 0 q87 ∷
   rw 1 q31 ∷
   rw 5 q88 ∷ []) Eq.refl

private
  q89 : Eqn
  q89 = wE 1496 W

-- pass [X2 CK21 X2] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 5 steps
lem-pass-X2-CK21-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (X2 ∷ CK21 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK21-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (X2 ∷ CK21 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ X2 ∷ CK21 ∷ X2 ∷ [])
  (rw 0 q36 ∷
   rw 1 q89 ∷
   rw 1 q31 ∷
   rw 5 q89 ∷
   rw 5 q36 ∷ []) Eq.refl

private
  q90 : Eqn
  q90 = sE 2058 lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [X1 CK10 X1] [CS03 TOFF012 CSd03 TOFF012]: 33 steps
lem-pass-X1-CK10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X1 ∷ CK10 ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CK10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X1 ∷ CK10 ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CK10 ∷ X1 ∷ [])
  (rw 0 q14 ∷
   rw 1 q15 ∷
   rw 2 q14 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 3 q14 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q16 ∷
   rw 1 q17 ∷
   rw 2 q14 ∷
   rw 3 q18 ∷
   rw 4 q14 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 5 q14 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q16 ∷
   rw 3 q17 ∷
   rw⁻ 4 q90 ∷
   rw 12 q14 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q16 ∷
   re 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q16 ∷
   rw 11 q20 ∷
   rw 10 q16 ∷
   rw 9 q21 ∷
   rw 10 q14 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q16 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q16 ∷
   rw 9 q22 ∷
   rw 8 q16 ∷
   rw 7 q21 ∷ []) Eq.refl

private
  q91 : Eqn
  q91 = sE 1918 lem-S2-at1023
  q92 : Eqn
  q92 = sE 2057 lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3
  q93 : Eqn
  q93 = sE 1918 lem-S2-at1023

-- pass [TOFF102 CS13 TOFF102 CSd13] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 3 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw 0 q91 ∷
   rw 0 q92 ∷
   rw⁻ 6 q93 ∷ []) Eq.refl

private
  q94 : Eqn
  q94 = wE 2120 W
  q95 : Eqn
  q95 = sE 88 lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q96 : Eqn
  q96 = wE 2121 W

-- pass [X3 CSd31 X3] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 5 steps
lem-pass-X3-CSd31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (X3 ∷ CS13⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ [])
  (rw 0 q94 ∷
   rw 8 q55 ∷
   rw 5 q95 ∷
   rw 2 q55 ∷
   rw 6 q96 ∷ []) Eq.refl

private
  q97 : Eqn
  q97 = wE 2122 W
  q98 : Eqn
  q98 = sE 1051 lem-pass-X3-CKd31-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q99 : Eqn
  q99 = wE 2123 W

-- pass [X3 CKd31 X3] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 7 steps
lem-pass-X3-CKd31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (X3 ∷ CK31⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ [])
  (rw 0 q97 ∷
   rw 14 q98 ∷
   rw 11 q55 ∷
   rw 8 q55 ∷
   rw 5 q95 ∷
   rw 2 q55 ∷
   rw 6 q99 ∷ []) Eq.refl

private
  q100 : Eqn
  q100 = wE 2124 W
  q101 : Eqn
  q101 = wE 2125 W

-- pass [X3 CK31 X3] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 7 steps
lem-pass-X3-CK31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (X3 ∷ CK31 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ [])
  (rw 0 q100 ∷
   rw 14 q95 ∷
   rw 11 q55 ∷
   rw 8 q55 ∷
   rw 5 q95 ∷
   rw 2 q55 ∷
   rw 6 q101 ∷ []) Eq.refl

private
  q102 : Eqn
  q102 = wE 2126 W
  q103 : Eqn
  q103 = sE 2060 lem-pass-X3-CSd31-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q104 : Eqn
  q104 = wE 2127 W

-- pass [X3 CS31 X3] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 5 steps
lem-pass-X3-CS31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS31-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (X3 ∷ CS13 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ [])
  (rw 0 q102 ∷
   rw 8 q103 ∷
   rw 5 q98 ∷
   rw 2 q103 ∷
   rw 6 q104 ∷ []) Eq.refl

private
  q105 : Eqn
  q105 = sE 2056 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2
  q106 : Eqn
  q106 = sE 2054 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS13
  q107 : Eqn
  q107 = sE 2055 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [X2 TOFF102 X2 CS13 X2 TOFF102 X2 CSd13]: 4 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2-CS13-X2-TOFF102-X2-CSd13 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw 0 q105 ∷
   rw 3 q106 ∷
   rw 4 q105 ∷
   rw 7 q107 ∷ []) Eq.refl

private
  q108 : Eqn
  q108 = wE 871 W
  q109 : Eqn
  q109 = wE 2128 W
  q110 : Eqn
  q110 = sE 2059 lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q111 : Eqn
  q111 = wE 389 W
  q112 : Eqn
  q112 = wE 2129 W

-- pass [X2 CKd21 X2] [TOFF102 CS13 TOFF102 CSd13]: 7 steps
lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = derive (X2 ∷ CK21⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  (rw 7 q108 ∷
   rw 8 q109 ∷
   rw 9 q108 ∷
   rw⁻ 3 q110 ∷
   rw 2 q111 ∷
   rw 1 q112 ∷
   rw 0 q111 ∷ []) Eq.refl

private
  q113 : Eqn
  q113 = wE 2130 W
  q114 : Eqn
  q114 = wE 2131 W

-- pass [X2 CSd21 X2] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 5 steps
lem-pass-X2-CSd21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (X2 ∷ CS12⁻ ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  (rw 0 q113 ∷
   rw 8 q32 ∷
   rw 5 q31 ∷
   rw 2 q32 ∷
   rw 6 q114 ∷ []) Eq.refl

private
  q115 : Eqn
  q115 = wE 2132 W
  q116 : Eqn
  q116 = wE 2133 W

-- pass [X2 CK21 X2] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 7 steps
lem-pass-X2-CK21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (X2 ∷ CK21 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (X2 ∷ CK21 ∷ X2 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ [])
  (rw 0 q115 ∷
   rw 14 q31 ∷
   rw 11 q32 ∷
   rw 8 q32 ∷
   rw 5 q31 ∷
   rw 2 q32 ∷
   rw 6 q116 ∷ []) Eq.refl
