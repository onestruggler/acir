{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD713 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D713 (W : Ws) (Sᴰ : SD713) where

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
  lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 840
  lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 1 Sᴰ
  lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 1146
  lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 2 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-S0-CSd03 : St 2044
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-S0-CSd03 = pickᴰ 3 Sᴰ
  lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 2034
  lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 4 Sᴰ
  lem-pass-X3-CK30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2036
  lem-pass-X3-CK30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 5 Sᴰ
  lem-pass-X3-CK31-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2045
  lem-pass-X3-CK31-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 6 Sᴰ
  lem-pass-X3-CKd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2037
  lem-pass-X3-CKd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 7 Sᴰ
  lem-pass-X3-CKd31-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2046
  lem-pass-X3-CKd31-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 8 Sᴰ
  lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2038
  lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 9 Sᴰ
  lem-pass-X3-CS30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2039
  lem-pass-X3-CS30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 10 Sᴰ
  lem-pass-X3-CS31-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2047
  lem-pass-X3-CS31-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 11 Sᴰ
  lem-pass-X3-CS31-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2048
  lem-pass-X3-CS31-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 12 Sᴰ
  lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2049
  lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 13 Sᴰ
  lem-pass-X3-CSd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2042
  lem-pass-X3-CSd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 14 Sᴰ
  lem-pass-X3-CSd31-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2050
  lem-pass-X3-CSd31-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 15 Sᴰ
  lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 2043
  lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 16 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q3 : Eqn
  q3 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q4 : Eqn
  q4 = wE 2099 W
  q5 : Eqn
  q5 = wE 175 W
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = eqn (S0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑)))
  q8 : Eqn
  q8 = eqn (K0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑)))
  q9 : Eqn
  q9 = wE 2100 W
  q10 : Eqn
  q10 = sE 840 lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q11 : Eqn
  q11 = sE 2038 lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q12 : Eqn
  q12 = wE 173 W
  q13 : Eqn
  q13 = wE 2101 W

-- ca-split Gad(t=0, W=(), d=SK, e=-1) 3: 55 steps
lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-3 : ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CK30 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ []) ⟫ʷ
lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-3 = derive (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (CS03 ∷ CK30 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ [])
  (rw 2 q1 ∷
   rw 1 q2 ∷
   rw 0 q3 ∷
   rw 1 q4 ∷
   rw 2 q1 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CK30 ∷ []) ∷
   rw 2 q5 ∷
   rw 5 q1 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q5 ∷
   rw 5 q5 ∷
   rw 8 q1 ∷
   re 6 3 (CK30 ∷ []) ∷
   rw 7 q5 ∷
   rw 8 q6 ∷
   rw 14 q1 ∷
   rw 13 q7 ∷
   rw 12 q8 ∷
   rw 13 q9 ∷
   rw 12 q5 ∷
   rw 15 q1 ∷
   re 13 3 (CK30⁻ ∷ []) ∷
   rw 14 q5 ∷
   rw 15 q5 ∷
   rw 18 q1 ∷
   re 16 3 (CS03⁻ ∷ []) ∷
   rw 17 q5 ∷
   rw 20 q1 ∷
   re 18 3 (CK30⁻ ∷ []) ∷
   rw 21 q1 ∷
   re 19 3 (CS03⁻ ∷ []) ∷
   rw 20 q6 ∷
   rw 5 q10 ∷
   rw 2 q11 ∷
   rw 18 q1 ∷
   rw 17 q12 ∷
   re 16 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q6 ∷
   rw 15 q12 ∷
   rw 14 q12 ∷
   re 13 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q6 ∷
   rw 12 q12 ∷
   rw 11 q12 ∷
   re 10 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   rw 9 q12 ∷
   rw 8 q12 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 6 q12 ∷
   rw 7 q13 ∷
   rw 6 q6 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = wE 1962 W
  q15 : Eqn
  q15 = sE 2044 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-S0-CSd03
  q16 : Eqn
  q16 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q17 : Eqn
  q17 = wE 1963 W
  q18 : Eqn
  q18 = wE 1964 W

-- pass [X3 TOFF012 CS03 TOFF012 CSd03 X3] [CS03]: 31 steps
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-CS03 : ⟪ (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-CS03 = derive (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ []) (CS03 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 7 q1 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q12 ∷
   rw 6 q14 ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   rw 7 q5 ∷
   rw 8 q6 ∷
   rw 1 q15 ∷
   rw⁻ 0 q16 ∷
   rw 3 q1 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw 1 q12 ∷
   rw 2 q17 ∷
   rw⁻ 1 q7 ∷
   rw 4 q1 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q5 ∷
   rw 4 q6 ∷
   rw 3 q1 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw 1 q7 ∷
   rw 0 q3 ∷
   rw 1 q18 ∷
   rw 2 q1 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 1 q6 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = wE 1357 W
  q20 : Eqn
  q20 = wE 45 W
  q21 : Eqn
  q21 = wE 231 W
  q22 : Eqn
  q22 = sE 2043 lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q23 : Eqn
  q23 = wE 1358 W
  q24 : Eqn
  q24 = wE 227 W
  q25 : Eqn
  q25 = wE 1342 W

-- pass [X3 TOFF012 CS03 TOFF012 CSd03 X3] [CS03 TOFF012 CSd03 TOFF012]: 33 steps
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 0 q1 ∷
   rw 1 q19 ∷
   rw 2 q1 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q6 ∷
   rw 1 q20 ∷
   rw 2 q1 ∷
   rw 3 q21 ∷
   rw 4 q1 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 5 q1 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q6 ∷
   rw 3 q20 ∷
   rw⁻ 4 q22 ∷
   rw 15 q1 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q6 ∷
   re 13 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q6 ∷
   rw 14 q23 ∷
   rw 13 q6 ∷
   rw 12 q24 ∷
   rw 13 q1 ∷
   re 12 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q6 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q6 ∷
   rw 12 q25 ∷
   rw 11 q6 ∷
   rw 10 q24 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = wE 1466 W
  q27 : Eqn
  q27 = sE 2049 lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q28 : Eqn
  q28 = wE 1467 W

-- pass [CSd30] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 23 steps
lem-pass-CSd30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (CS03⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (CS03⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ [])
  (rw 2 q1 ∷
   rw 1 q12 ∷
   re 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q6 ∷
   rw 1 q26 ∷
   rw 0 q5 ∷
   rw 1 q5 ∷
   rw 4 q1 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q5 ∷
   rw 4 q6 ∷
   rw 1 q27 ∷
   rw 9 q1 ∷
   rw 8 q12 ∷
   rw 7 q12 ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q12 ∷
   rw 6 q28 ∷
   rw 5 q5 ∷
   rw 8 q1 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   rw 7 q6 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 2102 W
  q30 : Eqn
  q30 = wE 2103 W

-- pass [X3 CSd30 X3] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 49 steps
lem-pass-X3-CSd30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 5 q1 ∷
   rw 4 q2 ∷
   rw 3 q3 ∷
   rw 2 q12 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q12 ∷
   rw 1 q29 ∷
   rw⁻ 0 q3 ∷
   rw⁻ 1 q2 ∷
   rw 2 q5 ∷
   rw 5 q1 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q5 ∷
   rw 5 q5 ∷
   rw 8 q1 ∷
   re 6 3 (CK30 ∷ []) ∷
   rw 7 q5 ∷
   rw 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q5 ∷
   rw 11 q6 ∷
   rw 8 q11 ∷
   rw 5 q10 ∷
   rw 2 q11 ∷
   rw 17 q1 ∷
   rw 16 q7 ∷
   rw 15 q8 ∷
   rw 14 q12 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q6 ∷
   rw 12 q12 ∷
   rw 11 q12 ∷
   re 10 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   rw 9 q12 ∷
   rw 8 q12 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 6 q12 ∷
   rw 7 q30 ∷
   rw⁻ 6 q8 ∷
   rw⁻ 7 q7 ∷
   rw 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   rw 10 q5 ∷
   rw 11 q6 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = wE 2104 W
  q32 : Eqn
  q32 = sE 1146 lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q33 : Eqn
  q33 = wE 2105 W

-- pass [X3 CKd30 X3] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 67 steps
lem-pass-X3-CKd30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X3 ∷ CK30⁻ ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  (rw 5 q1 ∷
   rw 4 q2 ∷
   rw 3 q3 ∷
   rw 2 q12 ∷
   re 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q12 ∷
   rw 1 q31 ∷
   rw⁻ 0 q3 ∷
   rw⁻ 1 q2 ∷
   rw 2 q5 ∷
   rw 5 q1 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q5 ∷
   rw 5 q5 ∷
   rw 8 q1 ∷
   re 6 3 (CK30 ∷ []) ∷
   rw 7 q5 ∷
   rw 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q5 ∷
   rw 11 q5 ∷
   rw 14 q1 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q5 ∷
   rw 14 q5 ∷
   rw 17 q1 ∷
   re 15 3 (CK30⁻ ∷ []) ∷
   rw 16 q5 ∷
   rw 17 q6 ∷
   rw 14 q32 ∷
   rw 11 q11 ∷
   rw 8 q11 ∷
   rw 5 q10 ∷
   rw 2 q11 ∷
   rw 23 q1 ∷
   rw 22 q7 ∷
   rw 21 q8 ∷
   rw 20 q12 ∷
   re 19 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 21 q6 ∷
   rw 18 q12 ∷
   rw 17 q12 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q6 ∷
   rw 15 q12 ∷
   rw 14 q12 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q6 ∷
   rw 12 q12 ∷
   rw 11 q12 ∷
   re 10 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   rw 9 q12 ∷
   rw 8 q12 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 6 q12 ∷
   rw 7 q33 ∷
   rw⁻ 6 q8 ∷
   rw⁻ 7 q7 ∷
   rw 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (CK30⁻ ∷ []) ∷
   rw 10 q5 ∷
   rw 11 q6 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = wE 2045 W
  q35 : Eqn
  q35 = wE 2046 W

-- pass [X3 CK30 X3] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 67 steps
lem-pass-X3-CK30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X3 ∷ CK30 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  (rw 5 q1 ∷
   rw 4 q2 ∷
   rw 3 q3 ∷
   rw 2 q12 ∷
   re 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q12 ∷
   rw 1 q34 ∷
   rw⁻ 0 q3 ∷
   rw⁻ 1 q2 ∷
   rw 2 q5 ∷
   rw 5 q1 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q5 ∷
   rw 5 q5 ∷
   rw 8 q1 ∷
   re 6 3 (CK30 ∷ []) ∷
   rw 7 q5 ∷
   rw 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q5 ∷
   rw 11 q5 ∷
   rw 14 q1 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q5 ∷
   rw 14 q5 ∷
   rw 17 q1 ∷
   re 15 3 (CK30 ∷ []) ∷
   rw 16 q5 ∷
   rw 17 q6 ∷
   rw 14 q10 ∷
   rw 11 q11 ∷
   rw 8 q11 ∷
   rw 5 q10 ∷
   rw 2 q11 ∷
   rw 23 q1 ∷
   rw 22 q7 ∷
   rw 21 q8 ∷
   rw 20 q12 ∷
   re 19 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 21 q6 ∷
   rw 18 q12 ∷
   rw 17 q12 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q6 ∷
   rw 15 q12 ∷
   rw 14 q12 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q6 ∷
   rw 12 q12 ∷
   rw 11 q12 ∷
   re 10 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   rw 9 q12 ∷
   rw 8 q12 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 6 q12 ∷
   rw 7 q35 ∷
   rw⁻ 6 q8 ∷
   rw⁻ 7 q7 ∷
   rw 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (CK30 ∷ []) ∷
   rw 10 q5 ∷
   rw 11 q6 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = wE 2106 W
  q37 : Eqn
  q37 = wE 2107 W

-- pass [X3 CS30 X3] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 49 steps
lem-pass-X3-CS30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (X3 ∷ CS03 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  (rw 5 q1 ∷
   rw 4 q2 ∷
   rw 3 q3 ∷
   rw 2 q12 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q12 ∷
   rw 1 q36 ∷
   rw⁻ 0 q3 ∷
   rw⁻ 1 q2 ∷
   rw 2 q5 ∷
   rw 5 q1 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 4 q5 ∷
   rw 5 q5 ∷
   rw 8 q1 ∷
   re 6 3 (CK30⁻ ∷ []) ∷
   rw 7 q5 ∷
   rw 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   rw 10 q5 ∷
   rw 11 q6 ∷
   rw 8 q27 ∷
   rw 5 q32 ∷
   rw 2 q27 ∷
   rw 17 q1 ∷
   rw 16 q7 ∷
   rw 15 q8 ∷
   rw 14 q12 ∷
   re 13 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q6 ∷
   rw 12 q12 ∷
   rw 11 q12 ∷
   re 10 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   rw 9 q12 ∷
   rw 8 q12 ∷
   re 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 6 q12 ∷
   rw 7 q37 ∷
   rw⁻ 6 q8 ∷
   rw⁻ 7 q7 ∷
   rw 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q5 ∷
   rw 11 q6 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = wE 2108 W
  q39 : Eqn
  q39 = wE 2109 W
  q40 : Eqn
  q40 = sE 88 lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q41 : Eqn
  q41 = sE 2048 lem-pass-X3-CS31-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q42 : Eqn
  q42 = wE 2110 W

-- ca-split Gad(t=1, W=(), d=SK, e=1) 3: 5 steps
lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-3 : ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CK31 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ []) ⟫ʷ
lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-3 = derive (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (CS13 ∷ CK31 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ [])
  (rw 0 q38 ∷
   rw 12 q39 ∷
   rw 5 q40 ∷
   rw 2 q41 ∷
   rw 6 q42 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = wE 2111 W
  q44 : Eqn
  q44 = sE 2047 lem-pass-X3-CS31-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q45 : Eqn
  q45 = wE 2112 W

-- pass [CS31] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 3 steps
lem-pass-CS31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (CS13 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (CS13 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS13 ∷ [])
  (rw 0 q43 ∷
   rw 1 q44 ∷
   rw 5 q45 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = wE 1366 W
  q47 : Eqn
  q47 = sE 2045 lem-pass-X3-CK31-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q48 : Eqn
  q48 = wE 1367 W

-- pass [CK31] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 3 steps
lem-pass-CK31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (CK31 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK31 ∷ []) ⟫ʷ
lem-pass-CK31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (CK31 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK31 ∷ [])
  (rw 0 q46 ∷
   rw 1 q47 ∷
   rw 5 q48 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = wE 1940 W
  q50 : Eqn
  q50 = sE 2046 lem-pass-X3-CKd31-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q51 : Eqn
  q51 = wE 1941 W

-- pass [CKd31] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 3 steps
lem-pass-CKd31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (CK31⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK31⁻ ∷ []) ⟫ʷ
lem-pass-CKd31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (CK31⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK31⁻ ∷ [])
  (rw 0 q49 ∷
   rw 1 q50 ∷
   rw 5 q51 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = wE 2113 W
  q53 : Eqn
  q53 = sE 2050 lem-pass-X3-CSd31-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q54 : Eqn
  q54 = wE 2114 W

-- pass [CSd31] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 3 steps
lem-pass-CSd31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (CS13⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-CSd31-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (CS13⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS13⁻ ∷ [])
  (rw 0 q52 ∷
   rw 1 q53 ∷
   rw 5 q54 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = wE 1482 W
  q56 : Eqn
  q56 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q57 : Eqn
  q57 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q58 : Eqn
  q58 = wE 1483 W
  q59 : Eqn
  q59 = sE 2042 lem-pass-X3-CSd30-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q60 : Eqn
  q60 = eqn (S1⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (Swap))
  q61 : Eqn
  q61 = eqn (K1⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K1⁻ ∷ []) (low-comm (((K • iI) ↑)) (Swap))
  q62 : Eqn
  q62 = wE 1484 W

-- pass [X3 CSd30 X3] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 53 steps
lem-pass-X3-CSd30-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 3 q1 ∷
   rw 2 q12 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q12 ∷
   rw 1 q55 ∷
   rw 0 q5 ∷
   rw 3 q1 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q5 ∷
   rw 3 q6 ∷
   rw 5 q1 ∷
   rw 4 q56 ∷
   rw 3 q57 ∷
   rw 2 q12 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q12 ∷
   rw 1 q58 ∷
   rw⁻ 0 q57 ∷
   rw⁻ 1 q56 ∷
   rw 2 q5 ∷
   rw 5 q1 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 2 q59 ∷
   rw 11 q1 ∷
   rw 10 q60 ∷
   rw 9 q61 ∷
   rw 8 q12 ∷
   re 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 6 q12 ∷
   rw 7 q62 ∷
   rw⁻ 6 q61 ∷
   rw⁻ 7 q60 ∷
   rw 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   rw 10 q5 ∷
   rw 11 q6 ∷
   rw 11 q1 ∷
   rw 10 q12 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   rw 8 q12 ∷
   rw 9 q55 ∷
   rw 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   rw 10 q5 ∷
   rw 11 q6 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = wE 1485 W
  q64 : Eqn
  q64 = wE 1486 W
  q65 : Eqn
  q65 = sE 2037 lem-pass-X3-CKd30-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q66 : Eqn
  q66 = wE 1487 W

-- pass [X3 CKd30 X3] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 53 steps
lem-pass-X3-CKd30-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (X3 ∷ CK30⁻ ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  (rw 3 q1 ∷
   rw 2 q12 ∷
   re 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q12 ∷
   rw 1 q63 ∷
   rw 0 q5 ∷
   rw 3 q1 ∷
   re 1 3 (CK30⁻ ∷ []) ∷
   rw 2 q5 ∷
   rw 3 q6 ∷
   rw 5 q1 ∷
   rw 4 q56 ∷
   rw 3 q57 ∷
   rw 2 q12 ∷
   re 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q12 ∷
   rw 1 q64 ∷
   rw⁻ 0 q57 ∷
   rw⁻ 1 q56 ∷
   rw 2 q5 ∷
   rw 5 q1 ∷
   re 3 3 (CK30⁻ ∷ []) ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 2 q65 ∷
   rw 11 q1 ∷
   rw 10 q60 ∷
   rw 9 q61 ∷
   rw 8 q12 ∷
   re 7 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 6 q12 ∷
   rw 7 q66 ∷
   rw⁻ 6 q61 ∷
   rw⁻ 7 q60 ∷
   rw 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (CK30⁻ ∷ []) ∷
   rw 10 q5 ∷
   rw 11 q6 ∷
   rw 11 q1 ∷
   rw 10 q12 ∷
   re 9 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   rw 8 q12 ∷
   rw 9 q63 ∷
   rw 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (CK30⁻ ∷ []) ∷
   rw 10 q5 ∷
   rw 11 q6 ∷ []) Eq.refl

private
  q67 : Eqn
  q67 = wE 1413 W
  q68 : Eqn
  q68 = wE 1488 W
  q69 : Eqn
  q69 = sE 2036 lem-pass-X3-CK30-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q70 : Eqn
  q70 = wE 1489 W

-- pass [X3 CK30 X3] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 53 steps
lem-pass-X3-CK30-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (X3 ∷ CK30 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  (rw 3 q1 ∷
   rw 2 q12 ∷
   re 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q12 ∷
   rw 1 q67 ∷
   rw 0 q5 ∷
   rw 3 q1 ∷
   re 1 3 (CK30 ∷ []) ∷
   rw 2 q5 ∷
   rw 3 q6 ∷
   rw 5 q1 ∷
   rw 4 q56 ∷
   rw 3 q57 ∷
   rw 2 q12 ∷
   re 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q12 ∷
   rw 1 q68 ∷
   rw⁻ 0 q57 ∷
   rw⁻ 1 q56 ∷
   rw 2 q5 ∷
   rw 5 q1 ∷
   re 3 3 (CK30 ∷ []) ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 2 q69 ∷
   rw 11 q1 ∷
   rw 10 q60 ∷
   rw 9 q61 ∷
   rw 8 q12 ∷
   re 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 6 q12 ∷
   rw 7 q70 ∷
   rw⁻ 6 q61 ∷
   rw⁻ 7 q60 ∷
   rw 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (CK30 ∷ []) ∷
   rw 10 q5 ∷
   rw 11 q6 ∷
   rw 11 q1 ∷
   rw 10 q12 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   rw 8 q12 ∷
   rw 9 q67 ∷
   rw 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (CK30 ∷ []) ∷
   rw 10 q5 ∷
   rw 11 q6 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = wE 1490 W
  q72 : Eqn
  q72 = wE 1491 W
  q73 : Eqn
  q73 = sE 2039 lem-pass-X3-CS30-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q74 : Eqn
  q74 = wE 1492 W

-- pass [X3 CS30 X3] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 53 steps
lem-pass-X3-CS30-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (X3 ∷ CS03 ∷ X3 ∷ S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ []) (S1 ∷ K1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  (rw 3 q1 ∷
   rw 2 q12 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q12 ∷
   rw 1 q71 ∷
   rw 0 q5 ∷
   rw 3 q1 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q5 ∷
   rw 3 q6 ∷
   rw 5 q1 ∷
   rw 4 q56 ∷
   rw 3 q57 ∷
   rw 2 q12 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q12 ∷
   rw 1 q72 ∷
   rw⁻ 0 q57 ∷
   rw⁻ 1 q56 ∷
   rw 2 q5 ∷
   rw 5 q1 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 2 q73 ∷
   rw 11 q1 ∷
   rw 10 q60 ∷
   rw 9 q61 ∷
   rw 8 q12 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 6 q12 ∷
   rw 7 q74 ∷
   rw⁻ 6 q61 ∷
   rw⁻ 7 q60 ∷
   rw 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q5 ∷
   rw 11 q6 ∷
   rw 11 q1 ∷
   rw 10 q12 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   rw 8 q12 ∷
   rw 9 q71 ∷
   rw 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q5 ∷
   rw 11 q6 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = wE 1407 W
  q76 : Eqn
  q76 = sE 2034 lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q77 : Eqn
  q77 = wE 1408 W

-- pass [CK20] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 3 steps
lem-pass-CK20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (CK20 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CK20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = derive (CK20 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20 ∷ [])
  (rw 0 q75 ∷
   rw 1 q76 ∷
   rw 5 q77 ∷ []) Eq.refl
