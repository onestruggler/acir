{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD724 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D724 (W : Ws) (Sᴰ : SD724) where

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
  lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 840
  lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 0 Sᴰ
  lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 879
  lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 1 Sᴰ
  lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 913
  lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 2 Sᴰ
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 1131
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 3 Sᴰ
  lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 1143
  lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 4 Sᴰ
  lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 2034
  lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 5 Sᴰ
  lem-pass-X3-CK31-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2045
  lem-pass-X3-CK31-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 6 Sᴰ
  lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2038
  lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 7 Sᴰ
  lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2049
  lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 8 Sᴰ
  lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 2058
  lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 9 Sᴰ
  lem-Z-passes-X0-CS03-CS03-CK30-CS03-CX32-CS : St 2184
  lem-Z-passes-X0-CS03-CS03-CK30-CS03-CX32-CS = pickᴰ 10 Sᴰ
  lem-pass-X2-CK20-X2-vs-S0-Kd0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-K0-Sd0 : St 2185
  lem-pass-X2-CK20-X2-vs-S0-Kd0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-K0-Sd0 = pickᴰ 11 Sᴰ
  lem-pass-X2-CKd20-X2-vs-S0-S0-Kd0-S0-Kd0-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-K0-Sd0-K0-Sd0-Sd0 : St 2186
  lem-pass-X2-CKd20-X2-vs-S0-S0-Kd0-S0-Kd0-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-K0-Sd0-K0-Sd0-Sd0 = pickᴰ 12 Sᴰ
  lem-pass-X3-CK30-X3-vs-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0 : St 2187
  lem-pass-X3-CK30-X3-vs-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0 = pickᴰ 13 Sᴰ
  lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-Kd0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-K0-Sd0-K0-S0 : St 2188
  lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-Kd0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-K0-Sd0-K0-S0 = pickᴰ 14 Sᴰ
  lem-respell-hyb-CS13-CS13-CK31-CS13-CX32-CS12-CS12-CS12---⟶-CS01-CS01-CK01-CS01-CX03-CS13-CS13-CS13- : St 2189
  lem-respell-hyb-CS13-CS13-CK31-CS13-CX32-CS12-CS12-CS12---⟶-CS01-CS01-CK01-CS01-CX03-CS13-CS13-CS13- = pickᴰ 15 Sᴰ

private
  q1 : Eqn
  q1 = eqn (X3 ∷ CK31 ∷ X3 ∷ []) (X3 ∷ CK31 ∷ X3 ∷ []) (wn 1534 W)
  q2 : Eqn
  q2 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q3 : Eqn
  q3 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q4 : Eqn
  q4 = eqn (K0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑)))
  q5 : Eqn
  q5 = eqn (S0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑)))
  q6 : Eqn
  q6 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q7 : Eqn
  q7 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q8 : Eqn
  q8 = eqn (X2 ∷ CK21 ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (wn 1665 W)
  q9 : Eqn
  q9 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q10 : Eqn
  q10 = eqn (X3 ∷ CK31 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (lem-pass-X3-CK31-X3-vs-CS03-TOFF012-CSd03-TOFF012)
  q11 : Eqn
  q11 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q12 : Eqn
  q12 = eqn (X2 ∷ CK21 ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (wn 1666 W)

-- pass [X3 CK31 X3] [Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0]: 41 steps
lem-pass-X3-CK31-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK31-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = derive (X3 ∷ CK31 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK31 ∷ X3 ∷ [])
  (rw 0 q1 ∷
   rw 7 q2 ∷
   rw 6 q3 ∷
   rw 5 q3 ∷
   rw 4 q4 ∷
   rw 3 q5 ∷
   rw 2 q6 ∷
   re 1 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   rw 0 q6 ∷
   rw 1 q8 ∷
   rw⁻ 0 q5 ∷
   rw⁻ 1 q4 ∷
   rw⁻ 2 q3 ∷
   rw⁻ 3 q3 ∷
   rw 4 q9 ∷
   rw 7 q2 ∷
   re 5 3 (CK31 ∷ []) ∷
   rw 6 q9 ∷
   rw 7 q7 ∷
   rw 4 q10 ∷
   rw 15 q2 ∷
   rw 14 q3 ∷
   rw 13 q11 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw 10 q6 ∷
   re 9 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   rw 8 q6 ∷
   rw 9 q12 ∷
   rw⁻ 8 q5 ∷
   rw⁻ 9 q5 ∷
   rw⁻ 10 q11 ∷
   rw⁻ 11 q3 ∷
   rw 12 q9 ∷
   rw 15 q2 ∷
   re 13 3 (CK31 ∷ []) ∷
   rw 14 q9 ∷
   rw 15 q7 ∷
   rw 12 q1 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q15 : Eqn
  q15 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q16 : Eqn
  q16 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q17 : Eqn
  q17 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q18 : Eqn
  q18 = eqn (X3 ∷ CS13⁻ ∷ X3 ∷ X2 ∷ []) (X2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (wn 2063 W)
  q19 : Eqn
  q19 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q20 : Eqn
  q20 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q21 : Eqn
  q21 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ K0⁻ ∷ []) (K0⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 2061 W)
  q22 : Eqn
  q22 = eqn (X3 ∷ CS03 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
  q23 : Eqn
  q23 = eqn (X3 ∷ CK30 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
  q24 : Eqn
  q24 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ K0 ∷ []) (K0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 2062 W)

-- pass [X3 CSd30 X3] [X2 Kd0 CS03 TOFF012 CSd03 TOFF012 K0 X2]: 83 steps
lem-pass-X3-CSd30-X3-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ []) (X2 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ X2 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 4 q13 ∷
   rw⁻ 3 q14 ∷
   rw⁻ 2 q15 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q16 ∷
   rw 2 q17 ∷
   rw⁻ 1 q16 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 0 q15 ∷
   rw 1 q18 ∷
   rw 0 q14 ∷
   rw 1 q15 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q16 ∷
   rw 3 q19 ∷
   rw 4 q16 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q15 ∷
   rw 4 q20 ∷
   rw 5 q2 ∷
   rw 4 q4 ∷
   rw 3 q6 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw 1 q6 ∷
   rw 2 q21 ∷
   rw⁻ 1 q4 ∷
   rw 2 q9 ∷
   rw 5 q2 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q9 ∷
   rw 5 q9 ∷
   rw 8 q2 ∷
   re 6 3 (CK30 ∷ []) ∷
   rw 7 q9 ∷
   rw 8 q9 ∷
   rw 11 q2 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q9 ∷
   rw 11 q7 ∷
   rw 8 q22 ∷
   rw 5 q23 ∷
   rw 2 q22 ∷
   rw 16 q2 ∷
   rw 15 q11 ∷
   rw 14 q6 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q7 ∷
   rw 12 q6 ∷
   rw 11 q6 ∷
   re 10 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 12 q7 ∷
   rw 9 q6 ∷
   rw 8 q6 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q7 ∷
   rw 6 q6 ∷
   rw 7 q24 ∷
   rw⁻ 6 q11 ∷
   rw 7 q9 ∷
   rw 10 q2 ∷
   re 8 3 (CS03⁻ ∷ []) ∷
   rw 9 q9 ∷
   rw 10 q7 ∷
   rw 11 q13 ∷
   rw⁻ 10 q14 ∷
   rw⁻ 9 q15 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q16 ∷
   rw 9 q17 ∷
   rw⁻ 8 q16 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q15 ∷
   rw 8 q18 ∷
   rw 7 q14 ∷
   rw 8 q15 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q16 ∷
   rw 10 q19 ∷
   rw 11 q16 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   rw 10 q15 ∷
   rw 11 q20 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = eqn (CX10 ∷ CZ01 ∷ X1 ∷ CX01 ∷ CZ01 ∷ X1 ∷ []) (Sw01 ∷ X0 ∷ X1 ∷ CX10 ∷ X1 ∷ []) (wn 1701 W)
  q26 : Eqn
  q26 = eqn (X1 ∷ CX10 ∷ X1 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK10 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S1 ∷ CK10 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK10 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S1 ∷ CK10 ∷ X0 ∷ X1 ∷ CX10 ∷ X1 ∷ []) (lem-Z-passes-X0-CS03-CS03-CK30-CS03-CX32-CS)
  q27 : Eqn
  q27 = eqn (X0 ∷ X0 ∷ []) [] (wn 387 W)
  q28 : Eqn
  q28 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q29 : Eqn
  q29 = eqn (Sw01 ∷ CK20 ∷ []) (CK21 ∷ Sw01 ∷ []) (wn 275 W)
  q30 : Eqn
  q30 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q31 : Eqn
  q31 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q32 : Eqn
  q32 = eqn (Sw01 ∷ CK10 ∷ []) (CK01 ∷ Sw01 ∷ []) (wn 327 W)
  q33 : Eqn
  q33 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q34 : Eqn
  q34 = eqn (Sw01 ∷ S1 ∷ []) (S0 ∷ Sw01 ∷ []) (wn 315 W)
  q35 : Eqn
  q35 = eqn (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK01 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S0 ∷ CK01 ∷ []) (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK21 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK21 ∷ []) (lem-respell-hyb-CS13-CS13-CK31-CS13-CX32-CS12-CS12-CS12---⟶-CS01-CS01-CK01-CS01-CX03-CS13-CS13-CS13-)
  q36 : Eqn
  q36 = eqn (Sw01 ∷ X0 ∷ X1 ∷ CX10 ∷ X1 ∷ []) (CX10 ∷ CZ01 ∷ X1 ∷ CX01 ∷ CZ01 ∷ X1 ∷ []) (wn 1702 W)

-- conjF X0 CS03 CS03 CK30 CS03 CX32 CS: 143 steps
lem-conjF-X0-CS03-CS03-CK30-CS03-CX32-CS : ⟪ (CX10 ∷ CZ01 ∷ X1 ∷ CX01 ∷ CZ01 ∷ X1 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK10 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S1 ∷ CK10 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK21 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK21 ∷ CX10 ∷ CZ01 ∷ X1 ∷ CX01 ∷ CZ01 ∷ X1 ∷ []) ⟫ʷ
lem-conjF-X0-CS03-CS03-CK30-CS03-CX32-CS = derive (CX10 ∷ CZ01 ∷ X1 ∷ CX01 ∷ CZ01 ∷ X1 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK10 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S1 ∷ CK10 ∷ X0 ∷ []) (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK21 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK21 ∷ CX10 ∷ CZ01 ∷ X1 ∷ CX01 ∷ CZ01 ∷ X1 ∷ [])
  (rw 0 q25 ∷
   rw 2 q26 ∷
   rw 1 q27 ∷
   rw 81 q13 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 0 q16 ∷
   rw 1 q28 ∷
   rw 2 q16 ∷
   re 0 3 (CS13 ∷ []) ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 1 q16 ∷
   rw 2 q28 ∷
   rw 3 q16 ∷
   re 1 3 (CS13 ∷ []) ∷
   re 3 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 2 q16 ∷
   rw 3 q29 ∷
   rw 4 q16 ∷
   re 2 3 (CK31 ∷ []) ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q16 ∷
   rw 4 q28 ∷
   rw 5 q16 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw 4 q30 ∷
   rw 5 q28 ∷
   rw 6 q28 ∷
   rw 7 q28 ∷
   rw 8 q29 ∷
   rw 9 q31 ∷
   rw 10 q28 ∷
   rw 11 q28 ∷
   rw 12 q28 ∷
   rw 13 q28 ∷
   rw 14 q28 ∷
   rw 15 q28 ∷
   rw 16 q30 ∷
   rw 17 q28 ∷
   rw 18 q28 ∷
   rw 19 q29 ∷
   rw 20 q28 ∷
   rw 21 q32 ∷
   rw 22 q28 ∷
   rw 23 q28 ∷
   rw 24 q28 ∷
   rw 25 q31 ∷
   rw 26 q29 ∷
   rw 27 q28 ∷
   rw 28 q28 ∷
   rw 29 q28 ∷
   rw 30 q28 ∷
   rw 31 q28 ∷
   rw 32 q28 ∷
   rw 33 q30 ∷
   rw 34 q28 ∷
   rw 35 q28 ∷
   rw 36 q28 ∷
   rw 37 q28 ∷
   rw 38 q28 ∷
   rw 39 q28 ∷
   rw 40 q28 ∷
   rw 41 q28 ∷
   rw 42 q28 ∷
   rw 43 q28 ∷
   rw 44 q28 ∷
   rw 45 q28 ∷
   rw 46 q28 ∷
   rw 47 q28 ∷
   rw 48 q28 ∷
   rw 49 q28 ∷
   rw 50 q28 ∷
   rw 51 q28 ∷
   rw 52 q31 ∷
   rw 53 q31 ∷
   rw 54 q31 ∷
   rw 55 q31 ∷
   rw 56 q29 ∷
   rw 57 q28 ∷
   rw 58 q28 ∷
   rw 59 q28 ∷
   rw 60 q28 ∷
   rw 61 q28 ∷
   rw 62 q28 ∷
   rw 63 q28 ∷
   rw 64 q28 ∷
   rw 65 q28 ∷
   rw 66 q30 ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 67 q16 ∷
   rw 68 q28 ∷
   rw 69 q16 ∷
   re 67 3 (CS13 ∷ []) ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 68 q16 ∷
   rw 69 q28 ∷
   rw 70 q16 ∷
   re 68 3 (CS13 ∷ []) ∷
   re 70 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 69 q16 ∷
   rw 70 q28 ∷
   rw 71 q16 ∷
   re 69 3 (CS13 ∷ []) ∷
   rw 70 q33 ∷
   re 72 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 71 q16 ∷
   rw 72 q29 ∷
   rw 73 q16 ∷
   re 71 3 (CK31 ∷ []) ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 72 q16 ∷
   rw 73 q28 ∷
   rw 74 q16 ∷
   re 72 3 (CS13 ∷ []) ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 73 q16 ∷
   rw 74 q28 ∷
   rw 75 q16 ∷
   re 73 3 (CS13 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q16 ∷
   rw 75 q28 ∷
   rw 76 q16 ∷
   re 74 3 (CS13 ∷ []) ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q16 ∷
   rw 76 q28 ∷
   rw 77 q16 ∷
   re 75 3 (CS13 ∷ []) ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q16 ∷
   rw 77 q28 ∷
   rw 78 q16 ∷
   re 76 3 (CS13 ∷ []) ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q16 ∷
   rw 78 q28 ∷
   rw 79 q16 ∷
   re 77 3 (CS13 ∷ []) ∷
   rw 78 q34 ∷
   rw 79 q32 ∷
   rw 80 q20 ∷
   rw 0 q35 ∷
   rw 80 q36 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = eqn (X2 ∷ CK20 ∷ X2 ∷ K0⁻ ∷ K0⁻ ∷ []) (K0⁻ ∷ K0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 2175 W)
  q38 : Eqn
  q38 = eqn (X2 ∷ CK20 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012)
  q39 : Eqn
  q39 = eqn (X2 ∷ CK20 ∷ X2 ∷ K0 ∷ K0 ∷ []) (K0 ∷ K0 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 2176 W)

-- pass [X2 CK20 X2] [Kd0 Kd0 CS03 TOFF012 CSd03 TOFF012 K0 K0]: 3 steps
lem-pass-X2-CK20-X2-vs-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK20-X2-vs-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0 = derive (X2 ∷ CK20 ∷ X2 ∷ K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ []) (K0⁻ ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ K0 ∷ X2 ∷ CK20 ∷ X2 ∷ [])
  (rw 0 q37 ∷
   rw 2 q38 ∷
   rw 6 q39 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 2177 W)
  q41 : Eqn
  q41 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012)
  q42 : Eqn
  q42 = eqn (X2 ∷ CS02 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012)
  q43 : Eqn
  q43 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 2178 W)

-- pass [X2 CKd20 X2] [S0 S0 Kd0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 K0 Sd0 Sd0]: 7 steps
lem-pass-X2-CKd20-X2-vs-S0-S0-Kd0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-K0-Sd0-Sd0 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd20-X2-vs-S0-S0-Kd0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-K0-Sd0-Sd0 = derive (X2 ∷ CK20⁻ ∷ X2 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  (rw 0 q40 ∷
   rw 16 q38 ∷
   rw 13 q38 ∷
   rw 10 q41 ∷
   rw 7 q38 ∷
   rw 4 q42 ∷
   rw 8 q43 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 2179 W)
  q45 : Eqn
  q45 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012)
  q46 : Eqn
  q46 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 2180 W)

-- pass [X3 CKd30 X3] [Sd0 Kd0 S0 S0 Kd0 CS03 TOFF012 CSd03 TOFF012 K0 Sd0 Sd0 K0 S0]: 79 steps
lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-S0 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-S0 = derive (X3 ∷ CK30⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  (rw 8 q2 ∷
   rw 7 q4 ∷
   rw 6 q3 ∷
   rw 5 q3 ∷
   rw 4 q4 ∷
   rw 3 q5 ∷
   rw 2 q6 ∷
   re 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   rw 0 q6 ∷
   rw 1 q44 ∷
   rw⁻ 0 q5 ∷
   rw⁻ 1 q4 ∷
   rw⁻ 2 q3 ∷
   rw⁻ 3 q3 ∷
   rw⁻ 4 q4 ∷
   rw 5 q9 ∷
   rw 8 q2 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q9 ∷
   rw 8 q9 ∷
   rw 11 q2 ∷
   re 9 3 (CK30 ∷ []) ∷
   rw 10 q9 ∷
   rw 11 q9 ∷
   rw 14 q2 ∷
   re 12 3 (CS03⁻ ∷ []) ∷
   rw 13 q9 ∷
   rw 14 q9 ∷
   rw 17 q2 ∷
   re 15 3 (CK30 ∷ []) ∷
   rw 16 q9 ∷
   rw 17 q9 ∷
   rw 20 q2 ∷
   re 18 3 (CK30 ∷ []) ∷
   rw 19 q9 ∷
   rw 20 q7 ∷
   rw 17 q23 ∷
   rw 14 q23 ∷
   rw 11 q45 ∷
   rw 8 q23 ∷
   rw 5 q22 ∷
   rw 29 q2 ∷
   rw 28 q3 ∷
   rw 27 q11 ∷
   rw 26 q5 ∷
   rw 25 q5 ∷
   rw 24 q11 ∷
   rw 23 q6 ∷
   re 22 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 24 q7 ∷
   rw 21 q6 ∷
   rw 20 q6 ∷
   re 19 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 21 q7 ∷
   rw 18 q6 ∷
   rw 17 q6 ∷
   re 16 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q7 ∷
   rw 15 q6 ∷
   rw 14 q6 ∷
   re 13 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 15 q7 ∷
   rw 12 q6 ∷
   rw 11 q6 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q7 ∷
   rw 9 q6 ∷
   rw 10 q46 ∷
   rw⁻ 9 q11 ∷
   rw⁻ 10 q5 ∷
   rw⁻ 11 q5 ∷
   rw⁻ 12 q11 ∷
   rw⁻ 13 q3 ∷
   rw 14 q9 ∷
   rw 17 q2 ∷
   re 15 3 (CK30⁻ ∷ []) ∷
   rw 16 q9 ∷
   rw 17 q7 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ []) (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 2181 W)
  q48 : Eqn
  q48 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) (S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 2182 W)

-- pass [X2 CKd20 X2] [Sd0 K0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 Kd0 S0]: 7 steps
lem-pass-X2-CKd20-X2-vs-Sd0-K0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-Kd0-S0 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd20-X2-vs-Sd0-K0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-Kd0-S0 = derive (X2 ∷ CK20⁻ ∷ X2 ∷ S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ []) (S0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  (rw 0 q47 ∷
   rw 16 q38 ∷
   rw 13 q42 ∷
   rw 10 q42 ∷
   rw 7 q38 ∷
   rw 4 q41 ∷
   rw 8 q48 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = eqn (CK20⁻ ∷ []) (K0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 1709 W)
  q50 : Eqn
  q50 = eqn (X3 ∷ CK30 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-K0-S0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-Sd0-Kd0)
  q51 : Eqn
  q51 = eqn (K0⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ []) (wn 2183 W)
  q52 : Eqn
  q52 = eqn (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (wn 2184 W)
  q53 : Eqn
  q53 = eqn (K0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (CK20⁻ ∷ []) (wn 1711 W)

-- CA CKd30 Gad(t=0, W=(), d=KSSKd, e=1): 23 steps
lem-CA-CKd30-Gad⟨t≡0-W≡⟨⟩-d≡KSSKd-e≡1⟩ : ⟪ (CK30⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ CK30⁻ ∷ []) ⟫ʷ
lem-CA-CKd30-Gad⟨t≡0-W≡⟨⟩-d≡KSSKd-e≡1⟩ = derive (CK30⁻ ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ CK30⁻ ∷ [])
  (rw 1 q2 ∷
   re 0 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q7 ∷
   rw 1 q49 ∷
   rw⁻ 0 q4 ∷
   rw 1 q9 ∷
   rw 4 q2 ∷
   re 2 3 (CK30 ∷ []) ∷
   rw 3 q9 ∷
   rw 4 q7 ∷
   rw 1 q50 ∷
   rw 0 q51 ∷
   rw 7 q52 ∷
   rw 14 q2 ∷
   rw 13 q6 ∷
   re 12 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 14 q7 ∷
   rw 11 q6 ∷
   rw 10 q4 ∷
   rw 11 q53 ∷
   rw 12 q2 ∷
   re 10 3 (CK30⁻ ∷ []) ∷
   rw 11 q7 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = eqn (X1 ∷ CK10 ∷ X1 ∷ S0 ∷ K0⁻ ∷ []) (S0 ∷ K0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (wn 2185 W)
  q55 : Eqn
  q55 = eqn (X1 ∷ CK10 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03)
  q56 : Eqn
  q56 = eqn (X1 ∷ CS01 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03)
  q57 : Eqn
  q57 = eqn (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ K0 ∷ S0⁻ ∷ []) (K0 ∷ S0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (wn 2186 W)

-- pass [X1 CK10 X1] [S0 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 Sd0]: 7 steps
lem-pass-X1-CK10-X1-vs-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0 : ⟪ (X1 ∷ CK10 ∷ X1 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CK10-X1-vs-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0 = derive (X1 ∷ CK10 ∷ X1 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ []) (S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ [])
  (rw 0 q54 ∷
   rw 14 q55 ∷
   rw 11 q56 ∷
   rw 8 q56 ∷
   rw 5 q55 ∷
   rw 2 q56 ∷
   rw 6 q57 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) (K0⁻ ∷ S0 ∷ K0⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (wn 2187 W)
  q59 : Eqn
  q59 = eqn (X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CS01 ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ K0 ∷ S0⁻ ∷ K0 ∷ []) (K0 ∷ S0⁻ ∷ K0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 2188 W)

-- pass [X1 CSd10 X1] [Kd0 S0 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 Sd0 K0]: 5 steps
lem-pass-X1-CSd10-X1-vs-Kd0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-K0 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-Kd0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-K0 = derive (X1 ∷ CS01⁻ ∷ X1 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ []) (K0⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  (rw 0 q58 ∷
   rw 9 q55 ∷
   rw 6 q56 ∷
   rw 3 q56 ∷
   rw 7 q59 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = eqn (X2 ∷ CK20 ∷ X2 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-S0-Kd0-S0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-Sd0-K0-Sd0)
  q61 : Eqn
  q61 = eqn (K0⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ []) (wn 2189 W)
  q62 : Eqn
  q62 = eqn (K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ []) (wn 2190 W)

-- CA CKd20 Gad(t=0, W=(), d=SKdSKd, e=1): 5 steps
lem-CA-CKd20-Gad⟨t≡0-W≡⟨⟩-d≡SKdSKd-e≡1⟩ : ⟪ (CK20⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ CK20⁻ ∷ []) ⟫ʷ
lem-CA-CKd20-Gad⟨t≡0-W≡⟨⟩-d≡SKdSKd-e≡1⟩ = derive (CK20⁻ ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (S0⁻ ∷ K0 ∷ K0 ∷ K0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ K0⁻ ∷ S0 ∷ CK20⁻ ∷ [])
  (rw 0 q49 ∷
   rw 1 q60 ∷
   rw 0 q61 ∷
   rw 9 q62 ∷
   rw 14 q53 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 2191 W)
  q64 : Eqn
  q64 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03)
  q65 : Eqn
  q65 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ X1 ∷ CK10 ∷ X1 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 2192 W)

-- pass [X1 CSd10 X1] [S0 Kd0 S0 Kd0 Sd0 TOFF012 CS03 TOFF012 CSd03 S0 K0 Sd0 K0 Sd0]: 5 steps
lem-pass-X1-CSd10-X1-vs-S0-Kd0-S0-Kd0-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-K0-Sd0-K0-Sd0 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-S0-Kd0-S0-Kd0-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-K0-Sd0-K0-Sd0 = derive (X1 ∷ CS01⁻ ∷ X1 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  (rw 0 q63 ∷
   rw 11 q64 ∷
   rw 8 q55 ∷
   rw 5 q64 ∷
   rw 9 q65 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = eqn (CK20 ∷ []) (K0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1459 W)
  q67 : Eqn
  q67 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-S0-S0-Kd0-S0-Kd0-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-K0-Sd0-K0-Sd0-Sd0)
  q68 : Eqn
  q68 = eqn (K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) (wn 2193 W)
  q69 : Eqn
  q69 = eqn (S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ K0 ∷ []) (wn 2194 W)
  q70 : Eqn
  q70 = eqn (K0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (CK20 ∷ []) (wn 1461 W)

-- CA CK20 Gad(t=0, W=(), d=SSKdSKdSd, e=1): 5 steps
lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSKdSd-e≡1⟩ : ⟪ (CK20 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ CK20 ∷ []) ⟫ʷ
lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡SSKdSKdSd-e≡1⟩ = derive (CK20 ∷ S0 ∷ S0 ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ CK20 ∷ [])
  (rw 0 q66 ∷
   rw 1 q67 ∷
   rw 0 q68 ∷
   rw 9 q69 ∷
   rw 14 q70 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = eqn (X3 ∷ CK30⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-Kd0-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-K0-Sd0-K0-S0)
  q72 : Eqn
  q72 = eqn (K0 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) (wn 2195 W)
  q73 : Eqn
  q73 = eqn (K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ K0 ∷ []) (wn 2196 W)

-- CA CK30 Gad(t=0, W=(), d=SdKdSKdKd, e=1): 23 steps
lem-CA-CK30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSKdKd-e≡1⟩ : ⟪ (CK30 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ CK30 ∷ []) ⟫ʷ
lem-CA-CK30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSKdKd-e≡1⟩ = derive (CK30 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ K0⁻ ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ K0 ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0 ∷ K0⁻ ∷ S0 ∷ S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0⁻ ∷ CK30 ∷ [])
  (rw 1 q2 ∷
   re 0 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 2 q7 ∷
   rw 1 q66 ∷
   rw⁻ 0 q11 ∷
   rw 1 q9 ∷
   rw 4 q2 ∷
   re 2 3 (CK30⁻ ∷ []) ∷
   rw 3 q9 ∷
   rw 4 q7 ∷
   rw 1 q71 ∷
   rw 0 q72 ∷
   rw 8 q73 ∷
   rw 16 q2 ∷
   rw 15 q6 ∷
   re 14 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q7 ∷
   rw 13 q6 ∷
   rw 12 q11 ∷
   rw 13 q70 ∷
   rw 14 q2 ∷
   re 12 3 (CK30 ∷ []) ∷
   rw 13 q7 ∷ []) Eq.refl
