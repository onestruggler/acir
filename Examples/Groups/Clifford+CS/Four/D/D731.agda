{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD731 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D731 (W : Ws) (Sᴰ : SD731) where

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
  lem-pass-CKd30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2260
  lem-pass-CKd30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 0 Sᴰ
  lem-ROT-gad : St 2261
  lem-ROT-gad = pickᴰ 1 Sᴰ
  lem-pass-CS30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2231
  lem-pass-CS30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 2 Sᴰ
  lem-pass-CSd30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2262
  lem-pass-CSd30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 3 Sᴰ
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 : St 2263
  lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 = pickᴰ 4 Sᴰ
  lem-pass-X3-CK30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : St 2264
  lem-pass-X3-CK30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = pickᴰ 5 Sᴰ
  lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : St 2265
  lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = pickᴰ 6 Sᴰ
  lem-pass-X3-CS30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : St 2266
  lem-pass-X3-CS30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = pickᴰ 7 Sᴰ
  lem-pass-X3-CS31-X3-vs-CS13-TOFF102-CSd13-TOFF102 : St 2267
  lem-pass-X3-CS31-X3-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 8 Sᴰ
  lem-pass-X3-CS32-X3-vs-CS23-TOFF201-CSd23-TOFF201 : St 2268
  lem-pass-X3-CS32-X3-vs-CS23-TOFF201-CSd23-TOFF201 = pickᴰ 9 Sᴰ
  lem-pass-X3-CSd30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : St 2269
  lem-pass-X3-CSd30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = pickᴰ 10 Sᴰ
  lem-pass-X3-CSd32-X3-vs-CS23-TOFF201-CSd23-TOFF201 : St 2270
  lem-pass-X3-CSd32-X3-vs-CS23-TOFF201-CSd23-TOFF201 = pickᴰ 11 Sᴰ

private
  q1 : Eqn
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = eqn (CZ02 ∷ Sw01 ∷ []) (Sw01 ∷ CZ12 ∷ []) (wn 189 W)
  q4 : Eqn
  q4 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q5 : Eqn
  q5 = eqn (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) (wn 8 W)
  q6 : Eqn
  q6 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wn 9 W)
  q7 : Eqn
  q7 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wn 10 W)
  q8 : Eqn
  q8 = eqn (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 11 W)
  q9 : Eqn
  q9 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q10 : Eqn
  q10 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wn 118 W)
  q11 : Eqn
  q11 = eqn (K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ ι1 ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wn 274 W)
  q12 : Eqn
  q12 = eqn (CK01 ∷ Sw01 ∷ []) (Sw01 ∷ CK10 ∷ []) (wn 480 W)
  q13 : Eqn
  q13 = eqn (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) (wn 481 W)
  q14 : Eqn
  q14 = eqn (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ []) (lem-ROT-gad)
  q15 : Eqn
  q15 = eqn (Sw01 ∷ S0 ∷ []) (S1 ∷ Sw01 ∷ []) (wn 311 W)
  q16 : Eqn
  q16 = eqn (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) (wn 123 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q18 : Eqn
  q18 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q19 : Eqn
  q19 = eqn (Sw01 ∷ CX01 ∷ []) (CX10 ∷ Sw01 ∷ []) (wn 28 W)
  q20 : Eqn
  q20 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q21 : Eqn
  q21 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)
  q22 : Eqn
  q22 = eqn (Sw01 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ Sw01 ∷ []) (wn 322 W)
  q23 : Eqn
  q23 = eqn (Sw01 ∷ K0⁻ ∷ []) (K1⁻ ∷ Sw01 ∷ []) (wn 313 W)
  q24 : Eqn
  q24 = eqn (Sw01 ∷ S0⁻ ∷ []) (S1⁻ ∷ Sw01 ∷ []) (wn 312 W)
  q25 : Eqn
  q25 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)

-- ROT-gad @1023: 138 steps
lem-ROT-gad-at1023 : ⟪ (CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ S0 ∷ CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ []) ⟫ʷ
lem-ROT-gad-at1023 = derive (CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ S0 ∷ CK01 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ [])
  (rw 15 q1 ∷
   re 14 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q2 ∷
   rw 15 q3 ∷
   rw⁻ 14 q2 ∷
   re 15 3 (CZ13 ∷ []) ∷
   re 13 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 17 q4 ∷
   rw 16 q5 ∷
   rw 15 q6 ∷
   rw 14 q5 ∷
   rw 13 q7 ∷
   rw 14 q8 ∷
   re 14 5 (CCZ012 ∷ []) ∷
   re 12 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 19 q9 ∷
   rw 18 q10 ∷
   rw 17 q4 ∷
   rw 16 q5 ∷
   rw 15 q6 ∷
   rw 14 q5 ∷
   rw 13 q7 ∷
   rw 12 q10 ∷
   rw 13 q11 ∷
   re 13 8 (Toff102 ∷ []) ∷
   re 11 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q2 ∷
   rw 12 q3 ∷
   rw⁻ 11 q2 ∷
   re 12 3 (CZ13 ∷ []) ∷
   re 10 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 17 q9 ∷
   rw 16 q10 ∷
   rw 15 q4 ∷
   rw 14 q5 ∷
   rw 13 q6 ∷
   rw 12 q5 ∷
   rw 11 q7 ∷
   rw 10 q10 ∷
   rw 11 q11 ∷
   re 11 8 (Toff102 ∷ []) ∷
   re 9 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 13 q4 ∷
   rw 12 q5 ∷
   rw 11 q6 ∷
   rw 10 q5 ∷
   rw 9 q7 ∷
   rw 10 q8 ∷
   re 10 5 (CCZ012 ∷ []) ∷
   rw 8 q12 ∷
   rw 7 q13 ∷
   re 6 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q2 ∷
   rw 7 q3 ∷
   rw⁻ 6 q2 ∷
   re 7 3 (CZ13 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 9 q4 ∷
   rw 8 q5 ∷
   rw 7 q6 ∷
   rw 6 q5 ∷
   rw 5 q7 ∷
   rw 6 q8 ∷
   re 6 5 (CCZ012 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   rw 9 q4 ∷
   rw 8 q5 ∷
   rw 7 q6 ∷
   rw 6 q5 ∷
   rw 5 q7 ∷
   rw 4 q10 ∷
   rw 5 q11 ∷
   re 5 8 (Toff102 ∷ []) ∷
   re 3 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q2 ∷
   rw 4 q3 ∷
   rw⁻ 3 q2 ∷
   re 4 3 (CZ13 ∷ []) ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 9 q9 ∷
   rw 8 q10 ∷
   rw 7 q4 ∷
   rw 6 q5 ∷
   rw 5 q6 ∷
   rw 4 q5 ∷
   rw 3 q7 ∷
   rw 2 q10 ∷
   rw 3 q11 ∷
   re 3 8 (Toff102 ∷ []) ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 5 q4 ∷
   rw 4 q5 ∷
   rw 3 q6 ∷
   rw 2 q5 ∷
   rw 1 q7 ∷
   rw 2 q8 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   rw 0 q12 ∷
   rw 1 q14 ∷
   rw 0 q15 ∷
   rw 1 q16 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q2 ∷
   rw 3 q17 ∷
   rw 4 q2 ∷
   re 2 3 (CS13 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 3 q16 ∷
   rw 4 q18 ∷
   rw 5 q19 ∷
   rw 6 q20 ∷
   rw 7 q19 ∷
   rw 8 q17 ∷
   rw 9 q16 ∷
   rw 10 q21 ∷
   rw 3 q11 ∷
   re 3 8 (Toff102 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q2 ∷
   rw 5 q22 ∷
   rw 6 q2 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 5 q16 ∷
   rw 6 q18 ∷
   rw 7 q19 ∷
   rw 8 q20 ∷
   rw 9 q19 ∷
   rw 10 q17 ∷
   rw 11 q16 ∷
   rw 12 q21 ∷
   rw 5 q11 ∷
   re 5 8 (Toff102 ∷ []) ∷
   rw 6 q23 ∷
   rw 7 q24 ∷
   rw 8 q25 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = eqn (S0⁻ ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑ ↑)))
  q27 : Eqn
  q27 = eqn (K0⁻ ∷ X3 ∷ []) (X3 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((X ↑ ↑)))
  q28 : Eqn
  q28 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q29 : Eqn
  q29 = eqn (K0 ∷ X3 ∷ []) (X3 ∷ K0 ∷ []) (low₁-comm (K) ((X ↑ ↑)))
  q30 : Eqn
  q30 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q31 : Eqn
  q31 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q32 : Eqn
  q32 = eqn (K0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑)))
  q33 : Eqn
  q33 = eqn (S0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑)))
  q34 : Eqn
  q34 = eqn (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02 ∷ CS02 ∷ []) (wn 2239 W)
  q35 : Eqn
  q35 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q36 : Eqn
  q36 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q37 : Eqn
  q37 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q38 : Eqn
  q38 = eqn (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (CS02⁻ ∷ CS02⁻ ∷ CK20 ∷ CS02 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 2240 W)
  q39 : Eqn
  q39 = eqn (CS03 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ []) (lem-pass-CS30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3)
  q40 : Eqn
  q40 = eqn (CK30⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30⁻ ∷ []) (lem-pass-CKd30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3)
  q41 : Eqn
  q41 = eqn (CS03⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ []) (lem-pass-CSd30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3)
  q42 : Eqn
  q42 = eqn (CS02⁻ ∷ CK20⁻ ∷ CS02 ∷ CS02 ∷ CS02⁻ ∷ CS02⁻ ∷ CK20 ∷ CS02 ∷ []) [] (wn 2241 W)

-- ca-split Gad(t=0, W=(3,), d=SdKdSS, e=-1) 3: 93 steps
lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3 : ⟪ (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3 = derive (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) (X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  (rw⁻ 0 q26 ∷
   rw⁻ 1 q27 ∷
   rw⁻ 2 q28 ∷
   rw⁻ 3 q28 ∷
   rw 12 q28 ∷
   rw 11 q29 ∷
   rw 10 q26 ∷
   rw 9 q26 ∷
   rw 4 q30 ∷
   rw 3 q31 ∷
   rw 2 q31 ∷
   rw 1 q32 ∷
   rw 0 q33 ∷
   rw 1 q34 ∷
   rw 0 q35 ∷
   rw 3 q30 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q35 ∷
   rw 3 q35 ∷
   rw 6 q30 ∷
   re 4 3 (CK30⁻ ∷ []) ∷
   rw 5 q35 ∷
   rw 6 q35 ∷
   rw 9 q30 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q35 ∷
   rw 9 q35 ∷
   rw 12 q30 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q35 ∷
   rw 14 q30 ∷
   re 12 3 (CS03⁻ ∷ []) ∷
   rw 15 q30 ∷
   re 13 3 (CK30⁻ ∷ []) ∷
   rw 16 q30 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 17 q30 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 16 q36 ∷
   rw 26 q30 ∷
   rw 25 q31 ∷
   rw 24 q37 ∷
   rw 23 q33 ∷
   rw 22 q33 ∷
   rw 23 q38 ∷
   rw 24 q30 ∷
   re 22 3 (CS03⁻ ∷ []) ∷
   rw 25 q30 ∷
   re 23 3 (CS03⁻ ∷ []) ∷
   rw 26 q30 ∷
   re 24 3 (CK30 ∷ []) ∷
   rw 27 q30 ∷
   re 25 3 (CS03 ∷ []) ∷
   rw 26 q35 ∷
   rw 29 q30 ∷
   re 27 3 (CS03⁻ ∷ []) ∷
   rw 28 q35 ∷
   rw 29 q35 ∷
   rw 32 q30 ∷
   re 30 3 (CS03⁻ ∷ []) ∷
   rw 31 q35 ∷
   rw 32 q35 ∷
   rw 35 q30 ∷
   re 33 3 (CK30 ∷ []) ∷
   rw 34 q35 ∷
   rw 35 q35 ∷
   rw 38 q30 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 37 q35 ∷
   rw 38 q36 ∷
   rw 15 q39 ∷
   rw 14 q39 ∷
   rw 13 q40 ∷
   rw 12 q41 ∷
   rw 26 q30 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q36 ∷
   re 24 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 26 q36 ∷
   re 23 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 25 q36 ∷
   re 22 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 24 q36 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q36 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q36 ∷
   re 19 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 21 q36 ∷
   re 18 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q36 ∷
   rw 19 q42 ∷
   rw 18 q36 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = eqn (CS23 ∷ X3 ∷ []) (X3 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (wn 2154 W)
  q44 : Eqn
  q44 = eqn (X3 ∷ CS23 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-pass-X3-CS32-X3-vs-CS23-TOFF201-CSd23-TOFF201)
  q45 : Eqn
  q45 = eqn (X3 ∷ CS23 ∷ X3 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ []) (wn 2155 W)

-- pass [CS32] [X3 CS23 TOFF201 CSd23 TOFF201 X3]: 3 steps
lem-pass-CS32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 : ⟪ (CS23 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 = derive (CS23 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23 ∷ [])
  (rw 0 q43 ∷
   rw 1 q44 ∷
   rw 5 q45 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = eqn (CS23⁻ ∷ X3 ∷ []) (X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (wn 2242 W)
  q47 : Eqn
  q47 = eqn (X3 ∷ CS23⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd32-X3-vs-CS23-TOFF201-CSd23-TOFF201)
  q48 : Eqn
  q48 = eqn (X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ []) (wn 2243 W)

-- pass [CSd32] [X3 CS23 TOFF201 CSd23 TOFF201 X3]: 3 steps
lem-pass-CSd32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 : ⟪ (CS23⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-CSd32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 = derive (CS23⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CS23⁻ ∷ [])
  (rw 0 q46 ∷
   rw 1 q47 ∷
   rw 5 q48 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q50 : Eqn
  q50 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q51 : Eqn
  q51 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 56 W)
  q52 : Eqn
  q52 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q53 : Eqn
  q53 = eqn (X2 ∷ Toff012 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ []) (wn 2016 W)
  q54 : Eqn
  q54 = eqn (CS02 ∷ X3 ∷ []) (X3 ∷ CS02 ∷ []) (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q55 : Eqn
  q55 = eqn (CS02⁻ ∷ X3 ∷ []) (X3 ∷ CS02⁻ ∷ []) (low₃-comm ((Swap ↑ • (CS • CS • CS) • Swap ↑)) (X))
  q56 : Eqn
  q56 = eqn (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02)
  q57 : Eqn
  q57 = eqn (X2 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (Toff012 ∷ X2 ∷ []) (wn 2017 W)

-- pass [X3 TOFF201 CS23 TOFF201 CSd23 X3] [TOFF013 CS02 TOFF013 CSd02]: 249 steps
lem-pass-X3-TOFF201-CS23-TOFF201-CSd23-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-TOFF201-CS23-TOFF201-CSd23-X3-vs-TOFF013-CS02-TOFF013-CSd02 = derive (X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ [])
  (rw 7 q30 ∷
   re 6 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 6 q37 ∷
   rw 9 q30 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q49 ∷
   rw 11 q30 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q49 ∷
   rw 13 q30 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q37 ∷
   rw⁻ 13 q50 ∷
   rw 14 q36 ∷
   rw 13 q50 ∷
   rw 12 q37 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q36 ∷
   rw 10 q49 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q36 ∷
   rw 8 q49 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q36 ∷
   rw 6 q37 ∷
   rw 7 q51 ∷
   re 7 8 (Toff012 ∷ []) ∷
   rw 5 q52 ∷
   rw 6 q53 ∷
   rw 5 q35 ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 6 q37 ∷
   rw 9 q30 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q49 ∷
   rw 11 q30 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q49 ∷
   rw 13 q30 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q37 ∷
   rw⁻ 13 q50 ∷
   rw 6 q30 ∷
   rw⁻ 7 q37 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q36 ∷
   rw⁻ 9 q49 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q36 ∷
   rw⁻ 11 q49 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q36 ∷
   rw⁻ 13 q37 ∷
   rw⁻ 14 q50 ∷
   rw 7 q51 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 6 3 (Toff013 ∷ []) ∷
   rw 7 q35 ∷
   rw 8 q35 ∷
   rw 9 q36 ∷
   rw⁻ 8 q54 ∷
   rw 11 q30 ∷
   re 10 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 11 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 10 q37 ∷
   rw 13 q30 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw⁻ 12 q49 ∷
   rw 15 q30 ∷
   re 13 3 (CS13⁻ ∷ []) ∷
   rw⁻ 14 q49 ∷
   rw 17 q30 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw⁻ 16 q37 ∷
   rw⁻ 17 q50 ∷
   rw 18 q36 ∷
   rw 17 q50 ∷
   rw 16 q37 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q36 ∷
   rw 14 q49 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q36 ∷
   rw 12 q49 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q36 ∷
   rw 10 q37 ∷
   rw 11 q51 ∷
   re 11 8 (Toff012 ∷ []) ∷
   rw 9 q52 ∷
   rw 10 q53 ∷
   rw 9 q35 ∷
   re 11 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 10 q37 ∷
   rw 13 q30 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw⁻ 12 q49 ∷
   rw 15 q30 ∷
   re 13 3 (CS13⁻ ∷ []) ∷
   rw⁻ 14 q49 ∷
   rw 17 q30 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw⁻ 16 q37 ∷
   rw⁻ 17 q50 ∷
   rw 10 q30 ∷
   rw⁻ 11 q37 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q36 ∷
   rw⁻ 13 q49 ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q36 ∷
   rw⁻ 15 q49 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q36 ∷
   rw⁻ 17 q37 ∷
   rw⁻ 18 q50 ∷
   rw 11 q51 ∷
   re 11 8 (Toff012 ∷ []) ∷
   re 10 3 (Toff013 ∷ []) ∷
   rw 11 q35 ∷
   rw 12 q35 ∷
   rw 13 q36 ∷
   rw⁻ 12 q55 ∷
   rw 1 q56 ∷
   rw 4 q30 ∷
   rw 3 q52 ∷
   re 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q37 ∷
   rw 5 q30 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q49 ∷
   rw 7 q30 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q49 ∷
   rw 9 q30 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q37 ∷
   rw⁻ 9 q50 ∷
   rw 10 q36 ∷
   rw 9 q50 ∷
   rw 8 q37 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q36 ∷
   rw 6 q49 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q36 ∷
   rw 4 q49 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q36 ∷
   rw 2 q37 ∷
   rw 3 q51 ∷
   re 3 8 (Toff012 ∷ []) ∷
   rw 1 q52 ∷
   rw 0 q52 ∷
   rw 1 q57 ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 0 q37 ∷
   rw 3 q30 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q49 ∷
   rw 5 q30 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q49 ∷
   rw 7 q30 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q37 ∷
   rw⁻ 7 q50 ∷
   rw 0 q30 ∷
   rw⁻ 1 q37 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q36 ∷
   rw⁻ 3 q49 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q36 ∷
   rw⁻ 5 q49 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q36 ∷
   rw⁻ 7 q37 ∷
   rw⁻ 8 q50 ∷
   rw 1 q51 ∷
   re 1 8 (Toff012 ∷ []) ∷
   re 0 3 (Toff013 ∷ []) ∷
   rw 1 q35 ∷
   rw 2 q36 ∷
   rw⁻ 1 q54 ∷
   rw 6 q30 ∷
   rw 5 q52 ∷
   re 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 4 q37 ∷
   rw 7 q30 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q49 ∷
   rw 9 q30 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q49 ∷
   rw 11 q30 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q37 ∷
   rw⁻ 11 q50 ∷
   rw 12 q36 ∷
   rw 11 q50 ∷
   rw 10 q37 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q36 ∷
   rw 8 q49 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q36 ∷
   rw 6 q49 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q36 ∷
   rw 4 q37 ∷
   rw 5 q51 ∷
   re 5 8 (Toff012 ∷ []) ∷
   rw 3 q52 ∷
   rw 2 q52 ∷
   rw 3 q57 ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q37 ∷
   rw 5 q30 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q49 ∷
   rw 7 q30 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q49 ∷
   rw 9 q30 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q37 ∷
   rw⁻ 9 q50 ∷
   rw 2 q30 ∷
   rw⁻ 3 q37 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q36 ∷
   rw⁻ 5 q49 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q36 ∷
   rw⁻ 7 q49 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q36 ∷
   rw⁻ 9 q37 ∷
   rw⁻ 10 q50 ∷
   rw 3 q51 ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 2 3 (Toff013 ∷ []) ∷
   rw 3 q35 ∷
   rw 4 q36 ∷
   rw⁻ 3 q55 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q59 : Eqn
  q59 = eqn (X2 ∷ CS12 ∷ X2 ∷ X0 ∷ []) (X0 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (wn 1689 W)
  q60 : Eqn
  q60 = eqn (X3 ∷ CS13 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ []) (wn 2119 W)
  q61 : Eqn
  q61 = eqn (X3 ∷ CS13 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (lem-pass-X3-CS31-X3-vs-CS13-TOFF102-CSd13-TOFF102)

-- pass [X3 CS31 X3] [X0 CS13 TOFF102 CSd13 TOFF102 X0]: 29 steps
lem-pass-X3-CS31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 = derive (X3 ∷ CS13 ∷ X3 ∷ X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ []) (X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ CS13 ∷ X3 ∷ [])
  (rw 4 q30 ∷
   rw 3 q58 ∷
   rw 2 q52 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q36 ∷
   rw 0 q52 ∷
   rw 1 q59 ∷
   rw⁻ 0 q58 ∷
   rw 1 q35 ∷
   rw 4 q30 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 3 q35 ∷
   rw 4 q36 ∷
   rw 1 q60 ∷
   rw 1 q61 ∷
   rw 5 q60 ∷
   rw 9 q30 ∷
   rw 8 q58 ∷
   rw 7 q52 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q36 ∷
   rw 5 q52 ∷
   rw 6 q59 ∷
   rw⁻ 5 q58 ∷
   rw 6 q35 ∷
   rw 9 q30 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 8 q35 ∷
   rw 9 q36 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = eqn (CS02⁻ ∷ X2 ∷ []) (X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 1466 W)
  q63 : Eqn
  q63 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0)
  q64 : Eqn
  q64 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ []) (X2 ∷ CS02⁻ ∷ []) (wn 1467 W)

-- pass [CSd30] [X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X3]: 23 steps
lem-pass-CSd30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : ⟪ (CS03⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = derive (CS03⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CS03⁻ ∷ [])
  (rw 2 q30 ∷
   rw 1 q52 ∷
   re 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q36 ∷
   rw 1 q62 ∷
   rw 0 q35 ∷
   rw 1 q35 ∷
   rw 4 q30 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q35 ∷
   rw 4 q36 ∷
   rw 1 q63 ∷
   rw 17 q30 ∷
   rw 16 q52 ∷
   rw 15 q52 ∷
   re 14 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q36 ∷
   rw 13 q52 ∷
   rw 14 q64 ∷
   rw 13 q35 ∷
   rw 16 q30 ∷
   re 14 3 (CS03⁻ ∷ []) ∷
   rw 15 q36 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = eqn (CK20⁻ ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1464 W)
  q66 : Eqn
  q66 = eqn (X3 ∷ CK30⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0)
  q67 : Eqn
  q67 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK20⁻ ∷ []) (wn 1465 W)

-- pass [CKd30] [X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X3]: 23 steps
lem-pass-CKd30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : ⟪ (CK30⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK30⁻ ∷ []) ⟫ʷ
lem-pass-CKd30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = derive (CK30⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK30⁻ ∷ [])
  (rw 2 q30 ∷
   rw 1 q52 ∷
   re 0 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q36 ∷
   rw 1 q65 ∷
   rw 0 q35 ∷
   rw 1 q35 ∷
   rw 4 q30 ∷
   re 2 3 (CK30⁻ ∷ []) ∷
   rw 3 q35 ∷
   rw 4 q36 ∷
   rw 1 q66 ∷
   rw 17 q30 ∷
   rw 16 q52 ∷
   rw 15 q52 ∷
   re 14 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q36 ∷
   rw 13 q52 ∷
   rw 14 q67 ∷
   rw 13 q35 ∷
   rw 16 q30 ∷
   re 14 3 (CK30⁻ ∷ []) ∷
   rw 15 q36 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = eqn (CK20 ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 1407 W)
  q69 : Eqn
  q69 = eqn (X3 ∷ CK30 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0)
  q70 : Eqn
  q70 = eqn (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK20 ∷ []) (wn 1408 W)

-- pass [CK30] [X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X3]: 23 steps
lem-pass-CK30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : ⟪ (CK30 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CK30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = derive (CK30 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK30 ∷ [])
  (rw 2 q30 ∷
   rw 1 q52 ∷
   re 0 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 2 q36 ∷
   rw 1 q68 ∷
   rw 0 q35 ∷
   rw 1 q35 ∷
   rw 4 q30 ∷
   re 2 3 (CK30 ∷ []) ∷
   rw 3 q35 ∷
   rw 4 q36 ∷
   rw 1 q69 ∷
   rw 17 q30 ∷
   rw 16 q52 ∷
   rw 15 q52 ∷
   re 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 16 q36 ∷
   rw 13 q52 ∷
   rw 14 q70 ∷
   rw 13 q35 ∷
   rw 16 q30 ∷
   re 14 3 (CK30 ∷ []) ∷
   rw 15 q36 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = eqn (CS02 ∷ X2 ∷ []) (X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 1462 W)
  q72 : Eqn
  q72 = eqn (X3 ∷ CS03 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0)
  q73 : Eqn
  q73 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ []) (X2 ∷ CS02 ∷ []) (wn 1463 W)

-- pass [CS30] [X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X3]: 23 steps
lem-pass-CS30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : ⟪ (CS03 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS30-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = derive (CS03 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CS03 ∷ [])
  (rw 2 q30 ∷
   rw 1 q52 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q36 ∷
   rw 1 q71 ∷
   rw 0 q35 ∷
   rw 1 q35 ∷
   rw 4 q30 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q35 ∷
   rw 4 q36 ∷
   rw 1 q72 ∷
   rw 17 q30 ∷
   rw 16 q52 ∷
   rw 15 q52 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q36 ∷
   rw 13 q52 ∷
   rw 14 q73 ∷
   rw 13 q35 ∷
   rw 16 q30 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 15 q36 ∷ []) Eq.refl

private
  q74 : Eqn
  q74 = eqn (X3 ∷ CS23 ∷ X3 ∷ X0 ∷ []) (X0 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (wn 2169 W)
  q75 : Eqn
  q75 = eqn (X3 ∷ CS23 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ X3 ∷ []) (wn 2170 W)

-- pass [X3 CS32 X3] [X0 CS23 TOFF201 CSd23 TOFF201 X0]: 5 steps
lem-pass-X3-CS32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ X0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0 = derive (X3 ∷ CS23 ∷ X3 ∷ X0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ []) (X0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  (rw 0 q74 ∷
   rw 1 q75 ∷
   rw 1 q44 ∷
   rw 5 q75 ∷
   rw 5 q74 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = eqn (X3 ∷ CS23⁻ ∷ X3 ∷ X0 ∷ []) (X0 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (wn 2244 W)
  q77 : Eqn
  q77 = eqn (X3 ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ X3 ∷ []) (wn 2245 W)

-- pass [X3 CSd32 X3] [X0 CS23 TOFF201 CSd23 TOFF201 X0]: 5 steps
lem-pass-X3-CSd32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ X0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0 = derive (X3 ∷ CS23⁻ ∷ X3 ∷ X0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ []) (X0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ [])
  (rw 0 q76 ∷
   rw 1 q77 ∷
   rw 1 q47 ∷
   rw 5 q77 ∷
   rw 5 q76 ∷ []) Eq.refl
