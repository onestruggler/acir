{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD515 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D515 (W : Ws) (Sᴰ : SD515) where

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
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-CS13-vs-CS02 : St 27
  lem-pass-CS13-vs-CS02 = pickᴰ 0 Sᴰ
  lem-pass-CSd02-vs-CS13 : St 28
  lem-pass-CSd02-vs-CS13 = pickᴰ 1 Sᴰ
  lem-pass-S2-vs-CS13 : St 30
  lem-pass-S2-vs-CS13 = pickᴰ 2 Sᴰ
  lem-pass-Sd2-vs-CS13 : St 32
  lem-pass-Sd2-vs-CS13 = pickᴰ 3 Sᴰ
  lem-pass-X3-CKd31-X3-vs-CS02 : St 117
  lem-pass-X3-CKd31-X3-vs-CS02 = pickᴰ 4 Sᴰ
  lem-pass-X3-CKd31-X3-vs-CSd02 : St 118
  lem-pass-X3-CKd31-X3-vs-CSd02 = pickᴰ 5 Sᴰ
  lem-pass-X3-CKd31-X3-vs-TOFF013 : St 119
  lem-pass-X3-CKd31-X3-vs-TOFF013 = pickᴰ 6 Sᴰ
  lem-pass-X3-CSd31-X3-vs-CS02 : St 122
  lem-pass-X3-CSd31-X3-vs-CS02 = pickᴰ 7 Sᴰ
  lem-pass-X3-CSd31-X3-vs-CSd02 : St 123
  lem-pass-X3-CSd31-X3-vs-CSd02 = pickᴰ 8 Sᴰ
  lem-pass-X3-CSd31-X3-vs-TOFF013 : St 124
  lem-pass-X3-CSd31-X3-vs-TOFF013 = pickᴰ 9 Sᴰ
  lem-pass-CS23-vs-Sd0 : St 157
  lem-pass-CS23-vs-Sd0 = pickᴰ 10 Sᴰ
  lem-pass-X3-CKd32-X3-vs-CS01 : St 139
  lem-pass-X3-CKd32-X3-vs-CS01 = pickᴰ 11 Sᴰ
  lem-pass-X3-CKd32-X3-vs-CSd01 : St 140
  lem-pass-X3-CKd32-X3-vs-CSd01 = pickᴰ 12 Sᴰ
  lem-pass-X3-CKd32-X3-vs-TOFF023 : St 141
  lem-pass-X3-CKd32-X3-vs-TOFF023 = pickᴰ 13 Sᴰ
  lem-pass-X3-CS32-X3-vs-CS01 : St 142
  lem-pass-X3-CS32-X3-vs-CS01 = pickᴰ 14 Sᴰ
  lem-pass-X3-CS32-X3-vs-CSd01 : St 143
  lem-pass-X3-CS32-X3-vs-CSd01 = pickᴰ 15 Sᴰ
  lem-pass-X3-CS32-X3-vs-TOFF023 : St 144
  lem-pass-X3-CS32-X3-vs-TOFF023 = pickᴰ 16 Sᴰ
  lem-pass-X3-CSd32-X3-vs-CS01 : St 145
  lem-pass-X3-CSd32-X3-vs-CS01 = pickᴰ 17 Sᴰ
  lem-pass-X3-CSd32-X3-vs-CSd01 : St 147
  lem-pass-X3-CSd32-X3-vs-CSd01 = pickᴰ 18 Sᴰ
  lem-pass-X3-CSd32-X3-vs-TOFF023 : St 149
  lem-pass-X3-CSd32-X3-vs-TOFF023 = pickᴰ 19 Sᴰ
  lem-comm-CCZ023-CS13 : St 158
  lem-comm-CCZ023-CS13 = pickᴰ 20 Sᴰ
  lem-pass-CS23-vs-Sd3 : St 159
  lem-pass-CS23-vs-Sd3 = pickᴰ 21 Sᴰ
  lem-pass-CS23-vs-iI : St 160
  lem-pass-CS23-vs-iI = pickᴰ 22 Sᴰ
  lem-pass-CSd23-vs-iI : St 161
  lem-pass-CSd23-vs-iI = pickᴰ 23 Sᴰ
  lem-pass-Sd0-vs-CSd23 : St 162
  lem-pass-Sd0-vs-CSd23 = pickᴰ 24 Sᴰ
  lem-pass-Sd3-vs-CSd23 : St 163
  lem-pass-Sd3-vs-CSd23 = pickᴰ 25 Sᴰ
  lem-pass-TOFF201-vs-iI : St 164
  lem-pass-TOFF201-vs-iI = pickᴰ 26 Sᴰ

private
  q1 : Eqn
  q1 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q2 : Eqn
  q2 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q3 : Eqn
  q3 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q4 : Eqn
  q4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q5 : Eqn
  q5 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q6 : Eqn
  q6 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q7 : Eqn
  q7 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 56 W)
  q8 : Eqn
  q8 = eqn (X2 ∷ Toff012 ∷ X2 ∷ []) (CX10 ∷ Toff012 ∷ []) (wn 1362 W)
  q9 : Eqn
  q9 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap))
  q10 : Eqn
  q10 = eqn (CS12 ∷ CX10 ∷ []) (CX10 ∷ CS12 ∷ []) (wn 1382 W)
  q11 : Eqn
  q11 = eqn (CS12 ∷ Toff012 ∷ []) (Toff012 ∷ CS12 ∷ []) (wn 90 W)
  q12 : Eqn
  q12 = eqn (CX10 ∷ Toff012 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ []) (wn 1364 W)
  q13 : Eqn
  q13 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q14 : Eqn
  q14 = eqn (S2 ∷ CS13 ∷ []) (CS13 ∷ S2 ∷ []) lem-pass-S2-vs-CS13
  q15 : Eqn
  q15 = eqn (CS02⁻ ∷ CS13 ∷ []) (CS13 ∷ CS02⁻ ∷ []) lem-pass-CSd02-vs-CS13
  q16 : Eqn
  q16 = eqn (S2⁻ ∷ CS13 ∷ []) (CS13 ∷ S2⁻ ∷ []) lem-pass-Sd2-vs-CS13
  q17 : Eqn
  q17 = eqn (CS13 ∷ CS02 ∷ []) (CS02 ∷ CS13 ∷ []) (lem-pass-CS13-vs-CS02)

-- pass [CS13] [X3 TOFF013 X3 S2 CSd02 X3 TOFF013 X3 Sd2 CS02]: 384 steps
lem-pass-CS13-vs-X3-TOFF013-X3-S2-CSd02-X3-TOFF013-X3-Sd2-CS02 : ⟪ (CS13 ∷ X3 ∷ Toff013 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-X3-TOFF013-X3-S2-CSd02-X3-TOFF013-X3-Sd2-CS02 = derive (CS13 ∷ X3 ∷ Toff013 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ S2 ∷ CS02⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ S2⁻ ∷ CS02 ∷ CS13 ∷ [])
  (rw 4 q1 ∷
   rw 3 q2 ∷
   re 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 10 q6 ∷
   rw 9 q5 ∷
   rw 8 q3 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 6 q4 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 4 q4 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 2 q3 ∷
   rw 3 q7 ∷
   re 3 8 (Toff012 ∷ []) ∷
   rw 1 q2 ∷
   rw 2 q8 ∷
   rw⁻ 1 q9 ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q1 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q5 ∷
   rw 3 q7 ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 2 3 (Toff013 ∷ []) ∷
   rw 3 q6 ∷
   rw 2 q1 ∷
   rw 1 q9 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q6 ∷
   rw 1 q10 ∷
   rw⁻ 0 q9 ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 2 q6 ∷
   rw 3 q1 ∷
   re 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 10 q6 ∷
   rw 9 q5 ∷
   rw 8 q3 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 6 q4 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 4 q4 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 2 q3 ∷
   rw 3 q7 ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 2 q11 ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 1 q1 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q7 ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 3 q6 ∷
   rw 2 q1 ∷
   re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 9 q6 ∷
   rw 8 q5 ∷
   rw 7 q3 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q4 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 3 q4 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw 1 q3 ∷
   rw 2 q7 ∷
   re 2 8 (Toff012 ∷ []) ∷
   rw 0 q9 ∷
   rw 1 q12 ∷
   rw 0 q13 ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 1 q1 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q7 ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   rw 2 q13 ∷
   rw 3 q6 ∷
   rw⁻ 3 q14 ∷
   rw⁻ 4 q15 ∷
   rw 9 q1 ∷
   rw 8 q2 ∷
   re 7 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 8 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q4 ∷
   rw 14 q1 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw⁻ 13 q3 ∷
   rw⁻ 14 q5 ∷
   rw 15 q6 ∷
   rw 14 q5 ∷
   rw 13 q3 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q6 ∷
   rw 11 q4 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   rw 9 q4 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw 7 q3 ∷
   rw 8 q7 ∷
   re 8 8 (Toff012 ∷ []) ∷
   rw 6 q2 ∷
   rw 7 q8 ∷
   rw⁻ 6 q9 ∷
   re 8 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q4 ∷
   rw 14 q1 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw⁻ 13 q3 ∷
   rw⁻ 14 q5 ∷
   rw 7 q1 ∷
   rw⁻ 8 q3 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw⁻ 10 q4 ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   rw⁻ 12 q4 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q6 ∷
   rw⁻ 14 q3 ∷
   rw⁻ 15 q5 ∷
   rw 8 q7 ∷
   re 8 8 (Toff012 ∷ []) ∷
   re 7 3 (Toff013 ∷ []) ∷
   rw 8 q6 ∷
   rw 7 q1 ∷
   rw 6 q9 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 6 q10 ∷
   rw⁻ 5 q9 ∷
   rw 8 q1 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 7 q6 ∷
   rw 8 q1 ∷
   re 7 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 8 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q4 ∷
   rw 14 q1 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw⁻ 13 q3 ∷
   rw⁻ 14 q5 ∷
   rw 15 q6 ∷
   rw 14 q5 ∷
   rw 13 q3 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q6 ∷
   rw 11 q4 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   rw 9 q4 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw 7 q3 ∷
   rw 8 q7 ∷
   re 8 8 (Toff012 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 7 q11 ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q4 ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q3 ∷
   rw⁻ 13 q5 ∷
   rw 6 q1 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw⁻ 9 q4 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw⁻ 11 q4 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   rw⁻ 13 q3 ∷
   rw⁻ 14 q5 ∷
   rw 7 q7 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 6 3 (Toff013 ∷ []) ∷
   rw 9 q1 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 8 q6 ∷
   rw 7 q1 ∷
   re 6 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q4 ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q3 ∷
   rw⁻ 13 q5 ∷
   rw 14 q6 ∷
   rw 13 q5 ∷
   rw 12 q3 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q6 ∷
   rw 10 q4 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   rw 8 q4 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 6 q3 ∷
   rw 7 q7 ∷
   re 7 8 (Toff012 ∷ []) ∷
   rw 5 q9 ∷
   rw 6 q12 ∷
   rw 5 q13 ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q4 ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q3 ∷
   rw⁻ 13 q5 ∷
   rw 6 q1 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw⁻ 9 q4 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw⁻ 11 q4 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   rw⁻ 13 q3 ∷
   rw⁻ 14 q5 ∷
   rw 7 q7 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 6 3 (Toff013 ∷ []) ∷
   rw 7 q13 ∷
   rw 8 q6 ∷
   rw⁻ 8 q16 ∷
   rw 9 q17 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = eqn (CCZ023 ∷ CS13 ∷ []) (CS13 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CS13)

-- pass [CCZ023] [CS13]: 1 steps
lem-pass-CCZ023-vs-CS13 : ⟪ (CCZ023 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CCZ023 ∷ []) ⟫ʷ
lem-pass-CCZ023-vs-CS13 = derive (CCZ023 ∷ CS13 ∷ []) (CS13 ∷ CCZ023 ∷ [])
  (rw 0 q18 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = eqn (X3 ∷ CK31⁻ ∷ X3 ∷ Toff013 ∷ []) (Toff013 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd31-X3-vs-TOFF013)
  q20 : Eqn
  q20 = eqn (X3 ∷ CK31⁻ ∷ X3 ∷ CS02 ∷ []) (CS02 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd31-X3-vs-CS02)
  q21 : Eqn
  q21 = eqn (X3 ∷ CK31⁻ ∷ X3 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd31-X3-vs-CSd02)

-- pass [X3 CKd31 X3] [TOFF013 CS02 TOFF013 CSd02]: 4 steps
lem-pass-X3-CKd31-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd31-X3-vs-TOFF013-CS02-TOFF013-CSd02 = derive (X3 ∷ CK31⁻ ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ [])
  (rw 0 q19 ∷
   rw 1 q20 ∷
   rw 2 q19 ∷
   rw 3 q21 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = eqn (X3 ∷ CS13⁻ ∷ X3 ∷ Toff013 ∷ []) (Toff013 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd31-X3-vs-TOFF013)
  q23 : Eqn
  q23 = eqn (X3 ∷ CS13⁻ ∷ X3 ∷ CS02 ∷ []) (CS02 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd31-X3-vs-CS02)
  q24 : Eqn
  q24 = eqn (X3 ∷ CS13⁻ ∷ X3 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd31-X3-vs-CSd02)

-- pass [X3 CSd31 X3] [TOFF013 CS02 TOFF013 CSd02]: 4 steps
lem-pass-X3-CSd31-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd31-X3-vs-TOFF013-CS02-TOFF013-CSd02 = derive (X3 ∷ CS13⁻ ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ [])
  (rw 0 q22 ∷
   rw 1 q23 ∷
   rw 2 q22 ∷
   rw 3 q24 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = eqn (X3 ∷ CS23⁻ ∷ X3 ∷ CS01 ∷ []) (CS01 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd32-X3-vs-CS01)
  q26 : Eqn
  q26 = eqn (X3 ∷ CS23⁻ ∷ X3 ∷ Toff023 ∷ []) (Toff023 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd32-X3-vs-TOFF023)
  q27 : Eqn
  q27 = eqn (X3 ∷ CS23⁻ ∷ X3 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd32-X3-vs-CSd01)

-- pass [X3 CSd32 X3] [CS01 TOFF023 CSd01 TOFF023]: 4 steps
lem-pass-X3-CSd32-X3-vs-CS01-TOFF023-CSd01-TOFF023 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd32-X3-vs-CS01-TOFF023-CSd01-TOFF023 = derive (X3 ∷ CS23⁻ ∷ X3 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ [])
  (rw 0 q25 ∷
   rw 1 q26 ∷
   rw 2 q27 ∷
   rw 3 q26 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = eqn (X3 ∷ CK32⁻ ∷ X3 ∷ CS01 ∷ []) (CS01 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd32-X3-vs-CS01)
  q29 : Eqn
  q29 = eqn (X3 ∷ CK32⁻ ∷ X3 ∷ Toff023 ∷ []) (Toff023 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd32-X3-vs-TOFF023)
  q30 : Eqn
  q30 = eqn (X3 ∷ CK32⁻ ∷ X3 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd32-X3-vs-CSd01)

-- pass [X3 CKd32 X3] [CS01 TOFF023 CSd01 TOFF023]: 4 steps
lem-pass-X3-CKd32-X3-vs-CS01-TOFF023-CSd01-TOFF023 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd32-X3-vs-CS01-TOFF023-CSd01-TOFF023 = derive (X3 ∷ CK32⁻ ∷ X3 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ [])
  (rw 0 q28 ∷
   rw 1 q29 ∷
   rw 2 q30 ∷
   rw 3 q29 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = eqn (X3 ∷ CS23 ∷ X3 ∷ CS01 ∷ []) (CS01 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-pass-X3-CS32-X3-vs-CS01)
  q32 : Eqn
  q32 = eqn (X3 ∷ CS23 ∷ X3 ∷ Toff023 ∷ []) (Toff023 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-pass-X3-CS32-X3-vs-TOFF023)
  q33 : Eqn
  q33 = eqn (X3 ∷ CS23 ∷ X3 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ []) (lem-pass-X3-CS32-X3-vs-CSd01)

-- pass [X3 CS32 X3] [CS01 TOFF023 CSd01 TOFF023]: 4 steps
lem-pass-X3-CS32-X3-vs-CS01-TOFF023-CSd01-TOFF023 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-CS01-TOFF023-CSd01-TOFF023 = derive (X3 ∷ CS23 ∷ X3 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  (rw 0 q31 ∷
   rw 1 q32 ∷
   rw 2 q33 ∷
   rw 3 q32 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = eqn (Toff201 ∷ ι ∷ []) (ι ∷ Toff201 ∷ []) (lem-pass-TOFF201-vs-iI)
  q35 : Eqn
  q35 = eqn (CS23⁻ ∷ ι ∷ []) (ι ∷ CS23⁻ ∷ []) (lem-pass-CSd23-vs-iI)
  q36 : Eqn
  q36 = eqn (CS23 ∷ ι ∷ []) (ι ∷ CS23 ∷ []) (lem-pass-CS23-vs-iI)

-- pass [CS23 TOFF201 CSd23 TOFF201] [iI]: 4 steps
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-iI : ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-iI = derive (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ ι ∷ []) (ι ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ [])
  (rw 3 q34 ∷
   rw 2 q35 ∷
   rw 1 q34 ∷
   rw 0 q36 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = eqn (CS23 ∷ S0⁻ ∷ []) (S0⁻ ∷ CS23 ∷ []) lem-pass-CS23-vs-Sd0
  q38 : Eqn
  q38 = eqn (S0⁻ ∷ Toff201 ∷ []) (Toff201 ∷ S0⁻ ∷ []) (wn 1383 W)
  q39 : Eqn
  q39 = eqn (S0⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S0⁻ ∷ []) (lem-pass-Sd0-vs-CSd23)

-- pass [Sd0] [CS23 TOFF201 CSd23 TOFF201]: 4 steps
lem-pass-Sd0-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (S0⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0⁻ ∷ []) ⟫ʷ
lem-pass-Sd0-vs-CS23-TOFF201-CSd23-TOFF201 = derive (S0⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0⁻ ∷ [])
  (rw⁻ 0 q37 ∷
   rw 1 q38 ∷
   rw 2 q39 ∷
   rw 3 q38 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = eqn (CS23 ∷ S3⁻ ∷ []) (S3⁻ ∷ CS23 ∷ []) lem-pass-CS23-vs-Sd3
  q41 : Eqn
  q41 = eqn (Toff201 ∷ S3⁻ ∷ []) (S3⁻ ∷ Toff201 ∷ []) (low₃-comm (Toffᵗ) ((S • S • S)))
  q42 : Eqn
  q42 = eqn (S3⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S3⁻ ∷ []) (lem-pass-Sd3-vs-CSd23)

-- pass [Sd3] [CS23 TOFF201 CSd23 TOFF201]: 4 steps
lem-pass-Sd3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (S3⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S3⁻ ∷ []) ⟫ʷ
lem-pass-Sd3-vs-CS23-TOFF201-CSd23-TOFF201 = derive (S3⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S3⁻ ∷ [])
  (rw⁻ 0 q40 ∷
   rw⁻ 1 q41 ∷
   rw 2 q42 ∷
   rw⁻ 3 q41 ∷ []) Eq.refl
