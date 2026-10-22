{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD733 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D733 (W : Ws) (Sᴰ : SD733) where

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
  lem-pass-X2-CSd20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : St 2274
  lem-pass-X2-CSd20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = pickᴰ 0 Sᴰ
  lem-pass-X3-CK30-X3-vs-CS23-TOFF201-CSd23-TOFF201 : St 2272
  lem-pass-X3-CK30-X3-vs-CS23-TOFF201-CSd23-TOFF201 = pickᴰ 1 Sᴰ
  lem-pass-X3-CKd30-X3-vs-CS23-TOFF201-CSd23-TOFF201 : St 2275
  lem-pass-X3-CKd30-X3-vs-CS23-TOFF201-CSd23-TOFF201 = pickᴰ 2 Sᴰ
  lem-pass-X3-CS30-X3-vs-CS23-TOFF201-CSd23-TOFF201 : St 2273
  lem-pass-X3-CS30-X3-vs-CS23-TOFF201-CSd23-TOFF201 = pickᴰ 3 Sᴰ
  lem-pass-X3-CSd30-X3-vs-CS23-TOFF201-CSd23-TOFF201 : St 2276
  lem-pass-X3-CSd30-X3-vs-CS23-TOFF201-CSd23-TOFF201 = pickᴰ 4 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q3 : Eqn
  q3 = wE 173 W
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = wE 2250 W
  q6 : Eqn
  q6 = wE 175 W
  q7 : Eqn
  q7 = wE 5 W
  q8 : Eqn
  q8 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q9 : Eqn
  q9 = eqn (Sw01 ∷ K2⁻ ∷ []) (K2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((K • iI)))
  q10 : Eqn
  q10 = eqn (Sw01 ∷ S2⁻ ∷ []) (S2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S • S • S)))
  q11 : Eqn
  q11 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q12 : Eqn
  q12 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q13 : Eqn
  q13 = wE 7 W
  q14 : Eqn
  q14 = wE 140 W
  q15 : Eqn
  q15 = wE 76 W
  q16 : Eqn
  q16 = wE 2251 W
  q17 : Eqn
  q17 = wE 27 W
  q18 : Eqn
  q18 = wE 142 W
  q19 : Eqn
  q19 = wE 29 W
  q20 : Eqn
  q20 = wE 31 W
  q21 : Eqn
  q21 = sE 2273 lem-pass-X3-CS30-X3-vs-CS23-TOFF201-CSd23-TOFF201
  q22 : Eqn
  q22 = sE 2272 lem-pass-X3-CK30-X3-vs-CS23-TOFF201-CSd23-TOFF201
  q23 : Eqn
  q23 = sE 2276 lem-pass-X3-CSd30-X3-vs-CS23-TOFF201-CSd23-TOFF201
  q24 : Eqn
  q24 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K))
  q25 : Eqn
  q25 = wE 2252 W
  q26 : Eqn
  q26 = wE 2253 W

-- pass [X3 CKd30 X3] [X0 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X0]: 225 steps
lem-pass-X3-CKd30-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ X0 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0 = derive (X3 ∷ CK30⁻ ∷ X3 ∷ X0 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ []) (X0 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  (rw 4 q1 ∷
   rw 3 q2 ∷
   rw 2 q3 ∷
   re 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   rw 0 q3 ∷
   rw 1 q5 ∷
   rw⁻ 0 q2 ∷
   rw 1 q6 ∷
   rw 4 q1 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q6 ∷
   rw 4 q6 ∷
   rw 7 q1 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 6 q6 ∷
   rw 7 q6 ∷
   rw 10 q1 ∷
   re 8 3 (CS03⁻ ∷ []) ∷
   rw 9 q6 ∷
   rw 10 q6 ∷
   rw 13 q1 ∷
   re 11 3 (CK30 ∷ []) ∷
   rw 12 q6 ∷
   rw 13 q6 ∷
   rw 16 q1 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 15 q6 ∷
   rw 16 q4 ∷
   rw 20 q7 ∷
   rw⁻ 19 q8 ∷
   rw⁻ 18 q8 ∷
   rw⁻ 17 q9 ∷
   rw⁻ 16 q10 ∷
   rw⁻ 15 q11 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q12 ∷
   rw 15 q13 ∷
   rw⁻ 14 q12 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw⁻ 13 q11 ∷
   rw⁻ 12 q11 ∷
   re 11 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q12 ∷
   rw 12 q14 ∷
   rw⁻ 11 q12 ∷
   re 12 3 (CK31 ∷ []) ∷
   rw⁻ 10 q11 ∷
   rw⁻ 9 q11 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q12 ∷
   rw 9 q15 ∷
   rw⁻ 8 q12 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q11 ∷
   rw⁻ 6 q11 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q12 ∷
   rw 6 q14 ∷
   rw⁻ 5 q12 ∷
   re 6 3 (CK31 ∷ []) ∷
   rw⁻ 4 q11 ∷
   rw⁻ 3 q11 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q12 ∷
   rw 3 q13 ∷
   rw⁻ 2 q12 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 1 q11 ∷
   rw 2 q16 ∷
   rw 1 q10 ∷
   rw 2 q9 ∷
   rw 3 q8 ∷
   rw 4 q8 ∷
   rw 5 q11 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q12 ∷
   rw 7 q17 ∷
   rw 8 q12 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q11 ∷
   rw 8 q11 ∷
   re 10 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   rw 10 q18 ∷
   rw 11 q12 ∷
   re 9 3 (CK30 ∷ []) ∷
   rw 10 q11 ∷
   rw 11 q11 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q12 ∷
   rw 13 q19 ∷
   rw 14 q12 ∷
   re 12 3 (CS03⁻ ∷ []) ∷
   rw 13 q11 ∷
   rw 14 q11 ∷
   re 16 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 15 q12 ∷
   rw 16 q18 ∷
   rw 17 q12 ∷
   re 15 3 (CK30 ∷ []) ∷
   rw 16 q11 ∷
   rw 17 q11 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q12 ∷
   rw 19 q17 ∷
   rw 20 q12 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 19 q11 ∷
   rw 20 q20 ∷
   rw 17 q21 ∷
   rw 14 q22 ∷
   rw 11 q23 ∷
   rw 8 q22 ∷
   rw 5 q21 ∷
   rw 28 q7 ∷
   rw⁻ 27 q8 ∷
   rw⁻ 26 q24 ∷
   rw⁻ 25 q10 ∷
   rw⁻ 24 q10 ∷
   rw⁻ 23 q11 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q12 ∷
   rw 23 q13 ∷
   rw⁻ 22 q12 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw⁻ 21 q11 ∷
   rw⁻ 20 q11 ∷
   re 19 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q12 ∷
   rw 20 q14 ∷
   rw⁻ 19 q12 ∷
   re 20 3 (CK31 ∷ []) ∷
   rw⁻ 18 q11 ∷
   rw⁻ 17 q11 ∷
   re 16 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q12 ∷
   rw 17 q15 ∷
   rw⁻ 16 q12 ∷
   re 17 3 (CS13⁻ ∷ []) ∷
   rw⁻ 15 q11 ∷
   rw⁻ 14 q11 ∷
   re 13 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q12 ∷
   rw 14 q14 ∷
   rw⁻ 13 q12 ∷
   re 14 3 (CK31 ∷ []) ∷
   rw⁻ 12 q11 ∷
   rw⁻ 11 q11 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q12 ∷
   rw 11 q13 ∷
   rw⁻ 10 q12 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw⁻ 9 q11 ∷
   rw 10 q25 ∷
   rw 9 q10 ∷
   rw 10 q10 ∷
   rw 11 q24 ∷
   rw 12 q8 ∷
   rw 13 q11 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q12 ∷
   rw 15 q17 ∷
   rw 16 q12 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 15 q11 ∷
   rw 16 q11 ∷
   re 18 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 17 q12 ∷
   rw 18 q18 ∷
   rw 19 q12 ∷
   re 17 3 (CK30 ∷ []) ∷
   rw 18 q11 ∷
   rw 19 q11 ∷
   re 21 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q12 ∷
   rw 21 q19 ∷
   rw 22 q12 ∷
   re 20 3 (CS03⁻ ∷ []) ∷
   rw 21 q11 ∷
   rw 22 q11 ∷
   re 24 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 23 q12 ∷
   rw 24 q18 ∷
   rw 25 q12 ∷
   re 23 3 (CK30 ∷ []) ∷
   rw 24 q11 ∷
   rw 25 q11 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q12 ∷
   rw 27 q17 ∷
   rw 28 q12 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 27 q11 ∷
   rw 28 q20 ∷
   rw 29 q1 ∷
   rw 28 q2 ∷
   rw 27 q3 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q4 ∷
   rw 25 q3 ∷
   rw 24 q3 ∷
   re 23 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 25 q4 ∷
   rw 22 q3 ∷
   rw 21 q3 ∷
   re 20 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 22 q4 ∷
   rw 19 q3 ∷
   rw 18 q3 ∷
   re 17 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 19 q4 ∷
   rw 16 q3 ∷
   rw 15 q3 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q4 ∷
   rw 13 q3 ∷
   rw 14 q26 ∷
   rw⁻ 13 q2 ∷
   rw 14 q6 ∷
   rw 17 q1 ∷
   re 15 3 (CK30⁻ ∷ []) ∷
   rw 16 q6 ∷
   rw 17 q4 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = wE 2254 W
  q28 : Eqn
  q28 = wE 137 W
  q29 : Eqn
  q29 = wE 2255 W
  q30 : Eqn
  q30 = wE 139 W
  q31 : Eqn
  q31 = sE 2275 lem-pass-X3-CKd30-X3-vs-CS23-TOFF201-CSd23-TOFF201
  q32 : Eqn
  q32 = wE 2256 W
  q33 : Eqn
  q33 = wE 2257 W

-- pass [X3 CK30 X3] [X0 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X0]: 225 steps
lem-pass-X3-CK30-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ X0 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0 = derive (X3 ∷ CK30 ∷ X3 ∷ X0 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ []) (X0 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  (rw 4 q1 ∷
   rw 3 q2 ∷
   rw 2 q3 ∷
   re 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   rw 0 q3 ∷
   rw 1 q27 ∷
   rw⁻ 0 q2 ∷
   rw 1 q6 ∷
   rw 4 q1 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q6 ∷
   rw 4 q6 ∷
   rw 7 q1 ∷
   re 5 3 (CK30⁻ ∷ []) ∷
   rw 6 q6 ∷
   rw 7 q6 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q6 ∷
   rw 10 q6 ∷
   rw 13 q1 ∷
   re 11 3 (CK30⁻ ∷ []) ∷
   rw 12 q6 ∷
   rw 13 q6 ∷
   rw 16 q1 ∷
   re 14 3 (CS03⁻ ∷ []) ∷
   rw 15 q6 ∷
   rw 16 q4 ∷
   rw 20 q7 ∷
   rw⁻ 19 q8 ∷
   rw⁻ 18 q8 ∷
   rw⁻ 17 q9 ∷
   rw⁻ 16 q10 ∷
   rw⁻ 15 q11 ∷
   re 14 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q12 ∷
   rw 15 q15 ∷
   rw⁻ 14 q12 ∷
   re 15 3 (CS13⁻ ∷ []) ∷
   rw⁻ 13 q11 ∷
   rw⁻ 12 q11 ∷
   re 11 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q12 ∷
   rw 12 q28 ∷
   rw⁻ 11 q12 ∷
   re 12 3 (CK31⁻ ∷ []) ∷
   rw⁻ 10 q11 ∷
   rw⁻ 9 q11 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q12 ∷
   rw 9 q13 ∷
   rw⁻ 8 q12 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 7 q11 ∷
   rw⁻ 6 q11 ∷
   re 5 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q12 ∷
   rw 6 q28 ∷
   rw⁻ 5 q12 ∷
   re 6 3 (CK31⁻ ∷ []) ∷
   rw⁻ 4 q11 ∷
   rw⁻ 3 q11 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q12 ∷
   rw 3 q15 ∷
   rw⁻ 2 q12 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 1 q11 ∷
   rw 2 q29 ∷
   rw 1 q10 ∷
   rw 2 q9 ∷
   rw 3 q8 ∷
   rw 4 q8 ∷
   rw 5 q11 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q12 ∷
   rw 7 q19 ∷
   rw 8 q12 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   rw 7 q11 ∷
   rw 8 q11 ∷
   re 10 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   rw 10 q30 ∷
   rw 11 q12 ∷
   re 9 3 (CK30⁻ ∷ []) ∷
   rw 10 q11 ∷
   rw 11 q11 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q12 ∷
   rw 13 q17 ∷
   rw 14 q12 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q11 ∷
   rw 14 q11 ∷
   re 16 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q12 ∷
   rw 16 q30 ∷
   rw 17 q12 ∷
   re 15 3 (CK30⁻ ∷ []) ∷
   rw 16 q11 ∷
   rw 17 q11 ∷
   re 19 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q12 ∷
   rw 19 q19 ∷
   rw 20 q12 ∷
   re 18 3 (CS03⁻ ∷ []) ∷
   rw 19 q11 ∷
   rw 20 q20 ∷
   rw 17 q23 ∷
   rw 14 q31 ∷
   rw 11 q21 ∷
   rw 8 q31 ∷
   rw 5 q23 ∷
   rw 28 q7 ∷
   rw⁻ 27 q8 ∷
   rw⁻ 26 q24 ∷
   rw⁻ 25 q10 ∷
   rw⁻ 24 q10 ∷
   rw⁻ 23 q11 ∷
   re 22 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q12 ∷
   rw 23 q15 ∷
   rw⁻ 22 q12 ∷
   re 23 3 (CS13⁻ ∷ []) ∷
   rw⁻ 21 q11 ∷
   rw⁻ 20 q11 ∷
   re 19 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q12 ∷
   rw 20 q28 ∷
   rw⁻ 19 q12 ∷
   re 20 3 (CK31⁻ ∷ []) ∷
   rw⁻ 18 q11 ∷
   rw⁻ 17 q11 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q12 ∷
   rw 17 q13 ∷
   rw⁻ 16 q12 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw⁻ 15 q11 ∷
   rw⁻ 14 q11 ∷
   re 13 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q12 ∷
   rw 14 q28 ∷
   rw⁻ 13 q12 ∷
   re 14 3 (CK31⁻ ∷ []) ∷
   rw⁻ 12 q11 ∷
   rw⁻ 11 q11 ∷
   re 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q12 ∷
   rw 11 q15 ∷
   rw⁻ 10 q12 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q11 ∷
   rw 10 q32 ∷
   rw 9 q10 ∷
   rw 10 q10 ∷
   rw 11 q24 ∷
   rw 12 q8 ∷
   rw 13 q11 ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q12 ∷
   rw 15 q19 ∷
   rw 16 q12 ∷
   re 14 3 (CS03⁻ ∷ []) ∷
   rw 15 q11 ∷
   rw 16 q11 ∷
   re 18 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q12 ∷
   rw 18 q30 ∷
   rw 19 q12 ∷
   re 17 3 (CK30⁻ ∷ []) ∷
   rw 18 q11 ∷
   rw 19 q11 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q12 ∷
   rw 21 q17 ∷
   rw 22 q12 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 21 q11 ∷
   rw 22 q11 ∷
   re 24 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 23 q12 ∷
   rw 24 q30 ∷
   rw 25 q12 ∷
   re 23 3 (CK30⁻ ∷ []) ∷
   rw 24 q11 ∷
   rw 25 q11 ∷
   re 27 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 26 q12 ∷
   rw 27 q19 ∷
   rw 28 q12 ∷
   re 26 3 (CS03⁻ ∷ []) ∷
   rw 27 q11 ∷
   rw 28 q20 ∷
   rw 29 q1 ∷
   rw 28 q2 ∷
   rw 27 q3 ∷
   re 26 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 28 q4 ∷
   rw 25 q3 ∷
   rw 24 q3 ∷
   re 23 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 25 q4 ∷
   rw 22 q3 ∷
   rw 21 q3 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q4 ∷
   rw 19 q3 ∷
   rw 18 q3 ∷
   re 17 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q4 ∷
   rw 16 q3 ∷
   rw 15 q3 ∷
   re 14 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q4 ∷
   rw 13 q3 ∷
   rw 14 q33 ∷
   rw⁻ 13 q2 ∷
   rw 14 q6 ∷
   rw 17 q1 ∷
   re 15 3 (CK30 ∷ []) ∷
   rw 16 q6 ∷
   rw 17 q4 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = wE 2258 W
  q35 : Eqn
  q35 = wE 2259 W
  q36 : Eqn
  q36 = wE 2260 W
  q37 : Eqn
  q37 = wE 2261 W

-- pass [X3 CS30 X3] [X0 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X0]: 151 steps
lem-pass-X3-CS30-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ X0 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0 = derive (X3 ∷ CS03 ∷ X3 ∷ X0 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ []) (X0 ∷ S2⁻ ∷ K2⁻ ∷ S2 ∷ S2 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S2⁻ ∷ S2⁻ ∷ K2 ∷ S2 ∷ X0 ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  (rw 4 q1 ∷
   rw 3 q2 ∷
   rw 2 q3 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   rw 0 q3 ∷
   rw 1 q34 ∷
   rw⁻ 0 q2 ∷
   rw 1 q6 ∷
   rw 4 q1 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q6 ∷
   rw 4 q6 ∷
   rw 7 q1 ∷
   re 5 3 (CK30⁻ ∷ []) ∷
   rw 6 q6 ∷
   rw 7 q6 ∷
   rw 10 q1 ∷
   re 8 3 (CK30⁻ ∷ []) ∷
   rw 9 q6 ∷
   rw 10 q4 ∷
   rw 14 q7 ∷
   rw⁻ 13 q8 ∷
   rw⁻ 12 q8 ∷
   rw⁻ 11 q9 ∷
   rw⁻ 10 q10 ∷
   rw⁻ 9 q11 ∷
   re 8 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q12 ∷
   rw 9 q28 ∷
   rw⁻ 8 q12 ∷
   re 9 3 (CK31⁻ ∷ []) ∷
   rw⁻ 7 q11 ∷
   rw⁻ 6 q11 ∷
   re 5 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q12 ∷
   rw 6 q28 ∷
   rw⁻ 5 q12 ∷
   re 6 3 (CK31⁻ ∷ []) ∷
   rw⁻ 4 q11 ∷
   rw⁻ 3 q11 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q12 ∷
   rw 3 q15 ∷
   rw⁻ 2 q12 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 1 q11 ∷
   rw 2 q35 ∷
   rw 1 q10 ∷
   rw 2 q9 ∷
   rw 3 q8 ∷
   rw 4 q8 ∷
   rw 5 q11 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q12 ∷
   rw 7 q19 ∷
   rw 8 q12 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   rw 7 q11 ∷
   rw 8 q11 ∷
   re 10 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   rw 10 q30 ∷
   rw 11 q12 ∷
   re 9 3 (CK30⁻ ∷ []) ∷
   rw 10 q11 ∷
   rw 11 q11 ∷
   re 13 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q12 ∷
   rw 13 q30 ∷
   rw 14 q12 ∷
   re 12 3 (CK30⁻ ∷ []) ∷
   rw 13 q11 ∷
   rw 14 q20 ∷
   rw 11 q31 ∷
   rw 8 q31 ∷
   rw 5 q23 ∷
   rw 22 q7 ∷
   rw⁻ 21 q8 ∷
   rw⁻ 20 q24 ∷
   rw⁻ 19 q10 ∷
   rw⁻ 18 q10 ∷
   rw⁻ 17 q11 ∷
   re 16 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q12 ∷
   rw 17 q28 ∷
   rw⁻ 16 q12 ∷
   re 17 3 (CK31⁻ ∷ []) ∷
   rw⁻ 15 q11 ∷
   rw⁻ 14 q11 ∷
   re 13 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q12 ∷
   rw 14 q28 ∷
   rw⁻ 13 q12 ∷
   re 14 3 (CK31⁻ ∷ []) ∷
   rw⁻ 12 q11 ∷
   rw⁻ 11 q11 ∷
   re 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q12 ∷
   rw 11 q15 ∷
   rw⁻ 10 q12 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q11 ∷
   rw 10 q36 ∷
   rw 9 q10 ∷
   rw 10 q10 ∷
   rw 11 q24 ∷
   rw 12 q8 ∷
   rw 13 q11 ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q12 ∷
   rw 15 q19 ∷
   rw 16 q12 ∷
   re 14 3 (CS03⁻ ∷ []) ∷
   rw 15 q11 ∷
   rw 16 q11 ∷
   re 18 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q12 ∷
   rw 18 q30 ∷
   rw 19 q12 ∷
   re 17 3 (CK30⁻ ∷ []) ∷
   rw 18 q11 ∷
   rw 19 q11 ∷
   re 21 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q12 ∷
   rw 21 q30 ∷
   rw 22 q12 ∷
   re 20 3 (CK30⁻ ∷ []) ∷
   rw 21 q11 ∷
   rw 22 q20 ∷
   rw 23 q1 ∷
   rw 22 q2 ∷
   rw 21 q3 ∷
   re 20 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 22 q4 ∷
   rw 19 q3 ∷
   rw 18 q3 ∷
   re 17 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q4 ∷
   rw 16 q3 ∷
   rw 15 q3 ∷
   re 14 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q4 ∷
   rw 13 q3 ∷
   rw 14 q37 ∷
   rw⁻ 13 q2 ∷
   rw 14 q6 ∷
   rw 17 q1 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 16 q6 ∷
   rw 17 q4 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = wE 1466 W
  q39 : Eqn
  q39 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q40 : Eqn
  q40 = sE 2274 lem-pass-X2-CSd20-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3
  q41 : Eqn
  q41 = wE 1467 W

-- pass [CSd20] [X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2 X3]: 5 steps
lem-pass-CSd20-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : ⟪ (CS02⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd20-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = derive (CS02⁻ ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ CS02⁻ ∷ [])
  (rw 0 q38 ∷
   rw 13 q39 ∷
   rw 1 q40 ∷
   rw 11 q41 ∷
   rw⁻ 10 q39 ∷ []) Eq.refl
