{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD741 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D741 (W : Ws) (Sᴰ : SD741) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Four.Str using (ℓ)

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-CS12 : St 397
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-CS12 = pickᴰ 0 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-CSd12 : St 399
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-CSd12 = pickᴰ 1 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CS12-X2 : St 2426
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CS12-X2 = pickᴰ 2 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd12-X2 : St 2427
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd12-X2 = pickᴰ 3 Sᴰ
  lem-pass-X3-CK31-X3-vs-CS13-TOFF102-CSd13-TOFF102 : St 907
  lem-pass-X3-CK31-X3-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 4 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X2-CS12-X2 : St 2428
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X2-CS12-X2 = pickᴰ 5 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X2-CSd12-X2 : St 2429
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X2-CSd12-X2 = pickᴰ 6 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS12-X2 : St 2430
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS12-X2 = pickᴰ 7 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd12-X2 : St 2431
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd12-X2 = pickᴰ 8 Sᴰ
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 1131
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 9 Sᴰ
  lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 1175
  lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 10 Sᴰ
  lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 1191
  lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 11 Sᴰ
  lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 1195
  lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 12 Sᴰ
  lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 1197
  lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 13 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-TOFF103-X0-X3 : St 2157
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-TOFF103-X0-X3 = pickᴰ 14 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-TOFF103-X0-X3 : St 2305
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-TOFF103-X0-X3 = pickᴰ 15 Sᴰ
  lem-pass-X3-CKd31-X3-vs-CS13-TOFF102-CSd13-TOFF102 : St 1386
  lem-pass-X3-CKd31-X3-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 16 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X0-X3-TOFF103-X0-X3 : St 2160
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X0-X3-TOFF103-X0-X3 = pickᴰ 17 Sᴰ
  lem-S2-at1023-ᵖ-1 : St 2083
  lem-S2-at1023-ᵖ-1 = pickᴰ 18 Sᴰ
  lem-pass-X1-CK10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 2240
  lem-pass-X1-CK10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 19 Sᴰ
  lem-pass-X2-CKd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 2244
  lem-pass-X2-CKd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 20 Sᴰ
  lem-pass-X2-CK21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 2296
  lem-pass-X2-CK21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 21 Sᴰ
  lem-pass-X3-CK30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : St 2264
  lem-pass-X3-CK30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = pickᴰ 22 Sᴰ
  lem-pass-X3-CS31-X3-vs-CS13-TOFF102-CSd13-TOFF102 : St 2267
  lem-pass-X3-CS31-X3-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 23 Sᴰ
  lem-distribute-Gad⟨t≡1-W≡⟨0-3⟩-d≡1-e≡-1⟩-CS12-TOFF103-CSd12-TOFF103 : St 2342
  lem-distribute-Gad⟨t≡1-W≡⟨0-3⟩-d≡1-e≡-1⟩-CS12-TOFF103-CSd12-TOFF103 = pickᴰ 24 Sᴰ
  lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡-1⟩-CS12-TOFF103-CSd12-TOFF103 : St 2413
  lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡-1⟩-CS12-TOFF103-CSd12-TOFF103 = pickᴰ 25 Sᴰ
  lem-pass-X3-CKd31-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : St 2432
  lem-pass-X3-CKd31-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = pickᴰ 26 Sᴰ
  lem-pass-X3-CSd31-X3-vs-CS13-TOFF102-CSd13-TOFF102 : St 2424
  lem-pass-X3-CSd31-X3-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 27 Sᴰ
  lem-pass-X2-CK20-X2-vs-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0 : St 2433
  lem-pass-X2-CK20-X2-vs-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0 = pickᴰ 28 Sᴰ
  lem-pass-X2-CKd20-X2-vs-S0-S0-Kd0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-K0-Sd0-Sd0 : St 2434
  lem-pass-X2-CKd20-X2-vs-S0-S0-Kd0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-K0-Sd0-Sd0 = pickᴰ 29 Sᴰ
  lem-pass-X3-CK31-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : St 2435
  lem-pass-X3-CK31-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = pickᴰ 30 Sᴰ
  lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-S0 : St 2436
  lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-S0 = pickᴰ 31 Sᴰ
  lem-pass-X3-CSd30-X3-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2 : St 2437
  lem-pass-X3-CSd30-X3-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2 = pickᴰ 32 Sᴰ

private
  q1 : Eqn
  q1 = sE 2083 lem-S2-at1023-ᵖ-1
  q2 : Eqn
  q2 = wE 1102 W
  q3 : Eqn
  q3 = eqn (ℓ "丌丘") (ℓ "丘丌") (low₁-comm (X) ((X ↑)))
  q4 : Eqn
  q4 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q5 : Eqn
  q5 = eqn (ℓ "丌丶") (ℓ "丶丌") (low₁-comm (X) (CS))
  q6 : Eqn
  q6 = wE 387 W
  q7 : Eqn
  q7 = eqn (ℓ "丶丞") (ℓ "丞丶") (low₃-comm ((CS ↑)) (X))
  q8 : Eqn
  q8 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q9 : Eqn
  q9 = wE 390 W
  q10 : Eqn
  q10 = wE 1609 W
  q11 : Eqn
  q11 = eqn (ℓ "习丞") (ℓ "丞习") (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))
  q12 : Eqn
  q12 = wE 173 W
  q13 : Eqn
  q13 = wE 389 W
  q14 : Eqn
  q14 = eqn (ℓ "丌丷") (ℓ "丷丌") (low₁-comm (X) ((CS • CS • CS)))
  q15 : Eqn
  q15 = eqn (ℓ "丷丞") (ℓ "丞丷") (low₃-comm (((CS • CS • CS) ↑)) (X))
  q16 : Eqn
  q16 = sE 2428 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X2-CS12-X2
  q17 : Eqn
  q17 = sE 2160 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X0-X3-TOFF103-X0-X3
  q18 : Eqn
  q18 = sE 2429 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X2-CSd12-X2
  q19 : Eqn
  q19 = sE 2413 lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡-1⟩-CS12-TOFF103-CSd12-TOFF103

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X0 X2 X3 CS13 TOFF102 CSd13 TOFF102 X0 X2 X3]: 39 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丌丘丞丽习举习丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丽习举习丌丘丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丌丘丞丽习举习丌丘丞") (ℓ "丌丘丞丽习举习丌丘丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 34 q1 ∷
   rw 35 q2 ∷
   rw 42 q2 ∷
   rw 49 q2 ∷
   rw 31 q3 ∷
   rw 32 q4 ∷
   rw 33 q5 ∷
   rw 34 q6 ∷
   rw⁻ 32 q7 ∷
   rw⁻ 33 q8 ∷
   rw 34 q9 ∷
   rw 35 q8 ∷
   re 37 1 (ℓ "乏习乏") ∷
   rw 36 q10 ∷
   rw⁻ 37 q11 ∷
   rw 38 q12 ∷
   re 36 3 (ℓ "乡") ∷
   rw⁻ 37 q3 ∷
   rw 38 q13 ∷
   rw 39 q3 ∷
   rw 40 q4 ∷
   rw 41 q14 ∷
   rw 42 q6 ∷
   rw⁻ 40 q15 ∷
   rw⁻ 41 q8 ∷
   rw 42 q9 ∷
   rw 43 q8 ∷
   re 45 1 (ℓ "乏习乏") ∷
   rw 44 q10 ∷
   rw⁻ 45 q11 ∷
   rw 46 q12 ∷
   re 44 3 (ℓ "乡") ∷
   rw⁻ 45 q3 ∷
   rw 46 q13 ∷
   rw 0 q16 ∷
   rw 3 q17 ∷
   rw 8 q18 ∷
   rw 11 q17 ∷
   rw⁻ 0 q19 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = sE 2426 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CS12-X2
  q21 : Eqn
  q21 = sE 2157 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-TOFF103-X0-X3
  q22 : Eqn
  q22 = sE 2427 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd12-X2

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X0 X2 X3 CS13 TOFF102 CSd13 TOFF102 X0 X2 X3]: 39 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丌丘丞丽习举习丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丽习举习丌丘丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丌丘丞丽习举习丌丘丞") (ℓ "丌丘丞丽习举习丌丘丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 32 q1 ∷
   rw 33 q2 ∷
   rw 40 q2 ∷
   rw 47 q2 ∷
   rw 29 q3 ∷
   rw 30 q4 ∷
   rw 31 q5 ∷
   rw 32 q6 ∷
   rw⁻ 30 q7 ∷
   rw⁻ 31 q8 ∷
   rw 32 q9 ∷
   rw 33 q8 ∷
   re 35 1 (ℓ "乏习乏") ∷
   rw 34 q10 ∷
   rw⁻ 35 q11 ∷
   rw 36 q12 ∷
   re 34 3 (ℓ "乡") ∷
   rw⁻ 35 q3 ∷
   rw 36 q13 ∷
   rw 37 q3 ∷
   rw 38 q4 ∷
   rw 39 q14 ∷
   rw 40 q6 ∷
   rw⁻ 38 q15 ∷
   rw⁻ 39 q8 ∷
   rw 40 q9 ∷
   rw 41 q8 ∷
   re 43 1 (ℓ "乏习乏") ∷
   rw 42 q10 ∷
   rw⁻ 43 q11 ∷
   rw 44 q12 ∷
   re 42 3 (ℓ "乡") ∷
   rw⁻ 43 q3 ∷
   rw 44 q13 ∷
   rw 0 q20 ∷
   rw 3 q21 ∷
   rw 8 q22 ∷
   rw 11 q21 ∷
   rw⁻ 0 q19 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = wE 1940 W
  q24 : Eqn
  q24 = sE 2432 lem-pass-X3-CKd31-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0
  q25 : Eqn
  q25 = wE 1941 W

-- pass [CKd31] [X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X3]: 3 steps
lem-pass-CKd31-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : ⟪ (ℓ "乕丞三下丈丈中九丮九三三上丈丞") ⟫ʷ ≈ ⟪ (ℓ "丞三下丈丈中九丮九三三上丈丞乕") ⟫ʷ
lem-pass-CKd31-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = derive (ℓ "乕丞三下丈丈中九丮九三三上丈丞") (ℓ "丞三下丈丈中九丮九三三上丈丞乕")
  (rw 0 q23 ∷
   rw 1 q24 ∷
   rw 13 q25 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = wE 1366 W
  q27 : Eqn
  q27 = sE 2435 lem-pass-X3-CK31-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0
  q28 : Eqn
  q28 = wE 1367 W

-- pass [CK31] [X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X3]: 3 steps
lem-pass-CK31-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : ⟪ (ℓ "乔丞三下丈丈中九丮九三三上丈丞") ⟫ʷ ≈ ⟪ (ℓ "丞三下丈丈中九丮九三三上丈丞乔") ⟫ʷ
lem-pass-CK31-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = derive (ℓ "乔丞三下丈丈中九丮九三三上丈丞") (ℓ "丞三下丈丈中九丮九三三上丈丞乔")
  (rw 0 q26 ∷
   rw 1 q27 ∷
   rw 13 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 2161 W
  q30 : Eqn
  q30 = wE 2162 W
  q31 : Eqn
  q31 = sE 2240 lem-pass-X1-CK10-X1-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [X1 CK10 X1] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 5 steps
lem-pass-X1-CK10-X1-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (ℓ "丒临丒丞中九丮九丞") ⟫ʷ ≈ ⟪ (ℓ "丞中九丮九丞丒临丒") ⟫ʷ
lem-pass-X1-CK10-X1-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (ℓ "丒临丒丞中九丮九丞") (ℓ "丞中九丮九丞丒临丒")
  (rw 0 q29 ∷
   rw 1 q30 ∷
   rw 1 q31 ∷
   rw 5 q30 ∷
   rw 5 q29 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = wE 2160 W

-- pass [X1 CK10 X1] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 5 steps
lem-pass-X1-CK10-X1-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (ℓ "丒临丒丘中九丮九丘") ⟫ʷ ≈ ⟪ (ℓ "丘中九丮九丘丒临丒") ⟫ʷ
lem-pass-X1-CK10-X1-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = derive (ℓ "丒临丒丘中九丮九丘") (ℓ "丘中九丮九丘丒临丒")
  (rw 0 q32 ∷
   rw 1 q30 ∷
   rw 1 q31 ∷
   rw 5 q30 ∷
   rw 5 q32 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = wE 1 W
  q34 : Eqn
  q34 = wE 3 W
  q35 : Eqn
  q35 = wE 1466 W
  q36 : Eqn
  q36 = wE 175 W
  q37 : Eqn
  q37 = sE 2437 lem-pass-X3-CSd30-X3-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2
  q38 : Eqn
  q38 = wE 1467 W

-- pass [CSd30] [X2 X3 Kd0 CS03 TOFF012 CSd03 TOFF012 K0 X2 X3]: 25 steps
lem-pass-CSd30-vs-X2-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2-X3 : ⟪ (ℓ "丮丘丞下中九丮九上丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞下中九丮九上丘丞丮") ⟫ʷ
lem-pass-CSd30-vs-X2-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2-X3 = derive (ℓ "丮丘丞下中九丮九上丘丞") (ℓ "丘丞下中九丮九上丘丞丮")
  (rw 1 q8 ∷
   rw 2 q33 ∷
   rw 1 q12 ∷
   re 0 1 (ℓ "乏丨乏") ∷
   rw 2 q34 ∷
   rw 1 q35 ∷
   rw 0 q36 ∷
   rw 1 q36 ∷
   rw 4 q33 ∷
   re 2 3 (ℓ "丮") ∷
   rw 3 q36 ∷
   rw 4 q34 ∷
   rw 1 q37 ∷
   rw 13 q33 ∷
   rw 12 q12 ∷
   rw 11 q12 ∷
   re 10 1 (ℓ "乏丨乏") ∷
   rw 12 q34 ∷
   rw 9 q12 ∷
   rw 10 q38 ∷
   rw 9 q36 ∷
   rw 12 q33 ∷
   re 10 3 (ℓ "丮") ∷
   rw 11 q34 ∷
   rw⁻ 0 q8 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q40 : Eqn
  q40 = wE 1833 W
  q41 : Eqn
  q41 = wE 2354 W
  q42 : Eqn
  q42 = sE 907 lem-pass-X3-CK31-X3-vs-CS13-TOFF102-CSd13-TOFF102
  q43 : Eqn
  q43 = sE 2267 lem-pass-X3-CS31-X3-vs-CS13-TOFF102-CSd13-TOFF102
  q44 : Eqn
  q44 = sE 2424 lem-pass-X3-CSd31-X3-vs-CS13-TOFF102-CSd13-TOFF102
  q45 : Eqn
  q45 = wE 2355 W

-- pass [X3 CKd31 X3] [X0 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0]: 33 steps
lem-pass-X3-CKd31-X3-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 : ⟪ (ℓ "丞乕丞丌丏丑与与丽习举习丏丏丐与丌") ⟫ʷ ≈ ⟪ (ℓ "丌丏丑与与丽习举习丏丏丐与丌丞乕丞") ⟫ʷ
lem-pass-X3-CKd31-X3-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 = derive (ℓ "丞乕丞丌丏丑与与丽习举习丏丏丐与丌") (ℓ "丌丏丑与与丽习举习丏丏丐与丌丞乕丞")
  (rw 4 q33 ∷
   rw 3 q39 ∷
   rw 2 q12 ∷
   re 1 1 (ℓ "乏么乏") ∷
   rw 3 q34 ∷
   rw 0 q12 ∷
   rw 1 q40 ∷
   rw⁻ 0 q39 ∷
   rw 1 q36 ∷
   rw 4 q33 ∷
   re 2 3 (ℓ "乕") ∷
   rw 3 q36 ∷
   rw 4 q34 ∷
   rw 1 q41 ∷
   rw 17 q42 ∷
   rw 14 q43 ∷
   rw 11 q43 ∷
   rw 8 q42 ∷
   rw 5 q44 ∷
   rw 9 q45 ∷
   rw 17 q33 ∷
   rw 16 q39 ∷
   rw 15 q12 ∷
   re 14 1 (ℓ "乏么乏") ∷
   rw 16 q34 ∷
   rw 13 q12 ∷
   rw 14 q40 ∷
   rw⁻ 13 q39 ∷
   rw 14 q36 ∷
   rw 17 q33 ∷
   re 15 3 (ℓ "乕") ∷
   rw 16 q36 ∷
   rw 17 q34 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = wE 1533 W
  q47 : Eqn
  q47 = wE 2356 W
  q48 : Eqn
  q48 = sE 1386 lem-pass-X3-CKd31-X3-vs-CS13-TOFF102-CSd13-TOFF102
  q49 : Eqn
  q49 = wE 2357 W

-- pass [X3 CK31 X3] [X0 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0]: 33 steps
lem-pass-X3-CK31-X3-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 : ⟪ (ℓ "丞乔丞丌丏丑与与丽习举习丏丏丐与丌") ⟫ʷ ≈ ⟪ (ℓ "丌丏丑与与丽习举习丏丏丐与丌丞乔丞") ⟫ʷ
lem-pass-X3-CK31-X3-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 = derive (ℓ "丞乔丞丌丏丑与与丽习举习丏丏丐与丌") (ℓ "丌丏丑与与丽习举习丏丏丐与丌丞乔丞")
  (rw 4 q33 ∷
   rw 3 q39 ∷
   rw 2 q12 ∷
   re 1 1 (ℓ "乏乇乏") ∷
   rw 3 q34 ∷
   rw 0 q12 ∷
   rw 1 q46 ∷
   rw⁻ 0 q39 ∷
   rw 1 q36 ∷
   rw 4 q33 ∷
   re 2 3 (ℓ "乔") ∷
   rw 3 q36 ∷
   rw 4 q34 ∷
   rw 1 q47 ∷
   rw 17 q43 ∷
   rw 14 q48 ∷
   rw 11 q43 ∷
   rw 8 q43 ∷
   rw 5 q48 ∷
   rw 9 q49 ∷
   rw 17 q33 ∷
   rw 16 q39 ∷
   rw 15 q12 ∷
   re 14 1 (ℓ "乏乇乏") ∷
   rw 16 q34 ∷
   rw 13 q12 ∷
   rw 14 q46 ∷
   rw⁻ 13 q39 ∷
   rw 14 q36 ∷
   rw 17 q33 ∷
   re 15 3 (ℓ "乔") ∷
   rw 16 q36 ∷
   rw 17 q34 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = wE 2071 W
  q51 : Eqn
  q51 = sE 397 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-CS12
  q52 : Eqn
  q52 = sE 2305 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-TOFF103-X0-X3
  q53 : Eqn
  q53 = sE 399 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-CSd12
  q54 : Eqn
  q54 = sE 2342 lem-distribute-Gad⟨t≡1-W≡⟨0-3⟩-d≡1-e≡-1⟩-CS12-TOFF103-CSd12-TOFF103

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X0 X3 CS13 TOFF102 CSd13 TOFF102 X0 X3]: 19 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丌丞丽习举习丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丽习举习丌丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丌丞丽习举习丌丞") (ℓ "丌丞丽习举习丌丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 33 q1 ∷
   rw 34 q50 ∷
   rw 39 q50 ∷
   rw 44 q50 ∷
   rw 31 q4 ∷
   rw 32 q5 ∷
   rw 33 q6 ∷
   rw⁻ 31 q7 ∷
   rw 32 q9 ∷
   rw 37 q4 ∷
   rw 38 q14 ∷
   rw 39 q6 ∷
   rw⁻ 37 q15 ∷
   rw 38 q9 ∷
   rw 0 q51 ∷
   rw 1 q52 ∷
   rw 6 q53 ∷
   rw 7 q52 ∷
   rw⁻ 0 q54 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = wE 2291 W
  q56 : Eqn
  q56 = sE 2296 lem-pass-X2-CK21-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q57 : Eqn
  q57 = sE 1195 lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q58 : Eqn
  q58 = sE 1197 lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q59 : Eqn
  q59 = wE 2292 W

-- pass [X2 CKd21 X2] [X0 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0]: 9 steps
lem-pass-X2-CKd21-X2-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 : ⟪ (ℓ "丘么丘丌丏丑与与丽习举习丏丏丐与丌") ⟫ʷ ≈ ⟪ (ℓ "丌丏丑与与丽习举习丏丏丐与丌丘么丘") ⟫ʷ
lem-pass-X2-CKd21-X2-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 = derive (ℓ "丘么丘丌丏丑与与丽习举习丏丏丐与丌") (ℓ "丌丏丑与与丽习举习丏丏丐与丌丘么丘")
  (rw 0 q40 ∷
   rw 1 q55 ∷
   rw 17 q56 ∷
   rw 14 q57 ∷
   rw 11 q57 ∷
   rw 8 q56 ∷
   rw 5 q58 ∷
   rw 9 q59 ∷
   rw 13 q40 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = wE 1677 W

-- pass [X3 CKd31 X3] [X0 X2 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2]: 35 steps
lem-pass-X3-CKd31-X3-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 : ⟪ (ℓ "丞乕丞丌丘丏丑与与丽习举习丏丏丐与丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘丏丑与与丽习举习丏丏丐与丌丘丞乕丞") ⟫ʷ
lem-pass-X3-CKd31-X3-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 = derive (ℓ "丞乕丞丌丘丏丑与与丽习举习丏丏丐与丌丘") (ℓ "丌丘丏丑与与丽习举习丏丏丐与丌丘丞乕丞")
  (rw 4 q33 ∷
   rw 3 q39 ∷
   rw 2 q12 ∷
   re 1 1 (ℓ "乏么乏") ∷
   rw 3 q34 ∷
   rw 0 q12 ∷
   rw 1 q40 ∷
   rw⁻ 0 q39 ∷
   rw 1 q36 ∷
   rw 4 q33 ∷
   re 2 3 (ℓ "乕") ∷
   rw 3 q36 ∷
   rw 4 q34 ∷
   rw 1 q60 ∷
   rw 2 q41 ∷
   rw 18 q42 ∷
   rw 15 q43 ∷
   rw 12 q43 ∷
   rw 9 q42 ∷
   rw 6 q44 ∷
   rw 10 q45 ∷
   rw 18 q33 ∷
   rw 17 q39 ∷
   rw 16 q12 ∷
   re 15 1 (ℓ "乏么乏") ∷
   rw 17 q34 ∷
   rw 14 q12 ∷
   rw 15 q40 ∷
   rw⁻ 14 q39 ∷
   rw 15 q36 ∷
   rw 18 q33 ∷
   re 16 3 (ℓ "乕") ∷
   rw 17 q36 ∷
   rw 18 q34 ∷
   rw 15 q60 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = wE 1412 W

-- pass [X3 CK31 X3] [X0 X2 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2]: 35 steps
lem-pass-X3-CK31-X3-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 : ⟪ (ℓ "丞乔丞丌丘丏丑与与丽习举习丏丏丐与丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘丏丑与与丽习举习丏丏丐与丌丘丞乔丞") ⟫ʷ
lem-pass-X3-CK31-X3-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 = derive (ℓ "丞乔丞丌丘丏丑与与丽习举习丏丏丐与丌丘") (ℓ "丌丘丏丑与与丽习举习丏丏丐与丌丘丞乔丞")
  (rw 4 q33 ∷
   rw 3 q39 ∷
   rw 2 q12 ∷
   re 1 1 (ℓ "乏乇乏") ∷
   rw 3 q34 ∷
   rw 0 q12 ∷
   rw 1 q46 ∷
   rw⁻ 0 q39 ∷
   rw 1 q36 ∷
   rw 4 q33 ∷
   re 2 3 (ℓ "乔") ∷
   rw 3 q36 ∷
   rw 4 q34 ∷
   rw 1 q61 ∷
   rw 2 q47 ∷
   rw 18 q43 ∷
   rw 15 q48 ∷
   rw 12 q43 ∷
   rw 9 q43 ∷
   rw 6 q48 ∷
   rw 10 q49 ∷
   rw 18 q33 ∷
   rw 17 q39 ∷
   rw 16 q12 ∷
   re 15 1 (ℓ "乏乇乏") ∷
   rw 17 q34 ∷
   rw 14 q12 ∷
   rw 15 q46 ∷
   rw⁻ 14 q39 ∷
   rw 15 q36 ∷
   rw 18 q33 ∷
   re 16 3 (ℓ "乔") ∷
   rw 17 q36 ∷
   rw 18 q34 ∷
   rw 15 q61 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = sE 2430 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS12-X2
  q63 : Eqn
  q63 = sE 2431 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd12-X2

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X0 X2 X3 CS13 TOFF102 CSd13 TOFF102 X0 X2 X3]: 39 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丌丘丞丽习举习丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丽习举习丌丘丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丌丘丞丽习举习丌丘丞") (ℓ "丌丘丞丽习举习丌丘丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 34 q1 ∷
   rw 35 q2 ∷
   rw 42 q2 ∷
   rw 49 q2 ∷
   rw 31 q3 ∷
   rw 32 q4 ∷
   rw 33 q5 ∷
   rw 34 q6 ∷
   rw⁻ 32 q7 ∷
   rw⁻ 33 q8 ∷
   rw 34 q9 ∷
   rw 35 q8 ∷
   re 37 1 (ℓ "乏习乏") ∷
   rw 36 q10 ∷
   rw⁻ 37 q11 ∷
   rw 38 q12 ∷
   re 36 3 (ℓ "乡") ∷
   rw⁻ 37 q3 ∷
   rw 38 q13 ∷
   rw 39 q3 ∷
   rw 40 q4 ∷
   rw 41 q14 ∷
   rw 42 q6 ∷
   rw⁻ 40 q15 ∷
   rw⁻ 41 q8 ∷
   rw 42 q9 ∷
   rw 43 q8 ∷
   re 45 1 (ℓ "乏习乏") ∷
   rw 44 q10 ∷
   rw⁻ 45 q11 ∷
   rw 46 q12 ∷
   re 44 3 (ℓ "乡") ∷
   rw⁻ 45 q3 ∷
   rw 46 q13 ∷
   rw 0 q62 ∷
   rw 3 q52 ∷
   rw 8 q63 ∷
   rw 11 q52 ∷
   rw⁻ 0 q19 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = wE 1709 W
  q65 : Eqn
  q65 = eqn (ℓ "下乏") (ℓ "乏下") (low₁-comm ((K • iI)) ((Swap ↑)))
  q66 : Eqn
  q66 = sE 2264 lem-pass-X3-CK30-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0
  q67 : Eqn
  q67 = wE 2358 W
  q68 : Eqn
  q68 = wE 2359 W
  q69 : Eqn
  q69 = wE 1711 W

-- CA CKd30 Gad(t=0, W=(), d=SdKdSS, e=-1): 23 steps
lem-CA-CKd30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "乒三下丈丈中九丮九三三上丈") ⟫ʷ ≈ ⟪ (ℓ "丈下三中九丮九丈上三乒") ⟫ʷ
lem-CA-CKd30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "乒三下丈丈中九丮九三三上丈") (ℓ "丈下三中九丮九丈上三乒")
  (rw 1 q33 ∷
   re 0 1 (ℓ "乏久乏") ∷
   rw 2 q34 ∷
   rw 1 q64 ∷
   rw⁻ 0 q65 ∷
   rw 1 q36 ∷
   rw 4 q33 ∷
   re 2 3 (ℓ "乑") ∷
   rw 3 q36 ∷
   rw 4 q34 ∷
   rw 1 q66 ∷
   rw 0 q67 ∷
   rw 7 q68 ∷
   rw 14 q33 ∷
   rw 13 q12 ∷
   re 12 1 (ℓ "乏乄乏") ∷
   rw 14 q34 ∷
   rw 11 q12 ∷
   rw 10 q65 ∷
   rw 11 q69 ∷
   rw 12 q33 ∷
   re 10 3 (ℓ "乒") ∷
   rw 11 q34 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = wE 2360 W
  q71 : Eqn
  q71 = sE 1191 lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012
  q72 : Eqn
  q72 = sE 1175 lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012
  q73 : Eqn
  q73 = wE 2361 W

-- pass [X1 CK10 X1] [Kd0 Sd0 CS03 TOFF012 CSd03 TOFF012 S0 K0]: 5 steps
lem-pass-X1-CK10-X1-vs-Kd0-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-K0 : ⟪ (ℓ "丒临丒下三中九丮九丈上") ⟫ʷ ≈ ⟪ (ℓ "下三中九丮九丈上丒临丒") ⟫ʷ
lem-pass-X1-CK10-X1-vs-Kd0-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-K0 = derive (ℓ "丒临丒下三中九丮九丈上") (ℓ "下三中九丮九丈上丒临丒")
  (rw 0 q70 ∷
   rw 8 q71 ∷
   rw 5 q31 ∷
   rw 2 q72 ∷
   rw 6 q73 ∷ []) Eq.refl

private
  q74 : Eqn
  q74 = sE 2433 lem-pass-X2-CK20-X2-vs-Kd0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-K0
  q75 : Eqn
  q75 = wE 2362 W
  q76 : Eqn
  q76 = wE 2363 W

-- CA CKd20 Gad(t=0, W=(), d=KdKd, e=-1): 5 steps
lem-CA-CKd20-Gad⟨t≡0-W≡⟨⟩-d≡KdKd-e≡-1⟩ : ⟪ (ℓ "久下下中九丮九上上") ⟫ʷ ≈ ⟪ (ℓ "下下下中九丮九上上上久") ⟫ʷ
lem-CA-CKd20-Gad⟨t≡0-W≡⟨⟩-d≡KdKd-e≡-1⟩ = derive (ℓ "久下下中九丮九上上") (ℓ "下下下中九丮九上上上久")
  (rw 0 q64 ∷
   rw 1 q74 ∷
   rw 0 q75 ∷
   rw 7 q76 ∷
   rw 10 q69 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = wE 2364 W
  q78 : Eqn
  q78 = wE 2365 W

-- pass [X1 CSd10 X1] [S0 Kd0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 K0 Sd0]: 5 steps
lem-pass-X1-CSd10-X1-vs-S0-Kd0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-K0-Sd0 : ⟪ (ℓ "丒両丒丈下丈中九丮九三上三") ⟫ʷ ≈ ⟪ (ℓ "丈下丈中九丮九三上三丒両丒") ⟫ʷ
lem-pass-X1-CSd10-X1-vs-S0-Kd0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-K0-Sd0 = derive (ℓ "丒両丒丈下丈中九丮九三上三") (ℓ "丈下丈中九丮九三上三丒両丒")
  (rw 0 q77 ∷
   rw 9 q72 ∷
   rw 6 q72 ∷
   rw 3 q31 ∷
   rw 7 q78 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = wE 1459 W
  q80 : Eqn
  q80 = sE 2434 lem-pass-X2-CKd20-X2-vs-S0-S0-Kd0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-K0-Sd0-Sd0
  q81 : Eqn
  q81 = wE 2366 W
  q82 : Eqn
  q82 = wE 2367 W
  q83 : Eqn
  q83 = wE 1461 W

-- CA CK20 Gad(t=0, W=(), d=SSKdS, e=-1): 5 steps
lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡SSKdS-e≡-1⟩ : ⟪ (ℓ "乄丈丈下丈中九丮九三上三三") ⟫ʷ ≈ ⟪ (ℓ "三下丈丈下中九丮九上三三上丈乄") ⟫ʷ
lem-CA-CK20-Gad⟨t≡0-W≡⟨⟩-d≡SSKdS-e≡-1⟩ = derive (ℓ "乄丈丈下丈中九丮九三上三三") (ℓ "三下丈丈下中九丮九上三三上丈乄")
  (rw 0 q79 ∷
   rw 1 q80 ∷
   rw 0 q81 ∷
   rw 9 q82 ∷
   rw 14 q83 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q85 : Eqn
  q85 = sE 2436 lem-pass-X3-CKd30-X3-vs-Sd0-Kd0-S0-S0-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-Sd0-Sd0-K0-S0
  q86 : Eqn
  q86 = wE 2368 W
  q87 : Eqn
  q87 = wE 2369 W

-- CA CK30 Gad(t=0, W=(), d=SdKdSSKd, e=-1): 23 steps
lem-CA-CK30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSSKd-e≡-1⟩ : ⟪ (ℓ "乑三下丈丈下中九丮九上三三上丈") ⟫ʷ ≈ ⟪ (ℓ "丈丈上丈中九丮九三下三三乑") ⟫ʷ
lem-CA-CK30-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSSKd-e≡-1⟩ = derive (ℓ "乑三下丈丈下中九丮九上三三上丈") (ℓ "丈丈上丈中九丮九三下三三乑")
  (rw 1 q33 ∷
   re 0 1 (ℓ "乏乄乏") ∷
   rw 2 q34 ∷
   rw 1 q79 ∷
   rw⁻ 0 q84 ∷
   rw 1 q36 ∷
   rw 4 q33 ∷
   re 2 3 (ℓ "乒") ∷
   rw 3 q36 ∷
   rw 4 q34 ∷
   rw 1 q85 ∷
   rw 0 q86 ∷
   rw 8 q87 ∷
   rw 16 q33 ∷
   rw 15 q12 ∷
   re 14 1 (ℓ "乏久乏") ∷
   rw 16 q34 ∷
   rw 13 q12 ∷
   rw 12 q84 ∷
   rw 13 q83 ∷
   rw 14 q33 ∷
   re 12 3 (ℓ "乑") ∷
   rw 13 q34 ∷ []) Eq.refl

private
  q88 : Eqn
  q88 = wE 2370 W
  q89 : Eqn
  q89 = sE 2244 lem-pass-X2-CKd20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q90 : Eqn
  q90 = sE 1131 lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q91 : Eqn
  q91 = wE 2371 W

-- pass [X2 CK20 X2] [S0 S0 K0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Kd0 Sd0 Sd0]: 7 steps
lem-pass-X2-CK20-X2-vs-S0-S0-K0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Kd0-Sd0-Sd0 : ⟪ (ℓ "丘乄丘丈丈上丈中九丮九三下三三") ⟫ʷ ≈ ⟪ (ℓ "丈丈上丈中九丮九三下三三丘乄丘") ⟫ʷ
lem-pass-X2-CK20-X2-vs-S0-S0-K0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Kd0-Sd0-Sd0 = derive (ℓ "丘乄丘丈丈上丈中九丮九三下三三") (ℓ "丈丈上丈中九丮九三下三三丘乄丘")
  (rw 0 q88 ∷
   rw 16 q89 ∷
   rw 13 q90 ∷
   rw 10 q89 ∷
   rw 7 q90 ∷
   rw 4 q90 ∷
   rw 8 q91 ∷ []) Eq.refl

private
  q92 : Eqn
  q92 = wE 2372 W
  q93 : Eqn
  q93 = wE 2373 W

-- pass [X1 CSd10 X1] [S0 S0 K0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 Kd0 Sd0 Sd0]: 5 steps
lem-pass-X1-CSd10-X1-vs-S0-S0-K0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-Kd0-Sd0-Sd0 : ⟪ (ℓ "丒両丒丈丈上丈丈中九丮九三三下三三") ⟫ʷ ≈ ⟪ (ℓ "丈丈上丈丈中九丮九三三下三三丒両丒") ⟫ʷ
lem-pass-X1-CSd10-X1-vs-S0-S0-K0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-Kd0-Sd0-Sd0 = derive (ℓ "丒両丒丈丈上丈丈中九丮九三三下三三") (ℓ "丈丈上丈丈中九丮九三三下三三丒両丒")
  (rw 0 q92 ∷
   rw 11 q71 ∷
   rw 8 q31 ∷
   rw 5 q71 ∷
   rw 9 q93 ∷ []) Eq.refl
