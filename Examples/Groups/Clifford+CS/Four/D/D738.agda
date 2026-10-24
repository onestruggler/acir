{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD738 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D738 (W : Ws) (Sᴰ : SD738) where

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
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS12 : St 200
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS12 = pickᴰ 0 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CSd12 : St 201
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CSd12 = pickᴰ 1 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CS12 : St 244
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CS12 = pickᴰ 2 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CSd12 : St 245
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CSd12 = pickᴰ 3 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-CS12 : St 397
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-CS12 = pickᴰ 4 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-CSd12 : St 399
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-CSd12 = pickᴰ 5 Sᴰ
  lem-pass-CCZ123-vs-X3-CK32-X3 : St 2336
  lem-pass-CCZ123-vs-X3-CK32-X3 = pickᴰ 6 Sᴰ
  lem-pass-CCZ123-vs-X3-CKd32-X3 : St 2337
  lem-pass-CCZ123-vs-X3-CKd32-X3 = pickᴰ 7 Sᴰ
  lem-pass-CCZ123-vs-X3-CS23-X3 : St 2338
  lem-pass-CCZ123-vs-X3-CS23-X3 = pickᴰ 8 Sᴰ
  lem-pass-CCZ123-vs-X3-CSd23-X3 : St 2339
  lem-pass-CCZ123-vs-X3-CSd23-X3 = pickᴰ 9 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-TOFF203-X0-X3 : St 2173
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-TOFF203-X0-X3 = pickᴰ 10 Sᴰ
  lem-pass-CK30-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : St 2362
  lem-pass-CK30-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = pickᴰ 11 Sᴰ
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 1131
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 12 Sᴰ
  lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 1143
  lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 13 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-TOFF103-X0-X3 : St 2157
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-TOFF103-X0-X3 = pickᴰ 14 Sᴰ
  lem-CA-CS20-Gad⟨t≡0-W≡⟨3⟩-d≡Sd-e≡1⟩ : St 2363
  lem-CA-CS20-Gad⟨t≡0-W≡⟨3⟩-d≡Sd-e≡1⟩ = pickᴰ 15 Sᴰ
  lem-CA-CSd20-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡1⟩ : St 2364
  lem-CA-CSd20-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡1⟩ = pickᴰ 16 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-TOFF203-X0-X3 : St 2159
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-TOFF203-X0-X3 = pickᴰ 17 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-TOFF203-X0-X3 : St 2178
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-TOFF203-X0-X3 = pickᴰ 18 Sᴰ
  lem-S2-at1023-ᵖ-1 : St 2083
  lem-S2-at1023-ᵖ-1 = pickᴰ 19 Sᴰ
  lem-S2-at2013-ᵖ-1 : St 2085
  lem-S2-at2013-ᵖ-1 = pickᴰ 20 Sᴰ
  lem-pass-CCZ123-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : St 2140
  lem-pass-CCZ123-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = pickᴰ 21 Sᴰ
  lem-pass-X2-CKd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 2244
  lem-pass-X2-CKd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 22 Sᴰ
  lem-pass-X2-CK21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 2296
  lem-pass-X2-CK21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 23 Sᴰ
  lem-distribute-Gad⟨t≡1-W≡⟨0-3⟩-d≡1-e≡-1⟩-CS12-TOFF103-CSd12-TOFF103 : St 2342
  lem-distribute-Gad⟨t≡1-W≡⟨0-3⟩-d≡1-e≡-1⟩-CS12-TOFF103-CSd12-TOFF103 = pickᴰ 24 Sᴰ
  lem-pass-X2-CK23-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 2350
  lem-pass-X2-CK23-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 25 Sᴰ
  lem-pass-X2-CKd23-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 2351
  lem-pass-X2-CKd23-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 26 Sᴰ
  lem-pass-X2-CS23-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 2352
  lem-pass-X2-CS23-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 27 Sᴰ
  lem-pass-X2-CSd23-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 2353
  lem-pass-X2-CSd23-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 28 Sᴰ
  lem-pass-X3-CK31-X3-vs-CS23-TOFF201-CSd23-TOFF201 : St 2354
  lem-pass-X3-CK31-X3-vs-CS23-TOFF201-CSd23-TOFF201 = pickᴰ 29 Sᴰ
  lem-pass-X3-CKd31-X3-vs-CS23-TOFF201-CSd23-TOFF201 : St 2357
  lem-pass-X3-CKd31-X3-vs-CS23-TOFF201-CSd23-TOFF201 = pickᴰ 30 Sᴰ
  lem-distribute-Gad⟨t≡2-W≡⟨0-3⟩-d≡1-e≡-1⟩-CS12-TOFF203-CSd12-TOFF203 : St 2365
  lem-distribute-Gad⟨t≡2-W≡⟨0-3⟩-d≡1-e≡-1⟩-CS12-TOFF203-CSd12-TOFF203 = pickᴰ 31 Sᴰ
  lem-pass-CCZ123-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 : St 2366
  lem-pass-CCZ123-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 = pickᴰ 32 Sᴰ
  lem-pass-CK32-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : St 2367
  lem-pass-CK32-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = pickᴰ 33 Sᴰ
  lem-pass-CKd30-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3 : St 2368
  lem-pass-CKd30-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3 = pickᴰ 34 Sᴰ
  lem-pass-CKd32-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : St 2369
  lem-pass-CKd32-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = pickᴰ 35 Sᴰ
  lem-pass-X2-CKd20-X2-vs-X3-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-X3 : St 2370
  lem-pass-X2-CKd20-X2-vs-X3-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-X3 = pickᴰ 36 Sᴰ
  lem-pass-X2-CSd20-X2-vs-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X3 : St 2371
  lem-pass-X2-CSd20-X2-vs-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X3 = pickᴰ 37 Sᴰ
  lem-pass-X3-CS30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 2372
  lem-pass-X3-CS30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 38 Sᴰ
  lem-pass-X3-CSd30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 2373
  lem-pass-X3-CSd30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 39 Sᴰ

private
  q1 : Eqn
  q1 = sE 2083 lem-S2-at1023-ᵖ-1
  q2 : Eqn
  q2 = wE 2071 W
  q3 : Eqn
  q3 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q4 : Eqn
  q4 = eqn (ℓ "丌丶") (ℓ "丶丌") (low₁-comm (X) (CS))
  q5 : Eqn
  q5 = wE 387 W
  q6 : Eqn
  q6 = eqn (ℓ "丶丞") (ℓ "丞丶") (low₃-comm ((CS ↑)) (X))
  q7 : Eqn
  q7 = wE 390 W
  q8 : Eqn
  q8 = eqn (ℓ "丌丷") (ℓ "丷丌") (low₁-comm (X) ((CS • CS • CS)))
  q9 : Eqn
  q9 = eqn (ℓ "丷丞") (ℓ "丞丷") (low₃-comm (((CS • CS • CS) ↑)) (X))
  q10 : Eqn
  q10 = sE 244 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CS12
  q11 : Eqn
  q11 = sE 2157 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-TOFF103-X0-X3
  q12 : Eqn
  q12 = sE 245 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CSd12
  q13 : Eqn
  q13 = sE 2342 lem-distribute-Gad⟨t≡1-W≡⟨0-3⟩-d≡1-e≡-1⟩-CS12-TOFF103-CSd12-TOFF103

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X0 X3 CS13 TOFF102 CSd13 TOFF102 X0 X3]: 19 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丌丞丽习举习丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丽习举习丌丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丌丞丽习举习丌丞") (ℓ "丌丞丽习举习丌丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 31 q1 ∷
   rw 32 q2 ∷
   rw 37 q2 ∷
   rw 42 q2 ∷
   rw 29 q3 ∷
   rw 30 q4 ∷
   rw 31 q5 ∷
   rw⁻ 29 q6 ∷
   rw 30 q7 ∷
   rw 35 q3 ∷
   rw 36 q8 ∷
   rw 37 q5 ∷
   rw⁻ 35 q9 ∷
   rw 36 q7 ∷
   rw 0 q10 ∷
   rw 1 q11 ∷
   rw 6 q12 ∷
   rw 7 q11 ∷
   rw⁻ 0 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = wE 5 W
  q15 : Eqn
  q15 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q16 : Eqn
  q16 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q17 : Eqn
  q17 = wE 137 W
  q18 : Eqn
  q18 = wE 1497 W
  q19 : Eqn
  q19 = wE 139 W
  q20 : Eqn
  q20 = wE 31 W
  q21 : Eqn
  q21 = wE 2059 W
  q22 : Eqn
  q22 = sE 1143 lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q23 : Eqn
  q23 = sE 2244 lem-pass-X2-CKd20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q24 : Eqn
  q24 = sE 1131 lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q25 : Eqn
  q25 = wE 2060 W

-- pass [X2 CKd20 X2] [X3 Sd0 CS03 TOFF012 CSd03 TOFF012 S0 X3]: 27 steps
lem-pass-X2-CKd20-X2-vs-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X3 : ⟪ (ℓ "丘久丘丞三中九丮九丈丞") ⟫ʷ ≈ ⟪ (ℓ "丞三中九丮九丈丞丘久丘") ⟫ʷ
lem-pass-X2-CKd20-X2-vs-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X3 = derive (ℓ "丘久丘丞三中九丮九丈丞") (ℓ "丞三中九丮九丈丞丘久丘")
  (rw 4 q14 ∷
   rw⁻ 3 q15 ∷
   rw⁻ 2 q16 ∷
   rw 1 q17 ∷
   rw⁻ 0 q16 ∷
   rw 1 q18 ∷
   rw 0 q15 ∷
   rw 1 q16 ∷
   rw 2 q19 ∷
   rw 3 q16 ∷
   rw 4 q20 ∷
   rw 1 q21 ∷
   rw 8 q22 ∷
   rw 5 q23 ∷
   rw 2 q24 ∷
   rw 6 q25 ∷
   rw 11 q14 ∷
   rw⁻ 10 q15 ∷
   rw⁻ 9 q16 ∷
   rw 8 q17 ∷
   rw⁻ 7 q16 ∷
   rw 8 q18 ∷
   rw 7 q15 ∷
   rw 8 q16 ∷
   rw 9 q19 ∷
   rw 10 q16 ∷
   rw 11 q20 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = wE 1466 W
  q27 : Eqn
  q27 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q28 : Eqn
  q28 = sE 2371 lem-pass-X2-CSd20-X2-vs-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X3
  q29 : Eqn
  q29 = wE 1467 W

-- pass [CSd20] [X2 X3 Kd0 CS03 TOFF012 CSd03 TOFF012 K0 X2 X3]: 5 steps
lem-pass-CSd20-vs-X2-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2-X3 : ⟪ (ℓ "丨丘丞下中九丮九上丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞下中九丮九上丘丞丨") ⟫ʷ
lem-pass-CSd20-vs-X2-X3-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2-X3 = derive (ℓ "丨丘丞下中九丮九上丘丞") (ℓ "丘丞下中九丮九上丘丞丨")
  (rw 0 q26 ∷
   rw 11 q27 ∷
   rw 1 q28 ∷
   rw 9 q29 ∷
   rw⁻ 8 q27 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = wE 1 W
  q31 : Eqn
  q31 = wE 173 W
  q32 : Eqn
  q32 = wE 3 W
  q33 : Eqn
  q33 = wE 175 W
  q34 : Eqn
  q34 = sE 2373 lem-pass-X3-CSd30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2

-- pass [CSd30] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 25 steps
lem-pass-CSd30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (ℓ "丮丘丞中九丮九丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞中九丮九丘丞丮") ⟫ʷ
lem-pass-CSd30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (ℓ "丮丘丞中九丮九丘丞") (ℓ "丘丞中九丮九丘丞丮")
  (rw 1 q27 ∷
   rw 2 q30 ∷
   rw 1 q31 ∷
   re 0 1 (ℓ "乏丨乏") ∷
   rw 2 q32 ∷
   rw 1 q26 ∷
   rw 0 q33 ∷
   rw 1 q33 ∷
   rw 4 q30 ∷
   re 2 3 (ℓ "丮") ∷
   rw 3 q33 ∷
   rw 4 q32 ∷
   rw 1 q34 ∷
   rw 11 q30 ∷
   rw 10 q31 ∷
   rw 9 q31 ∷
   re 8 1 (ℓ "乏丨乏") ∷
   rw 10 q32 ∷
   rw 7 q31 ∷
   rw 8 q29 ∷
   rw 7 q33 ∷
   rw 10 q30 ∷
   re 8 3 (ℓ "丮") ∷
   rw 9 q32 ∷
   rw⁻ 0 q27 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = wE 1462 W
  q36 : Eqn
  q36 = sE 2372 lem-pass-X3-CS30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q37 : Eqn
  q37 = wE 1463 W

-- pass [CS30] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 25 steps
lem-pass-CS30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (ℓ "中丘丞中九丮九丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞中九丮九丘丞中") ⟫ʷ
lem-pass-CS30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (ℓ "中丘丞中九丮九丘丞") (ℓ "丘丞中九丮九丘丞中")
  (rw 1 q27 ∷
   rw 2 q30 ∷
   rw 1 q31 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q32 ∷
   rw 1 q35 ∷
   rw 0 q33 ∷
   rw 1 q33 ∷
   rw 4 q30 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q33 ∷
   rw 4 q32 ∷
   rw 1 q36 ∷
   rw 11 q30 ∷
   rw 10 q31 ∷
   rw 9 q31 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q32 ∷
   rw 7 q31 ∷
   rw 8 q37 ∷
   rw 7 q33 ∷
   rw 10 q30 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q32 ∷
   rw⁻ 0 q27 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = wE 1533 W
  q39 : Eqn
  q39 = wE 1495 W
  q40 : Eqn
  q40 = wE 1496 W
  q41 : Eqn
  q41 = sE 2296 lem-pass-X2-CK21-X2-vs-CS13-TOFF102-CSd13-TOFF102

-- pass [X2 CK21 X2] [X0 X3 CS13 TOFF102 CSd13 TOFF102 X0 X3]: 7 steps
lem-pass-X2-CK21-X2-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : ⟪ (ℓ "丘乇丘丌丞丽习举习丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丽习举习丌丞丘乇丘") ⟫ʷ
lem-pass-X2-CK21-X2-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = derive (ℓ "丘乇丘丌丞丽习举习丌丞") (ℓ "丌丞丽习举习丌丞丘乇丘")
  (rw 0 q38 ∷
   rw 1 q39 ∷
   rw 2 q40 ∷
   rw 2 q41 ∷
   rw 6 q40 ∷
   rw 6 q38 ∷
   rw 7 q39 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = wE 2165 W
  q43 : Eqn
  q43 = wE 2287 W
  q44 : Eqn
  q44 = sE 2352 lem-pass-X2-CS23-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q45 : Eqn
  q45 = sE 2350 lem-pass-X2-CK23-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q46 : Eqn
  q46 = sE 2353 lem-pass-X2-CSd23-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q47 : Eqn
  q47 = wE 2288 W
  q48 : Eqn
  q48 = wE 2166 W

-- pass [X2 CKd23 X2] [X0 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X0 X3]: 9 steps
lem-pass-X2-CKd23-X2-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 : ⟪ (ℓ "丘乎丘丌丞与丐丽习举习丑丏丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞与丐丽习举习丑丏丌丞丘乎丘") ⟫ʷ
lem-pass-X2-CKd23-X2-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 = derive (ℓ "丘乎丘丌丞与丐丽习举习丑丏丌丞") (ℓ "丌丞与丐丽习举习丑丏丌丞丘乎丘")
  (rw 0 q42 ∷
   rw 2 q43 ∷
   rw 16 q44 ∷
   rw 13 q45 ∷
   rw 10 q46 ∷
   rw 7 q45 ∷
   rw 4 q44 ∷
   rw 8 q47 ∷
   rw 10 q48 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = wE 2167 W
  q50 : Eqn
  q50 = wE 2289 W
  q51 : Eqn
  q51 = sE 2351 lem-pass-X2-CKd23-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q52 : Eqn
  q52 = wE 2290 W
  q53 : Eqn
  q53 = wE 2168 W

-- pass [X2 CK23 X2] [X0 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X0 X3]: 9 steps
lem-pass-X2-CK23-X2-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 : ⟪ (ℓ "丘乍丘丌丞与丐丽习举习丑丏丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞与丐丽习举习丑丏丌丞丘乍丘") ⟫ʷ
lem-pass-X2-CK23-X2-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 = derive (ℓ "丘乍丘丌丞与丐丽习举习丑丏丌丞") (ℓ "丌丞与丐丽习举习丑丏丌丞丘乍丘")
  (rw 0 q49 ∷
   rw 2 q50 ∷
   rw 16 q46 ∷
   rw 13 q51 ∷
   rw 10 q44 ∷
   rw 7 q51 ∷
   rw 4 q46 ∷
   rw 8 q52 ∷
   rw 10 q53 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = sE 2085 lem-S2-at2013-ᵖ-1
  q55 : Eqn
  q55 = sE 2159 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-TOFF203-X0-X3
  q56 : Eqn
  q56 = sE 2365 lem-distribute-Gad⟨t≡2-W≡⟨0-3⟩-d≡1-e≡-1⟩-CS12-TOFF203-CSd12-TOFF203

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X0 X3 CS23 TOFF201 CSd23 TOFF201 X0 X3]: 19 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丌丞义乣乊乣丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞义乣乊乣丌丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丌丞义乣乊乣丌丞") (ℓ "丌丞义乣乊乣丌丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 31 q54 ∷
   rw 32 q2 ∷
   rw 37 q2 ∷
   rw 42 q2 ∷
   rw 29 q3 ∷
   rw 30 q4 ∷
   rw 31 q5 ∷
   rw⁻ 29 q6 ∷
   rw 30 q7 ∷
   rw 35 q3 ∷
   rw 36 q8 ∷
   rw 37 q5 ∷
   rw⁻ 35 q9 ∷
   rw 36 q7 ∷
   rw 0 q10 ∷
   rw 1 q55 ∷
   rw 6 q12 ∷
   rw 7 q55 ∷
   rw⁻ 0 q56 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q58 : Eqn
  q58 = wE 1833 W
  q59 : Eqn
  q59 = wE 2273 W
  q60 : Eqn
  q60 = sE 2357 lem-pass-X3-CKd31-X3-vs-CS23-TOFF201-CSd23-TOFF201
  q61 : Eqn
  q61 = wE 2274 W

-- pass [X3 CKd31 X3] [X0 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X0]: 29 steps
lem-pass-X3-CKd31-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0 : ⟪ (ℓ "丞乕丞丌丕丗且且义乣乊乣丕丕世且丌") ⟫ʷ ≈ ⟪ (ℓ "丌丕丗且且义乣乊乣丕丕世且丌丞乕丞") ⟫ʷ
lem-pass-X3-CKd31-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0 = derive (ℓ "丞乕丞丌丕丗且且义乣乊乣丕丕世且丌") (ℓ "丌丕丗且且义乣乊乣丕丕世且丌丞乕丞")
  (rw 4 q30 ∷
   rw 3 q57 ∷
   rw 2 q31 ∷
   re 1 1 (ℓ "乏么乏") ∷
   rw 3 q32 ∷
   rw 0 q31 ∷
   rw 1 q58 ∷
   rw⁻ 0 q57 ∷
   rw 1 q33 ∷
   rw 4 q30 ∷
   re 2 3 (ℓ "乕") ∷
   rw 3 q33 ∷
   rw 4 q32 ∷
   rw 1 q59 ∷
   rw 5 q60 ∷
   rw 9 q61 ∷
   rw 17 q30 ∷
   rw 16 q57 ∷
   rw 15 q31 ∷
   re 14 1 (ℓ "乏么乏") ∷
   rw 16 q32 ∷
   rw 13 q31 ∷
   rw 14 q58 ∷
   rw⁻ 13 q57 ∷
   rw 14 q33 ∷
   rw 17 q30 ∷
   re 15 3 (ℓ "乕") ∷
   rw 16 q33 ∷
   rw 17 q32 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = sE 2339 lem-pass-CCZ123-vs-X3-CSd23-X3
  q63 : Eqn
  q63 = sE 2337 lem-pass-CCZ123-vs-X3-CKd32-X3
  q64 : Eqn
  q64 = sE 2338 lem-pass-CCZ123-vs-X3-CS23-X3
  q65 : Eqn
  q65 = sE 2366 lem-pass-CCZ123-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3
  q66 : Eqn
  q66 = sE 2336 lem-pass-CCZ123-vs-X3-CK32-X3

-- CCZ(3,2,1) passes split Gad(t=2, W=(0, 3), d=SdKdSS, e=-1): 9 steps
lem-CCZ⟨321⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "乜丞乊丞丞乘丞丞义丞丞义丞丌丞义乣乊乣丌丞丞乊丞丞乊丞丞乗丞丞义丞") ⟫ʷ ≈ ⟪ (ℓ "丞乊丞丞乘丞丞义丞丞义丞丌丞义乣乊乣丌丞丞乊丞丞乊丞丞乗丞丞义丞乜") ⟫ʷ
lem-CCZ⟨321⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "乜丞乊丞丞乘丞丞义丞丞义丞丌丞义乣乊乣丌丞丞乊丞丞乊丞丞乗丞丞义丞") (ℓ "丞乊丞丞乘丞丞义丞丞义丞丌丞义乣乊乣丌丞丞乊丞丞乊丞丞乗丞丞义丞乜")
  (rw 0 q62 ∷
   rw 3 q63 ∷
   rw 6 q64 ∷
   rw 9 q64 ∷
   rw 12 q65 ∷
   rw 20 q62 ∷
   rw 23 q62 ∷
   rw 26 q66 ∷
   rw 29 q64 ∷ []) Eq.refl

private
  q67 : Eqn
  q67 = wE 2275 W
  q68 : Eqn
  q68 = sE 2354 lem-pass-X3-CK31-X3-vs-CS23-TOFF201-CSd23-TOFF201
  q69 : Eqn
  q69 = wE 2276 W

-- pass [X3 CK31 X3] [X0 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X0]: 29 steps
lem-pass-X3-CK31-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0 : ⟪ (ℓ "丞乔丞丌丕丗且且义乣乊乣丕丕世且丌") ⟫ʷ ≈ ⟪ (ℓ "丌丕丗且且义乣乊乣丕丕世且丌丞乔丞") ⟫ʷ
lem-pass-X3-CK31-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0 = derive (ℓ "丞乔丞丌丕丗且且义乣乊乣丕丕世且丌") (ℓ "丌丕丗且且义乣乊乣丕丕世且丌丞乔丞")
  (rw 4 q30 ∷
   rw 3 q57 ∷
   rw 2 q31 ∷
   re 1 1 (ℓ "乏乇乏") ∷
   rw 3 q32 ∷
   rw 0 q31 ∷
   rw 1 q38 ∷
   rw⁻ 0 q57 ∷
   rw 1 q33 ∷
   rw 4 q30 ∷
   re 2 3 (ℓ "乔") ∷
   rw 3 q33 ∷
   rw 4 q32 ∷
   rw 1 q67 ∷
   rw 5 q68 ∷
   rw 9 q69 ∷
   rw 17 q30 ∷
   rw 16 q57 ∷
   rw 15 q31 ∷
   re 14 1 (ℓ "乏乇乏") ∷
   rw 16 q32 ∷
   rw 13 q31 ∷
   rw 14 q38 ∷
   rw⁻ 13 q57 ∷
   rw 14 q33 ∷
   rw 17 q30 ∷
   re 15 3 (ℓ "乔") ∷
   rw 16 q33 ∷
   rw 17 q32 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = sE 397 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-CS12
  q71 : Eqn
  q71 = sE 2178 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-TOFF203-X0-X3
  q72 : Eqn
  q72 = sE 399 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-CSd12

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X0 X3 CS23 TOFF201 CSd23 TOFF201 X0 X3]: 19 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丌丞义乣乊乣丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞义乣乊乣丌丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丌丞义乣乊乣丌丞") (ℓ "丌丞义乣乊乣丌丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 33 q54 ∷
   rw 34 q2 ∷
   rw 39 q2 ∷
   rw 44 q2 ∷
   rw 31 q3 ∷
   rw 32 q4 ∷
   rw 33 q5 ∷
   rw⁻ 31 q6 ∷
   rw 32 q7 ∷
   rw 37 q3 ∷
   rw 38 q8 ∷
   rw 39 q5 ∷
   rw⁻ 37 q9 ∷
   rw 38 q7 ∷
   rw 0 q70 ∷
   rw 1 q71 ∷
   rw 6 q72 ∷
   rw 7 q71 ∷
   rw⁻ 0 q56 ∷ []) Eq.refl

private
  q73 : Eqn
  q73 = sE 200 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS12
  q74 : Eqn
  q74 = sE 2173 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-TOFF203-X0-X3
  q75 : Eqn
  q75 = sE 201 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-CSd12

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X0 X3 CS23 TOFF201 CSd23 TOFF201 X0 X3]: 19 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丌丞义乣乊乣丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞义乣乊乣丌丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丌丞义乣乊乣丌丞") (ℓ "丌丞义乣乊乣丌丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 31 q54 ∷
   rw 32 q2 ∷
   rw 37 q2 ∷
   rw 42 q2 ∷
   rw 29 q3 ∷
   rw 30 q4 ∷
   rw 31 q5 ∷
   rw⁻ 29 q6 ∷
   rw 30 q7 ∷
   rw 35 q3 ∷
   rw 36 q8 ∷
   rw 37 q5 ∷
   rw⁻ 35 q9 ∷
   rw 36 q7 ∷
   rw 0 q73 ∷
   rw 1 q74 ∷
   rw 6 q75 ∷
   rw 7 q74 ∷
   rw⁻ 0 q56 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = wE 2293 W
  q77 : Eqn
  q77 = wE 2294 W

-- pass [X2 CKd23 X2] [X0 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X3]: 9 steps
lem-pass-X2-CKd23-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 : ⟪ (ℓ "丘乎丘丌丞丏丑与与丽习举习丏丏丐与丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丏丑与与丽习举习丏丏丐与丌丞丘乎丘") ⟫ʷ
lem-pass-X2-CKd23-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 = derive (ℓ "丘乎丘丌丞丏丑与与丽习举习丏丏丐与丌丞") (ℓ "丌丞丏丑与与丽习举习丏丏丐与丌丞丘乎丘")
  (rw 0 q42 ∷
   rw 2 q76 ∷
   rw 18 q44 ∷
   rw 15 q45 ∷
   rw 12 q46 ∷
   rw 9 q45 ∷
   rw 6 q44 ∷
   rw 10 q77 ∷
   rw 14 q48 ∷ []) Eq.refl

private
  q78 : Eqn
  q78 = wE 2295 W
  q79 : Eqn
  q79 = wE 2296 W

-- pass [X2 CK23 X2] [X0 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X3]: 9 steps
lem-pass-X2-CK23-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 : ⟪ (ℓ "丘乍丘丌丞丏丑与与丽习举习丏丏丐与丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丏丑与与丽习举习丏丏丐与丌丞丘乍丘") ⟫ʷ
lem-pass-X2-CK23-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 = derive (ℓ "丘乍丘丌丞丏丑与与丽习举习丏丏丐与丌丞") (ℓ "丌丞丏丑与与丽习举习丏丏丐与丌丞丘乍丘")
  (rw 0 q49 ∷
   rw 2 q78 ∷
   rw 18 q46 ∷
   rw 15 q51 ∷
   rw 12 q44 ∷
   rw 9 q51 ∷
   rw 6 q46 ∷
   rw 10 q79 ∷
   rw 14 q53 ∷ []) Eq.refl

private
  q80 : Eqn
  q80 = wE 140 W
  q81 : Eqn
  q81 = wE 7 W
  q82 : Eqn
  q82 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q83 : Eqn
  q83 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q84 : Eqn
  q84 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q85 : Eqn
  q85 = wE 2004 W
  q86 : Eqn
  q86 = wE 142 W
  q87 : Eqn
  q87 = wE 27 W
  q88 : Eqn
  q88 = wE 29 W
  q89 : Eqn
  q89 = sE 2364 lem-CA-CSd20-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡1⟩
  q90 : Eqn
  q90 = sE 2368 lem-pass-CKd30-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3
  q91 : Eqn
  q91 = sE 2363 lem-CA-CS20-Gad⟨t≡0-W≡⟨3⟩-d≡Sd-e≡1⟩
  q92 : Eqn
  q92 = sE 2362 lem-pass-CK30-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3
  q93 : Eqn
  q93 = wE 76 W
  q94 : Eqn
  q94 = wE 2005 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 TOFF012 CS03 TOFF012 CSd03 X3]: 140 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞九中九丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞九中九丮丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞九中九丮丞") (ℓ "丞九中九丮丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 29 q14 ∷
   rw 28 q80 ∷
   rw 27 q80 ∷
   rw 26 q81 ∷
   rw 25 q80 ∷
   rw 24 q81 ∷
   rw 23 q81 ∷
   rw⁻ 22 q82 ∷
   rw 21 q81 ∷
   rw 20 q81 ∷
   rw 19 q81 ∷
   rw 18 q81 ∷
   rw 17 q81 ∷
   rw 16 q81 ∷
   rw⁻ 15 q83 ∷
   rw 14 q80 ∷
   rw 13 q81 ∷
   rw 12 q81 ∷
   rw 11 q81 ∷
   rw⁻ 10 q83 ∷
   rw 9 q80 ∷
   rw⁻ 8 q83 ∷
   rw 7 q80 ∷
   rw⁻ 6 q82 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw⁻ 7 q84 ∷
   rw 6 q80 ∷
   rw⁻ 5 q84 ∷
   re 6 3 (ℓ "乔") ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw⁻ 6 q84 ∷
   rw 5 q80 ∷
   rw⁻ 4 q84 ∷
   re 5 3 (ℓ "乔") ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q84 ∷
   rw 4 q81 ∷
   rw⁻ 3 q84 ∷
   re 4 3 (ℓ "丽") ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw⁻ 4 q84 ∷
   rw 3 q80 ∷
   rw⁻ 2 q84 ∷
   re 3 3 (ℓ "乔") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q84 ∷
   rw 2 q81 ∷
   rw⁻ 1 q84 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q84 ∷
   rw 1 q81 ∷
   rw⁻ 0 q84 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q85 ∷
   re 1 1 (ℓ "乏乇乏") ∷
   rw 0 q84 ∷
   rw 1 q86 ∷
   rw 2 q84 ∷
   re 0 3 (ℓ "乑") ∷
   rw 1 q87 ∷
   re 3 1 (ℓ "乏么乏") ∷
   rw 2 q84 ∷
   rw 3 q19 ∷
   rw 4 q84 ∷
   re 2 3 (ℓ "乒") ∷
   rw 3 q88 ∷
   rw 4 q20 ∷
   rw 3 q89 ∷
   rw 2 q90 ∷
   rw 1 q91 ∷
   rw 0 q92 ∷
   rw 10 q14 ∷
   rw 9 q93 ∷
   re 8 1 (ℓ "乏久乏") ∷
   rw⁻ 10 q84 ∷
   rw 9 q17 ∷
   rw⁻ 8 q84 ∷
   re 9 3 (ℓ "乕") ∷
   rw 7 q81 ∷
   re 6 1 (ℓ "乏乄乏") ∷
   rw⁻ 8 q84 ∷
   rw 7 q80 ∷
   rw⁻ 6 q84 ∷
   re 7 3 (ℓ "乔") ∷
   rw 7 q94 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q84 ∷
   rw 7 q87 ∷
   rw 8 q84 ∷
   re 6 3 (ℓ "中") ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q84 ∷
   rw 8 q87 ∷
   rw 9 q84 ∷
   re 7 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 8 q84 ∷
   rw 9 q86 ∷
   rw 10 q84 ∷
   re 8 3 (ℓ "乑") ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q84 ∷
   rw 10 q87 ∷
   rw 11 q84 ∷
   re 9 3 (ℓ "中") ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q84 ∷
   rw 11 q86 ∷
   rw 12 q84 ∷
   re 10 3 (ℓ "乑") ∷
   re 12 1 (ℓ "乏乇乏") ∷
   rw 11 q84 ∷
   rw 12 q86 ∷
   rw 13 q84 ∷
   re 11 3 (ℓ "乑") ∷
   rw 12 q82 ∷
   rw 13 q86 ∷
   rw 14 q83 ∷
   rw 15 q86 ∷
   rw 16 q83 ∷
   rw 17 q87 ∷
   rw 18 q87 ∷
   rw 19 q87 ∷
   rw 20 q86 ∷
   rw 21 q83 ∷
   rw 22 q87 ∷
   rw 23 q87 ∷
   rw 24 q87 ∷
   rw 25 q87 ∷
   rw 26 q87 ∷
   rw 27 q87 ∷
   rw 28 q82 ∷
   rw 29 q87 ∷
   rw 30 q87 ∷
   rw 31 q86 ∷
   rw 32 q87 ∷
   rw 33 q86 ∷
   rw 34 q86 ∷
   rw 35 q20 ∷ []) Eq.refl

private
  q95 : Eqn
  q95 = wE 2297 W
  q96 : Eqn
  q96 = sE 2369 lem-pass-CKd32-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3
  q97 : Eqn
  q97 = sE 2140 lem-pass-CCZ123-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3
  q98 : Eqn
  q98 = sE 2367 lem-pass-CK32-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3
  q99 : Eqn
  q99 = wE 2298 W

-- pass [TOFF213] [X3 TOFF012 CS03 TOFF012 CSd03 X3]: 5 steps
lem-pass-TOFF213-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : ⟪ (ℓ "乥丞九中九丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞九中九丮丞乥") ⟫ʷ
lem-pass-TOFF213-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = derive (ℓ "乥丞九中九丮丞") (ℓ "丞九中九丮丞乥")
  (rw 0 q95 ∷
   rw 2 q96 ∷
   rw 1 q97 ∷
   rw 0 q98 ∷
   rw 6 q99 ∷ []) Eq.refl

private
  q100 : Eqn
  q100 = wE 1459 W
  q101 : Eqn
  q101 = sE 2370 lem-pass-X2-CKd20-X2-vs-X3-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-X3
  q102 : Eqn
  q102 = eqn (ℓ "上丞") (ℓ "丞上") (low₁-comm (K) ((X ↑ ↑)))
  q103 : Eqn
  q103 = wE 1846 W
  q104 : Eqn
  q104 = wE 1460 W
  q105 : Eqn
  q105 = wE 1461 W

-- CA CK20 Gad(t=0, W=(3,), d=Kd, e=1): 7 steps
lem-CA-CK20-Gad⟨t≡0-W≡⟨3⟩-d≡Kd-e≡1⟩ : ⟪ (ℓ "乄丞下九中九丮上丞") ⟫ʷ ≈ ⟪ (ℓ "丞九中九丮丞乄") ⟫ʷ
lem-CA-CK20-Gad⟨t≡0-W≡⟨3⟩-d≡Kd-e≡1⟩ = derive (ℓ "乄丞下九中九丮上丞") (ℓ "丞九中九丮丞乄")
  (rw 0 q100 ∷
   rw 1 q101 ∷
   rw 0 q102 ∷
   rw 1 q103 ∷
   rw 5 q104 ∷
   rw 5 q102 ∷
   rw 6 q105 ∷ []) Eq.refl
