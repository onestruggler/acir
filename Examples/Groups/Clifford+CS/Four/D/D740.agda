{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD740 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D740 (W : Ws) (Sᴰ : SD740) where

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
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK32-X3 : St 400
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK32-X3 = pickᴰ 0 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd32-X3 : St 407
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd32-X3 = pickᴰ 1 Sᴰ
  lem-pass-CCZ123-vs-X3-CK31-X3 : St 2332
  lem-pass-CCZ123-vs-X3-CK31-X3 = pickᴰ 2 Sᴰ
  lem-pass-CCZ123-vs-X3-CKd31-X3 : St 2333
  lem-pass-CCZ123-vs-X3-CKd31-X3 = pickᴰ 3 Sᴰ
  lem-pass-CCZ123-vs-X3-CS13-X3 : St 2334
  lem-pass-CCZ123-vs-X3-CS13-X3 = pickᴰ 4 Sᴰ
  lem-pass-CCZ123-vs-X3-CSd13-X3 : St 2335
  lem-pass-CCZ123-vs-X3-CSd13-X3 = pickᴰ 5 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-X3 : St 2374
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-X3 = pickᴰ 6 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd23-X3 : St 2375
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd23-X3 = pickᴰ 7 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-CS12-X2 : St 2409
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-CS12-X2 = pickᴰ 8 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-CSd12-X2 : St 2410
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-CSd12-X2 = pickᴰ 9 Sᴰ
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 1131
  lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 10 Sᴰ
  lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 1143
  lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 11 Sᴰ
  lem-pass-X3-CKd31-X3-vs-CS13-TOFF102-CSd13-TOFF102 : St 1386
  lem-pass-X3-CKd31-X3-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 12 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-TOFF103-X0-X3 : St 2158
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-TOFF103-X0-X3 = pickᴰ 13 Sᴰ
  lem-S2-at1023-ᵖ-1 : St 2083
  lem-S2-at1023-ᵖ-1 = pickᴰ 14 Sᴰ
  lem-pass-X2-CKd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 2244
  lem-pass-X2-CKd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 15 Sᴰ
  lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 2245
  lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 16 Sᴰ
  lem-pass-X3-CK32-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2340
  lem-pass-X3-CK32-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 17 Sᴰ
  lem-pass-X3-CKd32-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2341
  lem-pass-X3-CKd32-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 18 Sᴰ
  lem-pass-X3-CS31-X3-vs-CS13-TOFF102-CSd13-TOFF102 : St 2267
  lem-pass-X3-CS31-X3-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 19 Sᴰ
  lem-pass-X3-CS32-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2411
  lem-pass-X3-CS32-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 20 Sᴰ
  lem-pass-X3-CSd32-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2412
  lem-pass-X3-CSd32-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 21 Sᴰ
  lem-pass-CCZ123-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : St 2345
  lem-pass-CCZ123-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = pickᴰ 22 Sᴰ
  lem-pass-X2-CK23-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 2350
  lem-pass-X2-CK23-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 23 Sᴰ
  lem-pass-X2-CKd23-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 2351
  lem-pass-X2-CKd23-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 24 Sᴰ
  lem-pass-X3-CK32-X3-vs-CS13-TOFF102-CSd13-TOFF102 : St 2355
  lem-pass-X3-CK32-X3-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 25 Sᴰ
  lem-pass-X3-CKd32-X3-vs-CS13-TOFF102-CSd13-TOFF102 : St 2358
  lem-pass-X3-CKd32-X3-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 26 Sᴰ
  lem-pass-X3-CS30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 2372
  lem-pass-X3-CS30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 27 Sᴰ
  lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡-1⟩-CS12-TOFF103-CSd12-TOFF103 : St 2413
  lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡-1⟩-CS12-TOFF103-CSd12-TOFF103 = pickᴰ 28 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 : St 2414
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 = pickᴰ 29 Sᴰ
  lem-pass-X2-CK21-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : St 2415
  lem-pass-X2-CK21-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = pickᴰ 30 Sᴰ
  lem-pass-X2-CK23-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 2416
  lem-pass-X2-CK23-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 31 Sᴰ
  lem-pass-X2-CK23-X2-vs-X0-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X3 : St 2417
  lem-pass-X2-CK23-X2-vs-X0-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X3 = pickᴰ 32 Sᴰ
  lem-pass-X2-CKd23-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 2418
  lem-pass-X2-CKd23-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 33 Sᴰ
  lem-pass-X2-CKd23-X2-vs-X0-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X3 : St 2419
  lem-pass-X2-CKd23-X2-vs-X0-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X3 = pickᴰ 34 Sᴰ
  lem-pass-X2-CSd20-X2-vs-Kd0-CS03-TOFF012-CSd03-TOFF012-K0 : St 2420
  lem-pass-X2-CSd20-X2-vs-Kd0-CS03-TOFF012-CSd03-TOFF012-K0 = pickᴰ 35 Sᴰ
  lem-pass-X3-CKd30-X3-vs-X2-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2 : St 2421
  lem-pass-X3-CKd30-X3-vs-X2-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2 = pickᴰ 36 Sᴰ
  lem-pass-X3-CS32-X3-vs-CS13-TOFF102-CSd13-TOFF102 : St 2422
  lem-pass-X3-CS32-X3-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 37 Sᴰ
  lem-pass-X3-CSd30-X3-vs-X2-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2 : St 2423
  lem-pass-X3-CSd30-X3-vs-X2-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2 = pickᴰ 38 Sᴰ
  lem-pass-X3-CSd31-X3-vs-CS13-TOFF102-CSd13-TOFF102 : St 2424
  lem-pass-X3-CSd31-X3-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 39 Sᴰ
  lem-pass-X3-CSd32-X3-vs-CS13-TOFF102-CSd13-TOFF102 : St 2425
  lem-pass-X3-CSd32-X3-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 40 Sᴰ

private
  q1 : Eqn
  q1 = sE 400 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK32-X3
  q2 : Eqn
  q2 = sE 2374 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-X3
  q3 : Eqn
  q3 = sE 407 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd32-X3
  q4 : Eqn
  q4 = sE 2414 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3
  q5 : Eqn
  q5 = sE 2375 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd23-X3

-- Bar(SSKSKK;3,2->0) passes split Gad(t=2, W=(0, 3), d=KSSKd, e=1): 9 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡KSSKd-e≡1⟩ : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乗丞丞义丞丞义丞丞乘丞丌丞乣义乣乊丌丞丞乗丞丞乊丞丞乊丞丞乘丞") ⟫ʷ ≈ ⟪ (ℓ "丞乗丞丞义丞丞义丞丞乘丞丌丞乣义乣乊丌丞丞乗丞丞乊丞丞乊丞丞乘丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡KSSKd-e≡1⟩ = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乗丞丞义丞丞义丞丞乘丞丌丞乣义乣乊丌丞丞乗丞丞乊丞丞乊丞丞乘丞") (ℓ "丞乗丞丞义丞丞义丞丞乘丞丌丞乣义乣乊丌丞丞乗丞丞乊丞丞乊丞丞乘丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 0 q1 ∷
   rw 3 q2 ∷
   rw 6 q2 ∷
   rw 9 q3 ∷
   rw 12 q4 ∷
   rw 20 q1 ∷
   rw 23 q5 ∷
   rw 26 q5 ∷
   rw 29 q3 ∷ []) Eq.refl

private
  q6 : Eqn
  q6 = wE 1833 W
  q7 : Eqn
  q7 = wE 1497 W
  q8 : Eqn
  q8 = wE 1498 W
  q9 : Eqn
  q9 = sE 2245 lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [X2 CKd21 X2] [X0 X3 TOFF102 CS13 TOFF102 CSd13 X0 X3]: 7 steps
lem-pass-X2-CKd21-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : ⟪ (ℓ "丘么丘丌丞习丽习举丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞习丽习举丌丞丘么丘") ⟫ʷ
lem-pass-X2-CKd21-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = derive (ℓ "丘么丘丌丞习丽习举丌丞") (ℓ "丌丞习丽习举丌丞丘么丘")
  (rw 0 q6 ∷
   rw 1 q7 ∷
   rw 2 q8 ∷
   rw 2 q9 ∷
   rw 6 q8 ∷
   rw 6 q6 ∷
   rw 7 q7 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = eqn (ℓ "丌丘") (ℓ "丘丌") (low₁-comm (X) ((X ↑)))
  q11 : Eqn
  q11 = wE 1476 W
  q12 : Eqn
  q12 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q13 : Eqn
  q13 = sE 2415 lem-pass-X2-CK21-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3
  q14 : Eqn
  q14 = wE 1477 W

-- pass [CK21] [X0 X2 X3 TOFF102 CS13 TOFF102 CSd13 X0 X2 X3]: 7 steps
lem-pass-CK21-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : ⟪ (ℓ "乇丌丘丞习丽习举丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞习丽习举丌丘丞乇") ⟫ʷ
lem-pass-CK21-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = derive (ℓ "乇丌丘丞习丽习举丌丘丞") (ℓ "丌丘丞习丽习举丌丘丞乇")
  (rw 1 q10 ∷
   rw 0 q11 ∷
   rw 11 q12 ∷
   rw 1 q13 ∷
   rw 9 q14 ∷
   rw⁻ 0 q10 ∷
   rw⁻ 8 q12 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = wE 2301 W
  q16 : Eqn
  q16 = sE 2419 lem-pass-X2-CKd23-X2-vs-X0-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X3
  q17 : Eqn
  q17 = wE 2302 W

-- pass [CKd23] [X0 X2 X3 K1 S1 S1 Kd1 TOFF102 CS13 TOFF102 CSd13 K1 Sd1 Sd1 Kd1 X0 X2 X3]: 7 steps
lem-pass-CKd23-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3 : ⟪ (ℓ "乎丌丘丞丐与与丑习丽习举丐丏丏丑丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丐与与丑习丽习举丐丏丏丑丌丘丞乎") ⟫ʷ
lem-pass-CKd23-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3 = derive (ℓ "乎丌丘丞丐与与丑习丽习举丐丏丏丑丌丘丞") (ℓ "丌丘丞丐与与丑习丽习举丐丏丏丑丌丘丞乎")
  (rw 1 q10 ∷
   rw 0 q15 ∷
   rw 19 q12 ∷
   rw 1 q16 ∷
   rw 17 q17 ∷
   rw⁻ 0 q10 ∷
   rw⁻ 16 q12 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = wE 2303 W
  q19 : Eqn
  q19 = sE 2417 lem-pass-X2-CK23-X2-vs-X0-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X3
  q20 : Eqn
  q20 = wE 2304 W

-- pass [CK23] [X0 X2 X3 K1 S1 S1 Kd1 TOFF102 CS13 TOFF102 CSd13 K1 Sd1 Sd1 Kd1 X0 X2 X3]: 7 steps
lem-pass-CK23-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3 : ⟪ (ℓ "乍丌丘丞丐与与丑习丽习举丐丏丏丑丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丐与与丑习丽习举丐丏丏丑丌丘丞乍") ⟫ʷ
lem-pass-CK23-vs-X0-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X0-X2-X3 = derive (ℓ "乍丌丘丞丐与与丑习丽习举丐丏丏丑丌丘丞") (ℓ "丌丘丞丐与与丑习丽习举丐丏丏丑丌丘丞乍")
  (rw 1 q10 ∷
   rw 0 q18 ∷
   rw 19 q12 ∷
   rw 1 q19 ∷
   rw 17 q20 ∷
   rw⁻ 0 q10 ∷
   rw⁻ 16 q12 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = wE 2315 W
  q22 : Eqn
  q22 = wE 2316 W
  q23 : Eqn
  q23 = sE 2267 lem-pass-X3-CS31-X3-vs-CS13-TOFF102-CSd13-TOFF102
  q24 : Eqn
  q24 = sE 1386 lem-pass-X3-CKd31-X3-vs-CS13-TOFF102-CSd13-TOFF102
  q25 : Eqn
  q25 = sE 2424 lem-pass-X3-CSd31-X3-vs-CS13-TOFF102-CSd13-TOFF102
  q26 : Eqn
  q26 = wE 2317 W

-- ca-split Gad(t=1, W=(), d=SdKdSS, e=-1) 3: 7 steps
lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SdKdSS-e≡-1⟩-3 : ⟪ (ℓ "丏丑与与丽习举习丏丏丐与") ⟫ʷ ≈ ⟪ (ℓ "举乕丽丽丽习举习举举乔丽") ⟫ʷ
lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SdKdSS-e≡-1⟩-3 = derive (ℓ "丏丑与与丽习举习丏丏丐与") (ℓ "举乕丽丽丽习举习举举乔丽")
  (rw 0 q21 ∷
   rw 20 q22 ∷
   rw 13 q23 ∷
   rw 10 q23 ∷
   rw 7 q24 ∷
   rw 4 q25 ∷
   rw 8 q26 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = wE 1688 W
  q28 : Eqn
  q28 = wE 2318 W
  q29 : Eqn
  q29 = sE 2341 lem-pass-X3-CKd32-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q30 : Eqn
  q30 = wE 2319 W

-- pass [X3 CKd32 X3] [Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0]: 5 steps
lem-pass-X3-CKd32-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : ⟪ (ℓ "丞乘丞三下丈丈中九丮九三三上丈") ⟫ʷ ≈ ⟪ (ℓ "三下丈丈中九丮九三三上丈丞乘丞") ⟫ʷ
lem-pass-X3-CKd32-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = derive (ℓ "丞乘丞三下丈丈中九丮九三三上丈") (ℓ "三下丈丈中九丮九三三上丈丞乘丞")
  (rw 0 q27 ∷
   rw 0 q28 ∷
   rw 4 q29 ∷
   rw 8 q30 ∷
   rw 12 q27 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = wE 1415 W
  q32 : Eqn
  q32 = wE 2320 W
  q33 : Eqn
  q33 = sE 2340 lem-pass-X3-CK32-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q34 : Eqn
  q34 = wE 2321 W

-- pass [X3 CK32 X3] [Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0]: 5 steps
lem-pass-X3-CK32-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : ⟪ (ℓ "丞乗丞三下丈丈中九丮九三三上丈") ⟫ʷ ≈ ⟪ (ℓ "三下丈丈中九丮九三三上丈丞乗丞") ⟫ʷ
lem-pass-X3-CK32-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = derive (ℓ "丞乗丞三下丈丈中九丮九三三上丈") (ℓ "三下丈丈中九丮九三三上丈丞乗丞")
  (rw 0 q31 ∷
   rw 0 q32 ∷
   rw 4 q33 ∷
   rw 8 q34 ∷
   rw 12 q31 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = wE 1 W
  q36 : Eqn
  q36 = wE 3 W
  q37 : Eqn
  q37 = wE 1812 W
  q38 : Eqn
  q38 = eqn (ℓ "三乏") (ℓ "乏三") (low₁-comm ((S • S • S)) ((Swap ↑)))
  q39 : Eqn
  q39 = wE 175 W
  q40 : Eqn
  q40 = sE 2372 lem-pass-X3-CS30-X3-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q41 : Eqn
  q41 = eqn (ℓ "三丘") (ℓ "丘三") (low₁-comm ((S • S • S)) ((X ↑)))
  q42 : Eqn
  q42 = wE 1813 W
  q43 : Eqn
  q43 = wE 1732 W
  q44 : Eqn
  q44 = wE 173 W
  q45 : Eqn
  q45 = wE 1814 W

-- CA CSd30 Gad(t=0, W=(2,), d=1, e=-1): 25 steps
lem-CA-CSd30-Gad⟨t≡0-W≡⟨2⟩-d≡1-e≡-1⟩ : ⟪ (ℓ "丮丘中九丮九丘") ⟫ʷ ≈ ⟪ (ℓ "丘三中九丮九丈丘丮") ⟫ʷ
lem-CA-CSd30-Gad⟨t≡0-W≡⟨2⟩-d≡1-e≡-1⟩ = derive (ℓ "丮丘中九丮九丘") (ℓ "丘三中九丮九丈丘丮")
  (rw 1 q35 ∷
   re 0 1 (ℓ "乏丨乏") ∷
   rw 2 q36 ∷
   rw 1 q37 ∷
   rw⁻ 0 q38 ∷
   rw 1 q39 ∷
   rw 4 q35 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q39 ∷
   rw 4 q36 ∷
   rw 1 q40 ∷
   rw 0 q41 ∷
   rw 1 q42 ∷
   rw 6 q43 ∷
   rw 7 q41 ∷
   rw 12 q35 ∷
   rw 11 q44 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q36 ∷
   rw 9 q44 ∷
   rw 8 q38 ∷
   rw 9 q45 ∷
   rw 10 q35 ∷
   re 8 3 (ℓ "丮") ∷
   rw 9 q36 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = wE 2059 W
  q47 : Eqn
  q47 = sE 1143 lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q48 : Eqn
  q48 = sE 2244 lem-pass-X2-CKd20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q49 : Eqn
  q49 = sE 1131 lem-pass-X2-CS20-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q50 : Eqn
  q50 = wE 2060 W

-- pass [X2 CKd20 X2] [Sd0 CS03 TOFF012 CSd03 TOFF012 S0]: 5 steps
lem-pass-X2-CKd20-X2-vs-Sd0-CS03-TOFF012-CSd03-TOFF012-S0 : ⟪ (ℓ "丘久丘三中九丮九丈") ⟫ʷ ≈ ⟪ (ℓ "三中九丮九丈丘久丘") ⟫ʷ
lem-pass-X2-CKd20-X2-vs-Sd0-CS03-TOFF012-CSd03-TOFF012-S0 = derive (ℓ "丘久丘三中九丮九丈") (ℓ "三中九丮九丈丘久丘")
  (rw 0 q46 ∷
   rw 7 q47 ∷
   rw 4 q48 ∷
   rw 1 q49 ∷
   rw 5 q50 ∷ []) Eq.refl

private
  q51 : Eqn
  q51 = wE 1815 W
  q52 : Eqn
  q52 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q53 : Eqn
  q53 = sE 2423 lem-pass-X3-CSd30-X3-vs-X2-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2
  q54 : Eqn
  q54 = eqn (ℓ "丈丘") (ℓ "丘丈") (low₁-comm (S) ((X ↑)))
  q55 : Eqn
  q55 = wE 1728 W
  q56 : Eqn
  q56 = wE 1727 W
  q57 : Eqn
  q57 = wE 1816 W

-- CA CS30 Gad(t=0, W=(2,), d=Sd, e=-1): 25 steps
lem-CA-CS30-Gad⟨t≡0-W≡⟨2⟩-d≡Sd-e≡-1⟩ : ⟪ (ℓ "中丘三中九丮九丈丘") ⟫ʷ ≈ ⟪ (ℓ "丘中九丮九丘中") ⟫ʷ
lem-CA-CS30-Gad⟨t≡0-W≡⟨2⟩-d≡Sd-e≡-1⟩ = derive (ℓ "中丘三中九丮九丈丘") (ℓ "丘中九丮九丘中")
  (rw 1 q35 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q36 ∷
   rw 1 q51 ∷
   rw⁻ 0 q52 ∷
   rw 1 q39 ∷
   rw 4 q35 ∷
   re 2 3 (ℓ "丮") ∷
   rw 3 q39 ∷
   rw 4 q36 ∷
   rw 1 q53 ∷
   rw 0 q54 ∷
   rw 1 q55 ∷
   rw 5 q56 ∷
   rw 5 q54 ∷
   rw 10 q35 ∷
   rw 9 q44 ∷
   re 8 1 (ℓ "乏丨乏") ∷
   rw 10 q36 ∷
   rw 7 q44 ∷
   rw 6 q52 ∷
   rw 7 q57 ∷
   rw 8 q35 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q36 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = wE 2322 W
  q59 : Eqn
  q59 = wE 2323 W
  q60 : Eqn
  q60 = sE 2418 lem-pass-X2-CKd23-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q61 : Eqn
  q61 = wE 2324 W

-- pass [X2 CKd23 X2] [Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0]: 5 steps
lem-pass-X2-CKd23-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : ⟪ (ℓ "丘乎丘三下丈丈中九丮九三三上丈") ⟫ʷ ≈ ⟪ (ℓ "三下丈丈中九丮九三三上丈丘乎丘") ⟫ʷ
lem-pass-X2-CKd23-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = derive (ℓ "丘乎丘三下丈丈中九丮九三三上丈") (ℓ "三下丈丈中九丮九三三上丈丘乎丘")
  (rw 0 q58 ∷
   rw 0 q59 ∷
   rw 4 q60 ∷
   rw 8 q61 ∷
   rw 12 q58 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = wE 2325 W
  q63 : Eqn
  q63 = wE 2326 W
  q64 : Eqn
  q64 = sE 2416 lem-pass-X2-CK23-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q65 : Eqn
  q65 = wE 2327 W

-- pass [X2 CK23 X2] [Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0]: 5 steps
lem-pass-X2-CK23-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : ⟪ (ℓ "丘乍丘三下丈丈中九丮九三三上丈") ⟫ʷ ≈ ⟪ (ℓ "三下丈丈中九丮九三三上丈丘乍丘") ⟫ʷ
lem-pass-X2-CK23-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = derive (ℓ "丘乍丘三下丈丈中九丮九三三上丈") (ℓ "三下丈丈中九丮九三三上丈丘乍丘")
  (rw 0 q62 ∷
   rw 0 q63 ∷
   rw 4 q64 ∷
   rw 8 q65 ∷
   rw 12 q62 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = wE 1466 W
  q67 : Eqn
  q67 = sE 2420 lem-pass-X2-CSd20-X2-vs-Kd0-CS03-TOFF012-CSd03-TOFF012-K0
  q68 : Eqn
  q68 = wE 1467 W

-- pass [CSd20] [X2 Kd0 CS03 TOFF012 CSd03 TOFF012 K0 X2]: 3 steps
lem-pass-CSd20-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2 : ⟪ (ℓ "丨丘下中九丮九上丘") ⟫ʷ ≈ ⟪ (ℓ "丘下中九丮九上丘丨") ⟫ʷ
lem-pass-CSd20-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2 = derive (ℓ "丨丘下中九丮九上丘") (ℓ "丘下中九丮九上丘丨")
  (rw 0 q66 ∷
   rw 1 q67 ∷
   rw 7 q68 ∷ []) Eq.refl

private
  q69 : Eqn
  q69 = wE 2328 W
  q70 : Eqn
  q70 = wE 2329 W
  q71 : Eqn
  q71 = sE 2411 lem-pass-X3-CS32-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q72 : Eqn
  q72 = sE 2412 lem-pass-X3-CSd32-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q73 : Eqn
  q73 = wE 2330 W
  q74 : Eqn
  q74 = wE 2331 W

-- pass [X3 CKd32 X3] [X2 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2]: 9 steps
lem-pass-X3-CKd32-X3-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 : ⟪ (ℓ "丞乘丞丘三下丈丈中九丮九三三上丈丘") ⟫ʷ ≈ ⟪ (ℓ "丘三下丈丈中九丮九三三上丈丘丞乘丞") ⟫ʷ
lem-pass-X3-CKd32-X3-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 = derive (ℓ "丞乘丞丘三下丈丈中九丮九三三上丈丘") (ℓ "丘三下丈丈中九丮九三三上丈丘丞乘丞")
  (rw 0 q69 ∷
   rw 1 q70 ∷
   rw 17 q71 ∷
   rw 14 q33 ∷
   rw 11 q72 ∷
   rw 8 q33 ∷
   rw 5 q71 ∷
   rw 9 q73 ∷
   rw 13 q74 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = wE 2332 W
  q76 : Eqn
  q76 = wE 2333 W
  q77 : Eqn
  q77 = wE 2334 W
  q78 : Eqn
  q78 = wE 2335 W

-- pass [X3 CK32 X3] [X2 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2]: 9 steps
lem-pass-X3-CK32-X3-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 : ⟪ (ℓ "丞乗丞丘三下丈丈中九丮九三三上丈丘") ⟫ʷ ≈ ⟪ (ℓ "丘三下丈丈中九丮九三三上丈丘丞乗丞") ⟫ʷ
lem-pass-X3-CK32-X3-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 = derive (ℓ "丞乗丞丘三下丈丈中九丮九三三上丈丘") (ℓ "丘三下丈丈中九丮九三三上丈丘丞乗丞")
  (rw 0 q75 ∷
   rw 1 q76 ∷
   rw 17 q72 ∷
   rw 14 q29 ∷
   rw 11 q71 ∷
   rw 8 q29 ∷
   rw 5 q72 ∷
   rw 9 q77 ∷
   rw 13 q78 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = wE 1464 W
  q80 : Eqn
  q80 = sE 2421 lem-pass-X3-CKd30-X3-vs-X2-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2
  q81 : Eqn
  q81 = wE 1465 W

-- pass [CKd30] [X2 X3 Sd0 CS03 TOFF012 CSd03 TOFF012 S0 X2 X3]: 25 steps
lem-pass-CKd30-vs-X2-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2-X3 : ⟪ (ℓ "乒丘丞三中九丮九丈丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞三中九丮九丈丘丞乒") ⟫ʷ
lem-pass-CKd30-vs-X2-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2-X3 = derive (ℓ "乒丘丞三中九丮九丈丘丞") (ℓ "丘丞三中九丮九丈丘丞乒")
  (rw 1 q12 ∷
   rw 2 q35 ∷
   rw 1 q44 ∷
   re 0 1 (ℓ "乏久乏") ∷
   rw 2 q36 ∷
   rw 1 q79 ∷
   rw 0 q39 ∷
   rw 1 q39 ∷
   rw 4 q35 ∷
   re 2 3 (ℓ "乒") ∷
   rw 3 q39 ∷
   rw 4 q36 ∷
   rw 1 q80 ∷
   rw 13 q35 ∷
   rw 12 q44 ∷
   rw 11 q44 ∷
   re 10 1 (ℓ "乏久乏") ∷
   rw 12 q36 ∷
   rw 9 q44 ∷
   rw 10 q81 ∷
   rw 9 q39 ∷
   rw 12 q35 ∷
   re 10 3 (ℓ "乒") ∷
   rw 11 q36 ∷
   rw⁻ 0 q12 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q83 : Eqn
  q83 = wE 1749 W
  q84 : Eqn
  q84 = wE 2118 W

-- pass [X3 CSd31 X3] [X0 CS13 TOFF102 CSd13 TOFF102 X0]: 29 steps
lem-pass-X3-CSd31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 : ⟪ (ℓ "丞举丞丌丽习举习丌") ⟫ʷ ≈ ⟪ (ℓ "丌丽习举习丌丞举丞") ⟫ʷ
lem-pass-X3-CSd31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 = derive (ℓ "丞举丞丌丽习举习丌") (ℓ "丌丽习举习丌丞举丞")
  (rw 4 q35 ∷
   rw 3 q82 ∷
   rw 2 q44 ∷
   re 1 1 (ℓ "乏丷乏") ∷
   rw 3 q36 ∷
   rw 0 q44 ∷
   rw 1 q83 ∷
   rw⁻ 0 q82 ∷
   rw 1 q39 ∷
   rw 4 q35 ∷
   re 2 3 (ℓ "举") ∷
   rw 3 q39 ∷
   rw 4 q36 ∷
   rw 1 q84 ∷
   rw 1 q25 ∷
   rw 5 q84 ∷
   rw 9 q35 ∷
   rw 8 q82 ∷
   rw 7 q44 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q36 ∷
   rw 5 q44 ∷
   rw 6 q83 ∷
   rw⁻ 5 q82 ∷
   rw 6 q39 ∷
   rw 9 q35 ∷
   re 7 3 (ℓ "举") ∷
   rw 8 q39 ∷
   rw 9 q36 ∷ []) Eq.refl

private
  q85 : Eqn
  q85 = wE 1687 W
  q86 : Eqn
  q86 = wE 2336 W
  q87 : Eqn
  q87 = sE 2358 lem-pass-X3-CKd32-X3-vs-CS13-TOFF102-CSd13-TOFF102
  q88 : Eqn
  q88 = wE 2337 W

-- pass [X3 CKd32 X3] [X0 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0]: 5 steps
lem-pass-X3-CKd32-X3-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 : ⟪ (ℓ "丞乘丞丌丏丑与与丽习举习丏丏丐与丌") ⟫ʷ ≈ ⟪ (ℓ "丌丏丑与与丽习举习丏丏丐与丌丞乘丞") ⟫ʷ
lem-pass-X3-CKd32-X3-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 = derive (ℓ "丞乘丞丌丏丑与与丽习举习丏丏丐与丌") (ℓ "丌丏丑与与丽习举习丏丏丐与丌丞乘丞")
  (rw 0 q85 ∷
   rw 1 q86 ∷
   rw 5 q87 ∷
   rw 9 q88 ∷
   rw 13 q85 ∷ []) Eq.refl

private
  q89 : Eqn
  q89 = sE 2335 lem-pass-CCZ123-vs-X3-CSd13-X3
  q90 : Eqn
  q90 = sE 2333 lem-pass-CCZ123-vs-X3-CKd31-X3
  q91 : Eqn
  q91 = sE 2334 lem-pass-CCZ123-vs-X3-CS13-X3
  q92 : Eqn
  q92 = sE 2345 lem-pass-CCZ123-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3
  q93 : Eqn
  q93 = sE 2332 lem-pass-CCZ123-vs-X3-CK31-X3

-- CCZ(3,1,2) passes split Gad(t=1, W=(0, 3), d=SdKdSS, e=-1): 9 steps
lem-CCZ⟨312⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "乜丞举丞丞乕丞丞丽丞丞丽丞丌丞丽习举习丌丞丞举丞丞举丞丞乔丞丞丽丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞丞乕丞丞丽丞丞丽丞丌丞丽习举习丌丞丞举丞丞举丞丞乔丞丞丽丞乜") ⟫ʷ
lem-CCZ⟨312⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "乜丞举丞丞乕丞丞丽丞丞丽丞丌丞丽习举习丌丞丞举丞丞举丞丞乔丞丞丽丞") (ℓ "丞举丞丞乕丞丞丽丞丞丽丞丌丞丽习举习丌丞丞举丞丞举丞丞乔丞丞丽丞乜")
  (rw 0 q89 ∷
   rw 3 q90 ∷
   rw 6 q91 ∷
   rw 9 q91 ∷
   rw 12 q92 ∷
   rw 20 q89 ∷
   rw 23 q89 ∷
   rw 26 q93 ∷
   rw 29 q91 ∷ []) Eq.refl

private
  q94 : Eqn
  q94 = wE 1414 W
  q95 : Eqn
  q95 = wE 2338 W
  q96 : Eqn
  q96 = sE 2355 lem-pass-X3-CK32-X3-vs-CS13-TOFF102-CSd13-TOFF102
  q97 : Eqn
  q97 = wE 2339 W

-- pass [X3 CK32 X3] [X0 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0]: 5 steps
lem-pass-X3-CK32-X3-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 : ⟪ (ℓ "丞乗丞丌丏丑与与丽习举习丏丏丐与丌") ⟫ʷ ≈ ⟪ (ℓ "丌丏丑与与丽习举习丏丏丐与丌丞乗丞") ⟫ʷ
lem-pass-X3-CK32-X3-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 = derive (ℓ "丞乗丞丌丏丑与与丽习举习丏丏丐与丌") (ℓ "丌丏丑与与丽习举习丏丏丐与丌丞乗丞")
  (rw 0 q94 ∷
   rw 1 q95 ∷
   rw 5 q96 ∷
   rw 9 q97 ∷
   rw 13 q94 ∷ []) Eq.refl

private
  q98 : Eqn
  q98 = wE 2340 W
  q99 : Eqn
  q99 = wE 2341 W
  q100 : Eqn
  q100 = sE 2351 lem-pass-X2-CKd23-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q101 : Eqn
  q101 = wE 2342 W

-- pass [X2 CKd23 X2] [X0 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0]: 5 steps
lem-pass-X2-CKd23-X2-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 : ⟪ (ℓ "丘乎丘丌丏丑与与丽习举习丏丏丐与丌") ⟫ʷ ≈ ⟪ (ℓ "丌丏丑与与丽习举习丏丏丐与丌丘乎丘") ⟫ʷ
lem-pass-X2-CKd23-X2-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 = derive (ℓ "丘乎丘丌丏丑与与丽习举习丏丏丐与丌") (ℓ "丌丏丑与与丽习举习丏丏丐与丌丘乎丘")
  (rw 0 q98 ∷
   rw 1 q99 ∷
   rw 5 q100 ∷
   rw 9 q101 ∷
   rw 13 q98 ∷ []) Eq.refl

private
  q102 : Eqn
  q102 = wE 2343 W
  q103 : Eqn
  q103 = wE 2344 W
  q104 : Eqn
  q104 = sE 2350 lem-pass-X2-CK23-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q105 : Eqn
  q105 = wE 2345 W

-- pass [X2 CK23 X2] [X0 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0]: 5 steps
lem-pass-X2-CK23-X2-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 : ⟪ (ℓ "丘乍丘丌丏丑与与丽习举习丏丏丐与丌") ⟫ʷ ≈ ⟪ (ℓ "丌丏丑与与丽习举习丏丏丐与丌丘乍丘") ⟫ʷ
lem-pass-X2-CK23-X2-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 = derive (ℓ "丘乍丘丌丏丑与与丽习举习丏丏丐与丌") (ℓ "丌丏丑与与丽习举习丏丏丐与丌丘乍丘")
  (rw 0 q102 ∷
   rw 1 q103 ∷
   rw 5 q104 ∷
   rw 9 q105 ∷
   rw 13 q102 ∷ []) Eq.refl

private
  q106 : Eqn
  q106 = wE 1689 W
  q107 : Eqn
  q107 = wE 2064 W
  q108 : Eqn
  q108 = wE 2119 W

-- pass [X3 CS31 X3] [X0 X2 CS13 TOFF102 CSd13 TOFF102 X0 X2]: 31 steps
lem-pass-X3-CS31-X3-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 : ⟪ (ℓ "丞丽丞丌丘丽习举习丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘丽习举习丌丘丞丽丞") ⟫ʷ
lem-pass-X3-CS31-X3-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 = derive (ℓ "丞丽丞丌丘丽习举习丌丘") (ℓ "丌丘丽习举习丌丘丞丽丞")
  (rw 4 q35 ∷
   rw 3 q82 ∷
   rw 2 q44 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q36 ∷
   rw 0 q44 ∷
   rw 1 q106 ∷
   rw⁻ 0 q82 ∷
   rw 1 q39 ∷
   rw 4 q35 ∷
   re 2 3 (ℓ "丽") ∷
   rw 3 q39 ∷
   rw 4 q36 ∷
   rw 1 q107 ∷
   rw 2 q108 ∷
   rw 2 q23 ∷
   rw 6 q108 ∷
   rw 10 q35 ∷
   rw 9 q82 ∷
   rw 8 q44 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 9 q36 ∷
   rw 6 q44 ∷
   rw 7 q106 ∷
   rw⁻ 6 q82 ∷
   rw 7 q39 ∷
   rw 10 q35 ∷
   re 8 3 (ℓ "丽") ∷
   rw 9 q39 ∷
   rw 10 q36 ∷
   rw 7 q107 ∷ []) Eq.refl

private
  q109 : Eqn
  q109 = wE 2063 W

-- pass [X3 CSd31 X3] [X0 X2 CS13 TOFF102 CSd13 TOFF102 X0 X2]: 31 steps
lem-pass-X3-CSd31-X3-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 : ⟪ (ℓ "丞举丞丌丘丽习举习丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘丽习举习丌丘丞举丞") ⟫ʷ
lem-pass-X3-CSd31-X3-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 = derive (ℓ "丞举丞丌丘丽习举习丌丘") (ℓ "丌丘丽习举习丌丘丞举丞")
  (rw 4 q35 ∷
   rw 3 q82 ∷
   rw 2 q44 ∷
   re 1 1 (ℓ "乏丷乏") ∷
   rw 3 q36 ∷
   rw 0 q44 ∷
   rw 1 q83 ∷
   rw⁻ 0 q82 ∷
   rw 1 q39 ∷
   rw 4 q35 ∷
   re 2 3 (ℓ "举") ∷
   rw 3 q39 ∷
   rw 4 q36 ∷
   rw 1 q109 ∷
   rw 2 q84 ∷
   rw 2 q25 ∷
   rw 6 q84 ∷
   rw 10 q35 ∷
   rw 9 q82 ∷
   rw 8 q44 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q36 ∷
   rw 6 q44 ∷
   rw 7 q83 ∷
   rw⁻ 6 q82 ∷
   rw 7 q39 ∷
   rw 10 q35 ∷
   re 8 3 (ℓ "举") ∷
   rw 9 q39 ∷
   rw 10 q36 ∷
   rw 7 q109 ∷ []) Eq.refl

private
  q110 : Eqn
  q110 = sE 2083 lem-S2-at1023-ᵖ-1
  q111 : Eqn
  q111 = wE 1102 W
  q112 : Eqn
  q112 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q113 : Eqn
  q113 = eqn (ℓ "丌丶") (ℓ "丶丌") (low₁-comm (X) (CS))
  q114 : Eqn
  q114 = wE 387 W
  q115 : Eqn
  q115 = eqn (ℓ "丶丞") (ℓ "丞丶") (low₃-comm ((CS ↑)) (X))
  q116 : Eqn
  q116 = wE 390 W
  q117 : Eqn
  q117 = wE 1609 W
  q118 : Eqn
  q118 = eqn (ℓ "习丞") (ℓ "丞习") (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))
  q119 : Eqn
  q119 = wE 389 W
  q120 : Eqn
  q120 = eqn (ℓ "丌丷") (ℓ "丷丌") (low₁-comm (X) ((CS • CS • CS)))
  q121 : Eqn
  q121 = eqn (ℓ "丷丞") (ℓ "丞丷") (low₃-comm (((CS • CS • CS) ↑)) (X))
  q122 : Eqn
  q122 = sE 2409 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-CS12-X2
  q123 : Eqn
  q123 = sE 2158 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-TOFF103-X0-X3
  q124 : Eqn
  q124 = sE 2410 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-CSd12-X2
  q125 : Eqn
  q125 = sE 2413 lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡-1⟩-CS12-TOFF103-CSd12-TOFF103

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X0 X2 X3 CS13 TOFF102 CSd13 TOFF102 X0 X2 X3]: 39 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丌丘丞丽习举习丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丽习举习丌丘丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丌丘丞丽习举习丌丘丞") (ℓ "丌丘丞丽习举习丌丘丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 32 q110 ∷
   rw 33 q111 ∷
   rw 40 q111 ∷
   rw 47 q111 ∷
   rw 29 q10 ∷
   rw 30 q112 ∷
   rw 31 q113 ∷
   rw 32 q114 ∷
   rw⁻ 30 q115 ∷
   rw⁻ 31 q12 ∷
   rw 32 q116 ∷
   rw 33 q12 ∷
   re 35 1 (ℓ "乏习乏") ∷
   rw 34 q117 ∷
   rw⁻ 35 q118 ∷
   rw 36 q44 ∷
   re 34 3 (ℓ "乡") ∷
   rw⁻ 35 q10 ∷
   rw 36 q119 ∷
   rw 37 q10 ∷
   rw 38 q112 ∷
   rw 39 q120 ∷
   rw 40 q114 ∷
   rw⁻ 38 q121 ∷
   rw⁻ 39 q12 ∷
   rw 40 q116 ∷
   rw 41 q12 ∷
   re 43 1 (ℓ "乏习乏") ∷
   rw 42 q117 ∷
   rw⁻ 43 q118 ∷
   rw 44 q44 ∷
   re 42 3 (ℓ "乡") ∷
   rw⁻ 43 q10 ∷
   rw 44 q119 ∷
   rw 0 q122 ∷
   rw 3 q123 ∷
   rw 8 q124 ∷
   rw 11 q123 ∷
   rw⁻ 0 q125 ∷ []) Eq.refl

private
  q126 : Eqn
  q126 = wE 2346 W
  q127 : Eqn
  q127 = wE 2347 W
  q128 : Eqn
  q128 = sE 2422 lem-pass-X3-CS32-X3-vs-CS13-TOFF102-CSd13-TOFF102
  q129 : Eqn
  q129 = sE 2425 lem-pass-X3-CSd32-X3-vs-CS13-TOFF102-CSd13-TOFF102
  q130 : Eqn
  q130 = wE 2348 W
  q131 : Eqn
  q131 = wE 2349 W

-- pass [X3 CKd32 X3] [X0 X2 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2]: 9 steps
lem-pass-X3-CKd32-X3-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 : ⟪ (ℓ "丞乘丞丌丘丏丑与与丽习举习丏丏丐与丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘丏丑与与丽习举习丏丏丐与丌丘丞乘丞") ⟫ʷ
lem-pass-X3-CKd32-X3-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 = derive (ℓ "丞乘丞丌丘丏丑与与丽习举习丏丏丐与丌丘") (ℓ "丌丘丏丑与与丽习举习丏丏丐与丌丘丞乘丞")
  (rw 0 q126 ∷
   rw 2 q127 ∷
   rw 18 q128 ∷
   rw 15 q96 ∷
   rw 12 q129 ∷
   rw 9 q96 ∷
   rw 6 q128 ∷
   rw 10 q130 ∷
   rw 14 q131 ∷ []) Eq.refl

private
  q132 : Eqn
  q132 = wE 2350 W
  q133 : Eqn
  q133 = wE 2351 W
  q134 : Eqn
  q134 = wE 2352 W
  q135 : Eqn
  q135 = wE 2353 W

-- pass [X3 CK32 X3] [X0 X2 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2]: 9 steps
lem-pass-X3-CK32-X3-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 : ⟪ (ℓ "丞乗丞丌丘丏丑与与丽习举习丏丏丐与丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘丏丑与与丽习举习丏丏丐与丌丘丞乗丞") ⟫ʷ
lem-pass-X3-CK32-X3-vs-X0-X2-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2 = derive (ℓ "丞乗丞丌丘丏丑与与丽习举习丏丏丐与丌丘") (ℓ "丌丘丏丑与与丽习举习丏丏丐与丌丘丞乗丞")
  (rw 0 q132 ∷
   rw 2 q133 ∷
   rw 18 q129 ∷
   rw 15 q87 ∷
   rw 12 q128 ∷
   rw 9 q87 ∷
   rw 6 q129 ∷
   rw 10 q134 ∷
   rw 14 q135 ∷ []) Eq.refl
