{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD739 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D739 (W : Ws) (Sᴰ : SD739) where

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
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK32-X3 : St 226
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK32-X3 = pickᴰ 0 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CKd32-X3 : St 232
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CKd32-X3 = pickᴰ 1 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS23-X3 : St 241
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS23-X3 = pickᴰ 2 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd23-X3 : St 243
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd23-X3 = pickᴰ 3 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK32-X3 : St 389
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK32-X3 = pickᴰ 4 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CKd32-X3 : St 390
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CKd32-X3 = pickᴰ 5 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS23-X3 : St 392
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS23-X3 = pickᴰ 6 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd23-X3 : St 395
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd23-X3 = pickᴰ 7 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK32-X3 : St 400
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK32-X3 = pickᴰ 8 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd32-X3 : St 407
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd32-X3 = pickᴰ 9 Sᴰ
  lem-pass-CCZ123-vs-X3-CK32-X3 : St 2336
  lem-pass-CCZ123-vs-X3-CK32-X3 = pickᴰ 10 Sᴰ
  lem-pass-CCZ123-vs-X3-CKd32-X3 : St 2337
  lem-pass-CCZ123-vs-X3-CKd32-X3 = pickᴰ 11 Sᴰ
  lem-pass-CCZ123-vs-X3-CS23-X3 : St 2338
  lem-pass-CCZ123-vs-X3-CS23-X3 = pickᴰ 12 Sᴰ
  lem-pass-CCZ123-vs-X3-CSd23-X3 : St 2339
  lem-pass-CCZ123-vs-X3-CSd23-X3 = pickᴰ 13 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-X3 : St 2374
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-X3 = pickᴰ 14 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd23-X3 : St 2375
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd23-X3 = pickᴰ 15 Sᴰ
  lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 869
  lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 16 Sᴰ
  lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 904
  lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 17 Sᴰ
  lem-pass-CK30-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : St 2362
  lem-pass-CK30-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = pickᴰ 18 Sᴰ
  lem-pass-CK32-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 : St 2376
  lem-pass-CK32-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 = pickᴰ 19 Sᴰ
  lem-pass-CKd32-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 : St 2377
  lem-pass-CKd32-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 = pickᴰ 20 Sᴰ
  lem-CA-CS10-Gad⟨t≡0-W≡⟨3⟩-d≡Sd-e≡1⟩ : St 2378
  lem-CA-CS10-Gad⟨t≡0-W≡⟨3⟩-d≡Sd-e≡1⟩ = pickᴰ 21 Sᴰ
  lem-CA-CSd10-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡1⟩ : St 2379
  lem-CA-CSd10-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡1⟩ = pickᴰ 22 Sᴰ
  lem-pass-CCZ123-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : St 2007
  lem-pass-CCZ123-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = pickᴰ 23 Sᴰ
  lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 2245
  lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 24 Sᴰ
  lem-pass-X1-CKd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 2278
  lem-pass-X1-CKd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 25 Sᴰ
  lem-pass-CCZ123-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : St 2380
  lem-pass-CCZ123-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = pickᴰ 26 Sᴰ
  lem-pass-CCZ123-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 : St 2381
  lem-pass-CCZ123-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 = pickᴰ 27 Sᴰ
  lem-pass-CK32-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : St 2382
  lem-pass-CK32-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = pickᴰ 28 Sᴰ
  lem-pass-CKd30-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3 : St 2368
  lem-pass-CKd30-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3 = pickᴰ 29 Sᴰ
  lem-pass-CKd32-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : St 2383
  lem-pass-CKd32-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = pickᴰ 30 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 : St 2384
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 = pickᴰ 31 Sᴰ
  lem-pass-CS32-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 : St 2385
  lem-pass-CS32-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 = pickᴰ 32 Sᴰ
  lem-pass-X2-CK23-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : St 2386
  lem-pass-X2-CK23-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = pickᴰ 33 Sᴰ
  lem-pass-X2-CKd23-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : St 2387
  lem-pass-X2-CKd23-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = pickᴰ 34 Sᴰ
  lem-pass-X3-CK31-X3-vs-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2 : St 2388
  lem-pass-X3-CK31-X3-vs-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2 = pickᴰ 35 Sᴰ
  lem-pass-X3-CKd31-X3-vs-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2 : St 2389
  lem-pass-X3-CKd31-X3-vs-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2 = pickᴰ 36 Sᴰ
  lem-pass-CCZ123-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : St 2390
  lem-pass-CCZ123-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = pickᴰ 37 Sᴰ
  lem-pass-CCZ123-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 : St 2391
  lem-pass-CCZ123-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 = pickᴰ 38 Sᴰ
  lem-pass-CK13-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : St 2392
  lem-pass-CK13-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = pickᴰ 39 Sᴰ
  lem-pass-CKd13-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : St 2393
  lem-pass-CKd13-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = pickᴰ 40 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 : St 2394
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 = pickᴰ 41 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 : St 2395
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 = pickᴰ 42 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 : St 2396
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 = pickᴰ 43 Sᴰ
  lem-pass-X1-CK10-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : St 2397
  lem-pass-X1-CK10-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = pickᴰ 44 Sᴰ
  lem-pass-X2-CK23-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : St 2398
  lem-pass-X2-CK23-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = pickᴰ 45 Sᴰ
  lem-pass-X2-CKd20-X2-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3 : St 2399
  lem-pass-X2-CKd20-X2-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3 = pickᴰ 46 Sᴰ
  lem-pass-X2-CKd20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : St 2400
  lem-pass-X2-CKd20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = pickᴰ 47 Sᴰ
  lem-pass-X2-CKd21-X2-vs-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X3 : St 2401
  lem-pass-X2-CKd21-X2-vs-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X3 = pickᴰ 48 Sᴰ
  lem-pass-X2-CKd23-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : St 2402
  lem-pass-X2-CKd23-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = pickᴰ 49 Sᴰ
  lem-pass-X3-CK31-X3-vs-X0-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X0 : St 2403
  lem-pass-X3-CK31-X3-vs-X0-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X0 = pickᴰ 50 Sᴰ
  lem-pass-X3-CK32-X3-vs-X0-TOFF102-CS13-TOFF102-CSd13-X0 : St 2404
  lem-pass-X3-CK32-X3-vs-X0-TOFF102-CS13-TOFF102-CSd13-X0 = pickᴰ 51 Sᴰ
  lem-pass-X3-CKd31-X3-vs-X0-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X0 : St 2405
  lem-pass-X3-CKd31-X3-vs-X0-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X0 = pickᴰ 52 Sᴰ
  lem-pass-X3-CKd32-X3-vs-X0-TOFF102-CS13-TOFF102-CSd13-X0 : St 2406
  lem-pass-X3-CKd32-X3-vs-X0-TOFF102-CS13-TOFF102-CSd13-X0 = pickᴰ 53 Sᴰ
  lem-pass-X3-CS32-X3-vs-X0-TOFF201-CS23-TOFF201-CSd23-X0 : St 2407
  lem-pass-X3-CS32-X3-vs-X0-TOFF201-CS23-TOFF201-CSd23-X0 = pickᴰ 54 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 : St 2408
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 = pickᴰ 55 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q3 : Eqn
  q3 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q6 : Eqn
  q6 = wE 2299 W
  q7 : Eqn
  q7 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q8 : Eqn
  q8 = sE 2379 lem-CA-CSd10-Gad⟨t≡0-W≡⟨3⟩-d≡1-e≡1⟩
  q9 : Eqn
  q9 = sE 2368 lem-pass-CKd30-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3
  q10 : Eqn
  q10 = sE 2378 lem-CA-CS10-Gad⟨t≡0-W≡⟨3⟩-d≡Sd-e≡1⟩
  q11 : Eqn
  q11 = sE 2362 lem-pass-CK30-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3
  q12 : Eqn
  q12 = wE 2300 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 TOFF012 CS03 TOFF012 CSd03 X3]: 96 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞九中九丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞九中九丮丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞九中九丮丞") (ℓ "丞九中九丮丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 29 q1 ∷
   rw 28 q2 ∷
   rw 27 q2 ∷
   rw 26 q3 ∷
   rw 25 q2 ∷
   rw 24 q3 ∷
   rw 23 q3 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 24 q4 ∷
   rw 21 q3 ∷
   rw 20 q3 ∷
   rw 19 q3 ∷
   rw 18 q3 ∷
   rw 17 q3 ∷
   rw 16 q3 ∷
   rw 15 q5 ∷
   rw 14 q2 ∷
   rw 13 q3 ∷
   rw 12 q3 ∷
   rw 11 q3 ∷
   rw 10 q5 ∷
   rw 9 q2 ∷
   rw 8 q5 ∷
   rw 7 q2 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 8 q4 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw 7 q4 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw 6 q4 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q4 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw 4 q4 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q4 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q4 ∷
   rw 1 q6 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "乑") ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "乒") ∷
   rw⁻ 3 q7 ∷
   rw 4 q4 ∷
   rw 3 q8 ∷
   rw 2 q9 ∷
   rw 1 q10 ∷
   rw 0 q11 ∷
   rw 10 q1 ∷
   rw 9 q7 ∷
   re 8 1 (ℓ "乏久乏") ∷
   rw 10 q4 ∷
   rw 7 q3 ∷
   re 6 1 (ℓ "乏乄乏") ∷
   rw 8 q4 ∷
   rw 7 q12 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "乑") ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "乑") ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "乑") ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "乓") ∷
   rw⁻ 13 q2 ∷
   rw⁻ 14 q5 ∷
   rw⁻ 15 q2 ∷
   rw⁻ 16 q5 ∷
   rw⁻ 17 q3 ∷
   rw⁻ 18 q3 ∷
   rw⁻ 19 q3 ∷
   rw⁻ 20 q2 ∷
   rw⁻ 21 q5 ∷
   rw⁻ 22 q3 ∷
   rw⁻ 23 q3 ∷
   rw⁻ 24 q3 ∷
   rw⁻ 25 q3 ∷
   rw⁻ 26 q3 ∷
   rw⁻ 27 q3 ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "乓") ∷
   rw⁻ 29 q3 ∷
   rw⁻ 30 q3 ∷
   rw⁻ 31 q2 ∷
   rw⁻ 32 q3 ∷
   rw⁻ 33 q2 ∷
   rw⁻ 34 q2 ∷
   rw 35 q4 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = sE 2380 lem-pass-CCZ123-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3

-- CCZ(3,1,2) passes split Gad(t=1, W=(3,), d=1, e=1): 1 steps
lem-CCZ⟨312⟩-passes-split-Gad⟨t≡1-W≡⟨3⟩-d≡1-e≡1⟩ : ⟪ (ℓ "乜丞习丽习举丞") ⟫ʷ ≈ ⟪ (ℓ "丞习丽习举丞乜") ⟫ʷ
lem-CCZ⟨312⟩-passes-split-Gad⟨t≡1-W≡⟨3⟩-d≡1-e≡1⟩ = derive (ℓ "乜丞习丽习举丞") (ℓ "丞习丽习举丞乜")
  (rw 0 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = wE 2297 W
  q15 : Eqn
  q15 = sE 2383 lem-pass-CKd32-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3
  q16 : Eqn
  q16 = sE 2382 lem-pass-CK32-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3
  q17 : Eqn
  q17 = wE 2298 W

-- pass [TOFF213] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 5 steps
lem-pass-TOFF213-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (ℓ "乥丞习丽习举丞") ⟫ʷ ≈ ⟪ (ℓ "丞习丽习举丞乥") ⟫ʷ
lem-pass-TOFF213-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (ℓ "乥丞习丽习举丞") (ℓ "丞习丽习举丞乥")
  (rw 0 q14 ∷
   rw 2 q15 ∷
   rw 1 q13 ∷
   rw 0 q16 ∷
   rw 6 q17 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = wE 2301 W
  q19 : Eqn
  q19 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q20 : Eqn
  q20 = sE 2387 lem-pass-X2-CKd23-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3
  q21 : Eqn
  q21 = wE 2302 W

-- pass [CKd23] [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3]: 5 steps
lem-pass-CKd23-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : ⟪ (ℓ "乎丘丞习丽习举丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞习丽习举丘丞乎") ⟫ʷ
lem-pass-CKd23-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = derive (ℓ "乎丘丞习丽习举丘丞") (ℓ "丘丞习丽习举丘丞乎")
  (rw 0 q18 ∷
   rw 9 q19 ∷
   rw 1 q20 ∷
   rw 7 q21 ∷
   rw⁻ 6 q19 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = wE 2303 W
  q23 : Eqn
  q23 = sE 2386 lem-pass-X2-CK23-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3
  q24 : Eqn
  q24 = wE 2304 W

-- pass [CK23] [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3]: 5 steps
lem-pass-CK23-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : ⟪ (ℓ "乍丘丞习丽习举丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞习丽习举丘丞乍") ⟫ʷ
lem-pass-CK23-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = derive (ℓ "乍丘丞习丽习举丘丞") (ℓ "丘丞习丽习举丘丞乍")
  (rw 0 q22 ∷
   rw 9 q19 ∷
   rw 1 q23 ∷
   rw 7 q24 ∷
   rw⁻ 6 q19 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = eqn (ℓ "世丞") (ℓ "丞世") (low₃-comm ((K ↑ ↑)) (X))
  q26 : Eqn
  q26 = eqn (ℓ "且丞") (ℓ "丞且") (low₃-comm ((S ↑ ↑)) (X))
  q27 : Eqn
  q27 = eqn (ℓ "丗丞") (ℓ "丞丗") (low₃-comm (((K • iI) ↑ ↑)) (X))
  q28 : Eqn
  q28 = eqn (ℓ "丕丞") (ℓ "丞丕") (low₃-comm (((S • S • S) ↑ ↑)) (X))
  q29 : Eqn
  q29 = wE 2305 W
  q30 : Eqn
  q30 = wE 2306 W
  q31 : Eqn
  q31 = sE 2377 lem-pass-CKd32-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3
  q32 : Eqn
  q32 = sE 2385 lem-pass-CS32-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3
  q33 : Eqn
  q33 = sE 2376 lem-pass-CK32-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3
  q34 : Eqn
  q34 = wE 2307 W

-- ca-split Gad(t=2, W=(3,), d=KSSKd, e=1) 3: 15 steps
lem-ca-split-Gad⟨t≡2-W≡⟨3⟩-d≡KSSKd-e≡1⟩-3 : ⟪ (ℓ "丞世且且丗乣义乣乊世丕丕丗丞") ⟫ʷ ≈ ⟪ (ℓ "丞乗丞丞义丞丞义丞丞乘丞丞乣义乣乊丞丞乗丞丞乊丞丞乊丞丞乘丞") ⟫ʷ
lem-ca-split-Gad⟨t≡2-W≡⟨3⟩-d≡KSSKd-e≡1⟩-3 = derive (ℓ "丞世且且丗乣义乣乊世丕丕丗丞") (ℓ "丞乗丞丞义丞丞义丞丞乘丞丞乣义乣乊丞丞乗丞丞乊丞丞乊丞丞乘丞")
  (rw⁻ 0 q25 ∷
   rw⁻ 1 q26 ∷
   rw⁻ 2 q26 ∷
   rw⁻ 3 q27 ∷
   rw 12 q27 ∷
   rw 11 q28 ∷
   rw 10 q28 ∷
   rw 9 q25 ∷
   rw 0 q29 ∷
   rw 22 q30 ∷
   rw 15 q31 ∷
   rw 14 q32 ∷
   rw 13 q32 ∷
   rw 12 q33 ∷
   rw 18 q34 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = sE 226 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK32-X3
  q36 : Eqn
  q36 = sE 241 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS23-X3
  q37 : Eqn
  q37 = sE 232 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CKd32-X3
  q38 : Eqn
  q38 = sE 2384 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3
  q39 : Eqn
  q39 = sE 243 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd23-X3

-- Bar(SSKSKK;3,1->0) passes split Gad(t=2, W=(3,), d=KSSKd, e=1): 9 steps
lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡KSSKd-e≡1⟩ : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乗丞丞义丞丞义丞丞乘丞丞乣义乣乊丞丞乗丞丞乊丞丞乊丞丞乘丞") ⟫ʷ ≈ ⟪ (ℓ "丞乗丞丞义丞丞义丞丞乘丞丞乣义乣乊丞丞乗丞丞乊丞丞乊丞丞乘丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡KSSKd-e≡1⟩ = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乗丞丞义丞丞义丞丞乘丞丞乣义乣乊丞丞乗丞丞乊丞丞乊丞丞乘丞") (ℓ "丞乗丞丞义丞丞义丞丞乘丞丞乣义乣乊丞丞乗丞丞乊丞丞乊丞丞乘丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 0 q35 ∷
   rw 3 q36 ∷
   rw 6 q36 ∷
   rw 9 q37 ∷
   rw 12 q38 ∷
   rw 18 q35 ∷
   rw 21 q39 ∷
   rw 24 q39 ∷
   rw 27 q37 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = wE 1940 W
  q41 : Eqn
  q41 = sE 2389 lem-pass-X3-CKd31-X3-vs-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2
  q42 : Eqn
  q42 = wE 1941 W

-- pass [CKd31] [X3 K2 S2 S2 Kd2 TOFF201 CS23 TOFF201 CSd23 K2 Sd2 Sd2 Kd2 X3]: 3 steps
lem-pass-CKd31-vs-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X3 : ⟪ (ℓ "乕丞世且且丗乣义乣乊世丕丕丗丞") ⟫ʷ ≈ ⟪ (ℓ "丞世且且丗乣义乣乊世丕丕丗丞乕") ⟫ʷ
lem-pass-CKd31-vs-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X3 = derive (ℓ "乕丞世且且丗乣义乣乊世丕丕丗丞") (ℓ "丞世且且丗乣义乣乊世丕丕丗丞乕")
  (rw 0 q40 ∷
   rw 1 q41 ∷
   rw 13 q42 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = sE 2336 lem-pass-CCZ123-vs-X3-CK32-X3
  q44 : Eqn
  q44 = sE 2338 lem-pass-CCZ123-vs-X3-CS23-X3
  q45 : Eqn
  q45 = sE 2337 lem-pass-CCZ123-vs-X3-CKd32-X3
  q46 : Eqn
  q46 = sE 2381 lem-pass-CCZ123-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3
  q47 : Eqn
  q47 = sE 2339 lem-pass-CCZ123-vs-X3-CSd23-X3

-- CCZ(3,2,1) passes split Gad(t=2, W=(3,), d=KSSKd, e=1): 9 steps
lem-CCZ⟨321⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡KSSKd-e≡1⟩ : ⟪ (ℓ "乜丞乗丞丞义丞丞义丞丞乘丞丞乣义乣乊丞丞乗丞丞乊丞丞乊丞丞乘丞") ⟫ʷ ≈ ⟪ (ℓ "丞乗丞丞义丞丞义丞丞乘丞丞乣义乣乊丞丞乗丞丞乊丞丞乊丞丞乘丞乜") ⟫ʷ
lem-CCZ⟨321⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡KSSKd-e≡1⟩ = derive (ℓ "乜丞乗丞丞义丞丞义丞丞乘丞丞乣义乣乊丞丞乗丞丞乊丞丞乊丞丞乘丞") (ℓ "丞乗丞丞义丞丞义丞丞乘丞丞乣义乣乊丞丞乗丞丞乊丞丞乊丞丞乘丞乜")
  (rw 0 q43 ∷
   rw 3 q44 ∷
   rw 6 q44 ∷
   rw 9 q45 ∷
   rw 12 q46 ∷
   rw 18 q43 ∷
   rw 21 q47 ∷
   rw 24 q47 ∷
   rw 27 q45 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = wE 1366 W
  q49 : Eqn
  q49 = sE 2388 lem-pass-X3-CK31-X3-vs-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2
  q50 : Eqn
  q50 = wE 1367 W

-- pass [CK31] [X3 K2 S2 S2 Kd2 TOFF201 CS23 TOFF201 CSd23 K2 Sd2 Sd2 Kd2 X3]: 3 steps
lem-pass-CK31-vs-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X3 : ⟪ (ℓ "乔丞世且且丗乣义乣乊世丕丕丗丞") ⟫ʷ ≈ ⟪ (ℓ "丞世且且丗乣义乣乊世丕丕丗丞乔") ⟫ʷ
lem-pass-CK31-vs-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X3 = derive (ℓ "乔丞世且且丗乣义乣乊世丕丕丗丞") (ℓ "丞世且且丗乣义乣乊世丕丕丗丞乔")
  (rw 0 q48 ∷
   rw 1 q49 ∷
   rw 13 q50 ∷ []) Eq.refl

private
  q51 : Eqn
  q51 = sE 389 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK32-X3
  q52 : Eqn
  q52 = sE 392 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS23-X3
  q53 : Eqn
  q53 = sE 390 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CKd32-X3
  q54 : Eqn
  q54 = sE 2396 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3
  q55 : Eqn
  q55 = sE 395 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd23-X3

-- Bar(SSSKSS;3,1->0) passes split Gad(t=2, W=(3,), d=KSSKd, e=1): 9 steps
lem-Bar⟨SSSKSS31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡KSSKd-e≡1⟩ : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乗丞丞义丞丞义丞丞乘丞丞乣义乣乊丞丞乗丞丞乊丞丞乊丞丞乘丞") ⟫ʷ ≈ ⟪ (ℓ "丞乗丞丞义丞丞义丞丞乘丞丞乣义乣乊丞丞乗丞丞乊丞丞乊丞丞乘丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-Bar⟨SSSKSS31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡KSSKd-e≡1⟩ = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乗丞丞义丞丞义丞丞乘丞丞乣义乣乊丞丞乗丞丞乊丞丞乊丞丞乘丞") (ℓ "丞乗丞丞义丞丞义丞丞乘丞丞乣义乣乊丞丞乗丞丞乊丞丞乊丞丞乘丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 0 q51 ∷
   rw 3 q52 ∷
   rw 6 q52 ∷
   rw 9 q53 ∷
   rw 12 q54 ∷
   rw 18 q51 ∷
   rw 21 q55 ∷
   rw 24 q55 ∷
   rw 27 q53 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = sE 400 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK32-X3
  q57 : Eqn
  q57 = sE 2374 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-X3
  q58 : Eqn
  q58 = sE 407 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd32-X3
  q59 : Eqn
  q59 = sE 2395 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3
  q60 : Eqn
  q60 = sE 2375 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd23-X3

-- Bar(SSKSKK;3,2->0) passes split Gad(t=2, W=(3,), d=KSSKd, e=1): 9 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡KSSKd-e≡1⟩ : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乗丞丞义丞丞义丞丞乘丞丞乣义乣乊丞丞乗丞丞乊丞丞乊丞丞乘丞") ⟫ʷ ≈ ⟪ (ℓ "丞乗丞丞义丞丞义丞丞乘丞丞乣义乣乊丞丞乗丞丞乊丞丞乊丞丞乘丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨3⟩-d≡KSSKd-e≡1⟩ = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乗丞丞义丞丞义丞丞乘丞丞乣义乣乊丞丞乗丞丞乊丞丞乊丞丞乘丞") (ℓ "丞乗丞丞义丞丞义丞丞乘丞丞乣义乣乊丞丞乗丞丞乊丞丞乊丞丞乘丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 0 q56 ∷
   rw 3 q57 ∷
   rw 6 q57 ∷
   rw 9 q58 ∷
   rw 12 q59 ∷
   rw 18 q56 ∷
   rw 21 q60 ∷
   rw 24 q60 ∷
   rw 27 q58 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = wE 2267 W
  q62 : Eqn
  q62 = wE 2268 W
  q63 : Eqn
  q63 = wE 2308 W
  q64 : Eqn
  q64 = sE 2278 lem-pass-X1-CKd10-X1-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [X1 CKd10 X1] [X2 X3 TOFF012 CS03 TOFF012 CSd03 X2 X3]: 7 steps
lem-pass-X1-CKd10-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : ⟪ (ℓ "丒丵丒丘丞九中九丮丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞九中九丮丘丞丒丵丒") ⟫ʷ
lem-pass-X1-CKd10-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = derive (ℓ "丒丵丒丘丞九中九丮丘丞") (ℓ "丘丞九中九丮丘丞丒丵丒")
  (rw 0 q61 ∷
   rw 1 q62 ∷
   rw 2 q63 ∷
   rw 2 q64 ∷
   rw 6 q63 ∷
   rw 6 q61 ∷
   rw 7 q62 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = wE 2205 W
  q66 : Eqn
  q66 = eqn (ℓ "丒丘") (ℓ "丘丒") (low-comm ((X ↑)) (X))
  q67 : Eqn
  q67 = eqn (ℓ "丒丞") (ℓ "丞丒") (low-comm ((X ↑)) ((X ↑)))
  q68 : Eqn
  q68 = sE 2397 lem-pass-X1-CK10-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3
  q69 : Eqn
  q69 = wE 2206 W

-- pass [CK10] [X1 X2 X3 TOFF012 CS03 TOFF012 CSd03 X1 X2 X3]: 7 steps
lem-pass-CK10-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : ⟪ (ℓ "临丒丘丞九中九丮丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞九中九丮丒丘丞临") ⟫ʷ
lem-pass-CK10-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = derive (ℓ "临丒丘丞九中九丮丒丘丞") (ℓ "丒丘丞九中九丮丒丘丞临")
  (rw 0 q65 ∷
   rw 10 q66 ∷
   rw 11 q67 ∷
   rw 1 q68 ∷
   rw 9 q69 ∷
   rw⁻ 8 q67 ∷
   rw⁻ 7 q66 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = wE 2207 W
  q71 : Eqn
  q71 = sE 2393 lem-pass-CKd13-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3
  q72 : Eqn
  q72 = sE 2007 lem-pass-CCZ123-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3
  q73 : Eqn
  q73 = sE 2392 lem-pass-CK13-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3
  q74 : Eqn
  q74 = wE 2208 W

-- pass [TOFF312] [X1 X2 X3 TOFF012 CS03 TOFF012 CSd03 X1 X2 X3]: 5 steps
lem-pass-TOFF312-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : ⟪ (ℓ "乨丒丘丞九中九丮丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞九中九丮丒丘丞乨") ⟫ʷ
lem-pass-TOFF312-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = derive (ℓ "乨丒丘丞九中九丮丒丘丞") (ℓ "丒丘丞九中九丮丒丘丞乨")
  (rw 0 q70 ∷
   rw 2 q71 ∷
   rw 1 q72 ∷
   rw 0 q73 ∷
   rw 10 q74 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = wE 1497 W
  q76 : Eqn
  q76 = wE 1498 W
  q77 : Eqn
  q77 = sE 2245 lem-pass-X2-CKd21-X2-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [X2 CKd21 X2] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 5 steps
lem-pass-X2-CKd21-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (ℓ "丘么丘丞习丽习举丞") ⟫ʷ ≈ ⟪ (ℓ "丞习丽习举丞丘么丘") ⟫ʷ
lem-pass-X2-CKd21-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (ℓ "丘么丘丞习丽习举丞") (ℓ "丞习丽习举丞丘么丘")
  (rw 0 q75 ∷
   rw 1 q76 ∷
   rw 1 q77 ∷
   rw 5 q76 ∷
   rw 5 q75 ∷ []) Eq.refl

private
  q78 : Eqn
  q78 = wE 1478 W
  q79 : Eqn
  q79 = sE 2401 lem-pass-X2-CKd21-X2-vs-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X3
  q80 : Eqn
  q80 = wE 1479 W

-- pass [CKd21] [X2 X3 K1 S1 S1 Kd1 TOFF102 CS13 TOFF102 CSd13 K1 Sd1 Sd1 Kd1 X2 X3]: 5 steps
lem-pass-CKd21-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3 : ⟪ (ℓ "么丘丞丐与与丑习丽习举丐丏丏丑丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丐与与丑习丽习举丐丏丏丑丘丞么") ⟫ʷ
lem-pass-CKd21-vs-X2-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X2-X3 = derive (ℓ "么丘丞丐与与丑习丽习举丐丏丏丑丘丞") (ℓ "丘丞丐与与丑习丽习举丐丏丏丑丘丞么")
  (rw 0 q78 ∷
   rw 17 q19 ∷
   rw 1 q79 ∷
   rw 15 q80 ∷
   rw⁻ 14 q19 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = wE 1495 W
  q82 : Eqn
  q82 = wE 2309 W
  q83 : Eqn
  q83 = sE 904 lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q84 : Eqn
  q84 = sE 869 lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q85 : Eqn
  q85 = wE 2310 W

-- pass [X2 CK21 X2] [X3 K1 S1 S1 Kd1 TOFF102 CS13 TOFF102 CSd13 K1 Sd1 Sd1 Kd1 X3]: 9 steps
lem-pass-X2-CK21-X2-vs-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X3 : ⟪ (ℓ "丘乇丘丞丐与与丑习丽习举丐丏丏丑丞") ⟫ʷ ≈ ⟪ (ℓ "丞丐与与丑习丽习举丐丏丏丑丞丘乇丘") ⟫ʷ
lem-pass-X2-CK21-X2-vs-X3-K1-S1-S1-Kd1-TOFF102-CS13-TOFF102-CSd13-K1-Sd1-Sd1-Kd1-X3 = derive (ℓ "丘乇丘丞丐与与丑习丽习举丐丏丏丑丞") (ℓ "丞丐与与丑习丽习举丐丏丏丑丞丘乇丘")
  (rw 0 q81 ∷
   rw 1 q82 ∷
   rw 17 q83 ∷
   rw 14 q77 ∷
   rw 11 q84 ∷
   rw 8 q77 ∷
   rw 5 q83 ∷
   rw 9 q85 ∷
   rw 13 q81 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q87 : Eqn
  q87 = wE 1674 W
  q88 : Eqn
  q88 = sE 2406 lem-pass-X3-CKd32-X3-vs-X0-TOFF102-CS13-TOFF102-CSd13-X0
  q89 : Eqn
  q89 = wE 1675 W

-- pass [CKd32] [X0 X3 TOFF102 CS13 TOFF102 CSd13 X0 X3]: 5 steps
lem-pass-CKd32-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : ⟪ (ℓ "乘丌丞习丽习举丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞习丽习举丌丞乘") ⟫ʷ
lem-pass-CKd32-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = derive (ℓ "乘丌丞习丽习举丌丞") (ℓ "丌丞习丽习举丌丞乘")
  (rw 1 q86 ∷
   rw 0 q87 ∷
   rw 1 q88 ∷
   rw 7 q89 ∷
   rw⁻ 0 q86 ∷ []) Eq.refl

private
  q90 : Eqn
  q90 = sE 2390 lem-pass-CCZ123-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3

-- CCZ(3,1,2) passes split Gad(t=1, W=(0, 3), d=1, e=1): 1 steps
lem-CCZ⟨312⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡1-e≡1⟩ : ⟪ (ℓ "乜丌丞习丽习举丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞习丽习举丌丞乜") ⟫ʷ
lem-CCZ⟨312⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡1-e≡1⟩ = derive (ℓ "乜丌丞习丽习举丌丞") (ℓ "丌丞习丽习举丌丞乜")
  (rw 0 q90 ∷ []) Eq.refl

private
  q91 : Eqn
  q91 = wE 1409 W
  q92 : Eqn
  q92 = sE 2404 lem-pass-X3-CK32-X3-vs-X0-TOFF102-CS13-TOFF102-CSd13-X0
  q93 : Eqn
  q93 = wE 1410 W

-- pass [CK32] [X0 X3 TOFF102 CS13 TOFF102 CSd13 X0 X3]: 5 steps
lem-pass-CK32-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : ⟪ (ℓ "乗丌丞习丽习举丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞习丽习举丌丞乗") ⟫ʷ
lem-pass-CK32-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = derive (ℓ "乗丌丞习丽习举丌丞") (ℓ "丌丞习丽习举丌丞乗")
  (rw 1 q86 ∷
   rw 0 q91 ∷
   rw 1 q92 ∷
   rw 7 q93 ∷
   rw⁻ 0 q86 ∷ []) Eq.refl

private
  q94 : Eqn
  q94 = wE 1464 W
  q95 : Eqn
  q95 = sE 2400 lem-pass-X2-CKd20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3
  q96 : Eqn
  q96 = wE 1465 W

-- pass [CKd20] [X2 X3 TOFF012 CS03 TOFF012 CSd03 X2 X3]: 5 steps
lem-pass-CKd20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : ⟪ (ℓ "久丘丞九中九丮丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞九中九丮丘丞久") ⟫ʷ
lem-pass-CKd20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = derive (ℓ "久丘丞九中九丮丘丞") (ℓ "丘丞九中九丮丘丞久")
  (rw 0 q94 ∷
   rw 9 q19 ∷
   rw 1 q95 ∷
   rw 7 q96 ∷
   rw⁻ 6 q19 ∷ []) Eq.refl

private
  q97 : Eqn
  q97 = sE 2399 lem-pass-X2-CKd20-X2-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3

-- pass [CKd20] [X2 X3 Sd0 TOFF012 CS03 TOFF012 CSd03 S0 X2 X3]: 5 steps
lem-pass-CKd20-vs-X2-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X2-X3 : ⟪ (ℓ "久丘丞三九中九丮丈丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞三九中九丮丈丘丞久") ⟫ʷ
lem-pass-CKd20-vs-X2-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X2-X3 = derive (ℓ "久丘丞三九中九丮丈丘丞") (ℓ "丘丞三九中九丮丈丘丞久")
  (rw 0 q94 ∷
   rw 11 q19 ∷
   rw 1 q97 ∷
   rw 9 q96 ∷
   rw⁻ 8 q19 ∷ []) Eq.refl

private
  q98 : Eqn
  q98 = wE 2311 W
  q99 : Eqn
  q99 = eqn (ℓ "下丘") (ℓ "丘下") (low₁-comm ((K • iI)) ((X ↑)))
  q100 : Eqn
  q100 = eqn (ℓ "下丞") (ℓ "丞下") (low₁-comm ((K • iI)) ((X ↑ ↑)))
  q101 : Eqn
  q101 = wE 1710 W
  q102 : Eqn
  q102 = wE 116 W
  q103 : Eqn
  q103 = wE 2312 W

-- CA CKd10 Gad(t=0, W=(2, 3), d=1, e=1): 9 steps
lem-CA-CKd10-Gad⟨t≡0-W≡⟨2-3⟩-d≡1-e≡1⟩ : ⟪ (ℓ "丵丘丞九中九丮丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞下九中九丮上丘丞丵") ⟫ʷ
lem-CA-CKd10-Gad⟨t≡0-W≡⟨2-3⟩-d≡1-e≡1⟩ = derive (ℓ "丵丘丞九中九丮丘丞") (ℓ "丘丞下九中九丮上丘丞丵")
  (rw 0 q98 ∷
   rw 1 q68 ∷
   rw 0 q99 ∷
   rw 1 q100 ∷
   rw 2 q101 ∷
   rw 7 q102 ∷
   rw 8 q99 ∷
   rw 9 q100 ∷
   rw 10 q103 ∷ []) Eq.refl

private
  q104 : Eqn
  q104 = wE 2313 W
  q105 : Eqn
  q105 = wE 2314 W

-- pass [X1 CKd10 X1] [X2 X3 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 X2 X3]: 7 steps
lem-pass-X1-CKd10-X1-vs-X2-X3-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-X2-X3 : ⟪ (ℓ "丒丵丒丘丞下九中九丮上丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞下九中九丮上丘丞丒丵丒") ⟫ʷ
lem-pass-X1-CKd10-X1-vs-X2-X3-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-X2-X3 = derive (ℓ "丒丵丒丘丞下九中九丮上丘丞") (ℓ "丘丞下九中九丮上丘丞丒丵丒")
  (rw 0 q61 ∷
   rw 1 q62 ∷
   rw 2 q104 ∷
   rw 3 q64 ∷
   rw 7 q105 ∷
   rw 8 q61 ∷
   rw 9 q62 ∷ []) Eq.refl

private
  q106 : Eqn
  q106 = eqn (ℓ "丌丘") (ℓ "丘丌") (low₁-comm (X) ((X ↑)))
  q107 : Eqn
  q107 = sE 2402 lem-pass-X2-CKd23-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3

-- pass [CKd23] [X0 X2 X3 TOFF102 CS13 TOFF102 CSd13 X0 X2 X3]: 7 steps
lem-pass-CKd23-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : ⟪ (ℓ "乎丌丘丞习丽习举丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞习丽习举丌丘丞乎") ⟫ʷ
lem-pass-CKd23-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = derive (ℓ "乎丌丘丞习丽习举丌丘丞") (ℓ "丌丘丞习丽习举丌丘丞乎")
  (rw 1 q106 ∷
   rw 0 q18 ∷
   rw 11 q19 ∷
   rw 1 q107 ∷
   rw 9 q21 ∷
   rw⁻ 0 q106 ∷
   rw⁻ 8 q19 ∷ []) Eq.refl

private
  q108 : Eqn
  q108 = sE 2398 lem-pass-X2-CK23-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3

-- pass [CK23] [X0 X2 X3 TOFF102 CS13 TOFF102 CSd13 X0 X2 X3]: 7 steps
lem-pass-CK23-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : ⟪ (ℓ "乍丌丘丞习丽习举丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞习丽习举丌丘丞乍") ⟫ʷ
lem-pass-CK23-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = derive (ℓ "乍丌丘丞习丽习举丌丘丞") (ℓ "丌丘丞习丽习举丌丘丞乍")
  (rw 1 q106 ∷
   rw 0 q22 ∷
   rw 11 q19 ∷
   rw 1 q108 ∷
   rw 9 q24 ∷
   rw⁻ 0 q106 ∷
   rw⁻ 8 q19 ∷ []) Eq.refl

private
  q109 : Eqn
  q109 = wE 2154 W
  q110 : Eqn
  q110 = sE 2407 lem-pass-X3-CS32-X3-vs-X0-TOFF201-CS23-TOFF201-CSd23-X0
  q111 : Eqn
  q111 = wE 2155 W

-- pass [CS32] [X0 X3 TOFF201 CS23 TOFF201 CSd23 X0 X3]: 5 steps
lem-pass-CS32-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 : ⟪ (ℓ "义丌丞乣义乣乊丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞乣义乣乊丌丞义") ⟫ʷ
lem-pass-CS32-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 = derive (ℓ "义丌丞乣义乣乊丌丞") (ℓ "丌丞乣义乣乊丌丞义")
  (rw 1 q86 ∷
   rw 0 q109 ∷
   rw 1 q110 ∷
   rw 7 q111 ∷
   rw⁻ 0 q86 ∷ []) Eq.refl

private
  q112 : Eqn
  q112 = sE 2394 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3

-- Bar(SSKSKK;3,1->0) passes split Gad(t=2, W=(0, 3), d=KSSKd, e=1): 9 steps
lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡KSSKd-e≡1⟩ : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乗丞丞义丞丞义丞丞乘丞丌丞乣义乣乊丌丞丞乗丞丞乊丞丞乊丞丞乘丞") ⟫ʷ ≈ ⟪ (ℓ "丞乗丞丞义丞丞义丞丞乘丞丌丞乣义乣乊丌丞丞乗丞丞乊丞丞乊丞丞乘丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡KSSKd-e≡1⟩ = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乗丞丞义丞丞义丞丞乘丞丌丞乣义乣乊丌丞丞乗丞丞乊丞丞乊丞丞乘丞") (ℓ "丞乗丞丞义丞丞义丞丞乘丞丌丞乣义乣乊丌丞丞乗丞丞乊丞丞乊丞丞乘丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 0 q35 ∷
   rw 3 q36 ∷
   rw 6 q36 ∷
   rw 9 q37 ∷
   rw 12 q112 ∷
   rw 20 q35 ∷
   rw 23 q39 ∷
   rw 26 q39 ∷
   rw 29 q37 ∷ []) Eq.refl

private
  q113 : Eqn
  q113 = sE 2405 lem-pass-X3-CKd31-X3-vs-X0-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X0

-- pass [CKd31] [X0 X3 K2 S2 S2 Kd2 TOFF201 CS23 TOFF201 CSd23 K2 Sd2 Sd2 Kd2 X0 X3]: 5 steps
lem-pass-CKd31-vs-X0-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X0-X3 : ⟪ (ℓ "乕丌丞世且且丗乣义乣乊世丕丕丗丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞世且且丗乣义乣乊世丕丕丗丌丞乕") ⟫ʷ
lem-pass-CKd31-vs-X0-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X0-X3 = derive (ℓ "乕丌丞世且且丗乣义乣乊世丕丕丗丌丞") (ℓ "丌丞世且且丗乣义乣乊世丕丕丗丌丞乕")
  (rw 1 q86 ∷
   rw 0 q40 ∷
   rw 1 q113 ∷
   rw 15 q42 ∷
   rw⁻ 0 q86 ∷ []) Eq.refl

private
  q114 : Eqn
  q114 = sE 2391 lem-pass-CCZ123-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3

-- CCZ(3,2,1) passes split Gad(t=2, W=(0, 3), d=KSSKd, e=1): 9 steps
lem-CCZ⟨321⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡KSSKd-e≡1⟩ : ⟪ (ℓ "乜丞乗丞丞义丞丞义丞丞乘丞丌丞乣义乣乊丌丞丞乗丞丞乊丞丞乊丞丞乘丞") ⟫ʷ ≈ ⟪ (ℓ "丞乗丞丞义丞丞义丞丞乘丞丌丞乣义乣乊丌丞丞乗丞丞乊丞丞乊丞丞乘丞乜") ⟫ʷ
lem-CCZ⟨321⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡KSSKd-e≡1⟩ = derive (ℓ "乜丞乗丞丞义丞丞义丞丞乘丞丌丞乣义乣乊丌丞丞乗丞丞乊丞丞乊丞丞乘丞") (ℓ "丞乗丞丞义丞丞义丞丞乘丞丌丞乣义乣乊丌丞丞乗丞丞乊丞丞乊丞丞乘丞乜")
  (rw 0 q43 ∷
   rw 3 q44 ∷
   rw 6 q44 ∷
   rw 9 q45 ∷
   rw 12 q114 ∷
   rw 20 q43 ∷
   rw 23 q47 ∷
   rw 26 q47 ∷
   rw 29 q45 ∷ []) Eq.refl

private
  q115 : Eqn
  q115 = sE 2403 lem-pass-X3-CK31-X3-vs-X0-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X0

-- pass [CK31] [X0 X3 K2 S2 S2 Kd2 TOFF201 CS23 TOFF201 CSd23 K2 Sd2 Sd2 Kd2 X0 X3]: 5 steps
lem-pass-CK31-vs-X0-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X0-X3 : ⟪ (ℓ "乔丌丞世且且丗乣义乣乊世丕丕丗丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞世且且丗乣义乣乊世丕丕丗丌丞乔") ⟫ʷ
lem-pass-CK31-vs-X0-X3-K2-S2-S2-Kd2-TOFF201-CS23-TOFF201-CSd23-K2-Sd2-Sd2-Kd2-X0-X3 = derive (ℓ "乔丌丞世且且丗乣义乣乊世丕丕丗丌丞") (ℓ "丌丞世且且丗乣义乣乊世丕丕丗丌丞乔")
  (rw 1 q86 ∷
   rw 0 q48 ∷
   rw 1 q115 ∷
   rw 15 q50 ∷
   rw⁻ 0 q86 ∷ []) Eq.refl

private
  q116 : Eqn
  q116 = sE 2408 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3

-- Bar(SSSKSS;3,1->0) passes split Gad(t=2, W=(0, 3), d=KSSKd, e=1): 9 steps
lem-Bar⟨SSSKSS31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡KSSKd-e≡1⟩ : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乗丞丞义丞丞义丞丞乘丞丌丞乣义乣乊丌丞丞乗丞丞乊丞丞乊丞丞乘丞") ⟫ʷ ≈ ⟪ (ℓ "丞乗丞丞义丞丞义丞丞乘丞丌丞乣义乣乊丌丞丞乗丞丞乊丞丞乊丞丞乘丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-Bar⟨SSSKSS31-⟶0⟩-passes-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡KSSKd-e≡1⟩ = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乗丞丞义丞丞义丞丞乘丞丌丞乣义乣乊丌丞丞乗丞丞乊丞丞乊丞丞乘丞") (ℓ "丞乗丞丞义丞丞义丞丞乘丞丌丞乣义乣乊丌丞丞乗丞丞乊丞丞乊丞丞乘丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 0 q51 ∷
   rw 3 q52 ∷
   rw 6 q52 ∷
   rw 9 q53 ∷
   rw 12 q116 ∷
   rw 20 q51 ∷
   rw 23 q55 ∷
   rw 26 q55 ∷
   rw 29 q53 ∷ []) Eq.refl
