{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD743 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D743 (W : Ws) (Sᴰ : SD743) where

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
  lem-pass-CS12-vs-CS03 : St 21
  lem-pass-CS12-vs-CS03 = pickᴰ 0 Sᴰ
  lem-pass-S0-vs-CSd03 : St 818
  lem-pass-S0-vs-CSd03 = pickᴰ 1 Sᴰ
  lem-pass-Sd0-vs-CS03 : St 176
  lem-pass-Sd0-vs-CS03 = pickᴰ 2 Sᴰ
  lem-pass-Sd0-vs-CSd03 : St 825
  lem-pass-Sd0-vs-CSd03 = pickᴰ 3 Sᴰ
  lem-pass-CCZ012-vs-Sd0 : St 2446
  lem-pass-CCZ012-vs-Sd0 = pickᴰ 4 Sᴰ
  lem-pass-CS12-vs-Sd0 : St 2447
  lem-pass-CS12-vs-Sd0 = pickᴰ 5 Sᴰ
  lem-K0-PPw3-Kd0 : St 2448
  lem-K0-PPw3-Kd0 = pickᴰ 6 Sᴰ
  lem-cocycle-KdSK∣S : St 2449
  lem-cocycle-KdSK∣S = pickᴰ 7 Sᴰ
  lem-cocycle-KdSK∣SKdSK : St 2450
  lem-cocycle-KdSK∣SKdSK = pickᴰ 8 Sᴰ
  lem-cocycle-S∣KdSK : St 2451
  lem-cocycle-S∣KdSK = pickᴰ 9 Sᴰ
  lem-cocycle-S∣KdSKS : St 2452
  lem-cocycle-S∣KdSKS = pickᴰ 10 Sᴰ
  lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 38
  lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 11 Sᴰ
  lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 88
  lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 12 Sᴰ
  lem-ROT-form : St 2018
  lem-ROT-form = pickᴰ 13 Sᴰ
  lem-pass-CCZ012-vs-CS03 : St 822
  lem-pass-CCZ012-vs-CS03 = pickᴰ 14 Sᴰ
  lem-pass-CS12-vs-TOFF012-CS03-TOFF012 : St 2453
  lem-pass-CS12-vs-TOFF012-CS03-TOFF012 = pickᴰ 15 Sᴰ
  lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 841
  lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 16 Sᴰ
  lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 849
  lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 17 Sᴰ
  lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 850
  lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 18 Sᴰ
  lem-pass-X2-CS20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 852
  lem-pass-X2-CS20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 19 Sᴰ
  lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 853
  lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 20 Sᴰ
  lem-pass-X3-CKd31-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 1051
  lem-pass-X3-CKd31-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 21 Sᴰ
  lem-C⟨U'⟩≡eps : St 2454
  lem-C⟨U'⟩≡eps = pickᴰ 22 Sᴰ
  lem-pass-CCZ012-vs-TOFF012-CS03-TOFF012 : St 2455
  lem-pass-CCZ012-vs-TOFF012-CS03-TOFF012 = pickᴰ 23 Sᴰ
  lem-pass-CK30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2205
  lem-pass-CK30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 24 Sᴰ
  lem-pass-S0-vs-TOFF012-CS03-TOFF012 : St 2456
  lem-pass-S0-vs-TOFF012-CS03-TOFF012 = pickᴰ 25 Sᴰ
  lem-pass-X2-CK20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : St 2457
  lem-pass-X2-CK20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = pickᴰ 26 Sᴰ
  lem-pass-X2-CK21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 1135
  lem-pass-X2-CK21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 27 Sᴰ
  lem-pass-X2-CKd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : St 2458
  lem-pass-X2-CKd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = pickᴰ 28 Sᴰ
  lem-pass-X2-CKd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 1137
  lem-pass-X2-CKd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 29 Sᴰ
  lem-pass-X2-CS20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : St 2459
  lem-pass-X2-CS20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = pickᴰ 30 Sᴰ
  lem-pass-X2-CS21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 1140
  lem-pass-X2-CS21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 31 Sᴰ
  lem-pass-X2-CSd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : St 2460
  lem-pass-X2-CSd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = pickᴰ 32 Sᴰ
  lem-pass-X2-CSd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 1144
  lem-pass-X2-CSd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 33 Sᴰ
  lem-ROT≡cF : St 1425
  lem-ROT≡cF = pickᴰ 34 Sᴰ
  lem-pass-CKd30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2260
  lem-pass-CKd30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 35 Sᴰ
  lem-pass-CS20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 2219
  lem-pass-CS20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 36 Sᴰ
  lem-pass-CS21-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : St 2461
  lem-pass-CS21-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = pickᴰ 37 Sᴰ
  lem-pass-CSd20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 2462
  lem-pass-CSd20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 38 Sᴰ
  lem-pass-CKd32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 : St 2463
  lem-pass-CKd32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 = pickᴰ 39 Sᴰ
  lem-pass-CS20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 1765
  lem-pass-CS20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 40 Sᴰ
  lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 1926
  lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 41 Sᴰ
  lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 1930
  lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 42 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 2464
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 43 Sᴰ
  lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 2079
  lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 44 Sᴰ
  lem-pass-X3-CS31-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2048
  lem-pass-X3-CS31-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 45 Sᴰ
  lem-pass-X3-CSd31-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2060
  lem-pass-X3-CSd31-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 46 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2 : St 2230
  lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2 = pickᴰ 47 Sᴰ
  lem-pass-CS30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2231
  lem-pass-CS30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 48 Sᴰ
  lem-pass-X3-CK30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : St 2465
  lem-pass-X3-CK30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = pickᴰ 49 Sᴰ
  lem-pass-X3-CKd30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : St 2466
  lem-pass-X3-CKd30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = pickᴰ 50 Sᴰ
  lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : St 2467
  lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = pickᴰ 51 Sᴰ
  lem-pass-X3-CS30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : St 2468
  lem-pass-X3-CS30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = pickᴰ 52 Sᴰ
  lem-pass-X3-CSd30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : St 2469
  lem-pass-X3-CSd30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = pickᴰ 53 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-3 : St 2470
  lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-3 = pickᴰ 54 Sᴰ
  lem-pass-CK20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 2233
  lem-pass-CK20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 55 Sᴰ
  lem-pass-CSd30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2262
  lem-pass-CSd30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 56 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : St 2471
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = pickᴰ 57 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2472
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 58 Sᴰ
  lem-PP-flip : St 2473
  lem-PP-flip = pickᴰ 59 Sᴰ
  lem-PP2≡E : St 2474
  lem-PP2≡E = pickᴰ 60 Sᴰ
  lem-PPi2≡E : St 2475
  lem-PPi2≡E = pickᴰ 61 Sᴰ
  lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-TOFF013-CS02-TOFF013-CSd02 : St 2476
  lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-TOFF013-CS02-TOFF013-CSd02 = pickᴰ 62 Sᴰ
  lem-pass-X1-X3-TOFF102-CS13-TOFF102-CSd13-X1-X3-vs-TOFF013-CS02-TOFF013-CSd02 : St 2477
  lem-pass-X1-X3-TOFF102-CS13-TOFF102-CSd13-X1-X3-vs-TOFF013-CS02-TOFF013-CSd02 = pickᴰ 63 Sᴰ
  lem-pass-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3-vs-TOFF013-CS02-TOFF013-CSd02 : St 2478
  lem-pass-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3-vs-TOFF013-CS02-TOFF013-CSd02 = pickᴰ 64 Sᴰ
  lem-pass-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3-vs-TOFF013-CS02-TOFF013-CSd02 : St 2479
  lem-pass-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3-vs-TOFF013-CS02-TOFF013-CSd02 = pickᴰ 65 Sᴰ
  lem-CAw-KdSK-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩ : St 2480
  lem-CAw-KdSK-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩ = pickᴰ 66 Sᴰ
  lem-CAw-S-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩ : St 2481
  lem-CAw-S-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩ = pickᴰ 67 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩-2 : St 2482
  lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩-2 = pickᴰ 68 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3 : St 2483
  lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3 = pickᴰ 69 Sᴰ
  lem-ca-split-Gad⟨t≡1-W≡⟨2⟩-d≡SK-e≡1⟩-2 : St 2484
  lem-ca-split-Gad⟨t≡1-W≡⟨2⟩-d≡SK-e≡1⟩-2 = pickᴰ 70 Sᴰ
  lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡1⟩-3 : St 2485
  lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡1⟩-3 = pickᴰ 71 Sᴰ
  lem-pass-CCZ012-X3-K0-CS03-Kd0-X3-CCZ012-X3-K0-CSd03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 2486
  lem-pass-CCZ012-X3-K0-CS03-Kd0-X3-CCZ012-X3-K0-CSd03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 72 Sᴰ
  lem-pass-CK20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 2487
  lem-pass-CK20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 73 Sᴰ
  lem-pass-CK21-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : St 2488
  lem-pass-CK21-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = pickᴰ 74 Sᴰ
  lem-pass-CKd20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 2489
  lem-pass-CKd20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 75 Sᴰ
  lem-pass-CSd03-vs-TOFF012-CS03-TOFF012 : St 2490
  lem-pass-CSd03-vs-TOFF012-CS03-TOFF012 = pickᴰ 76 Sᴰ
  lem-pass-X1-CSd10-X1-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2491
  lem-pass-X1-CSd10-X1-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 77 Sᴰ
  lem-pass-X1-CSd10-X1-vs-S0-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-Sd0 : St 2492
  lem-pass-X1-CSd10-X1-vs-S0-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-Sd0 = pickᴰ 78 Sᴰ
  lem-pass-X2-CKd20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2493
  lem-pass-X2-CKd20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 79 Sᴰ
  lem-pass-X2-CKd21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : St 2494
  lem-pass-X2-CKd21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = pickᴰ 80 Sᴰ
  lem-pass-X2-CKd21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : St 2495
  lem-pass-X2-CKd21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = pickᴰ 81 Sᴰ
  lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 2496
  lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 82 Sᴰ
  lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : St 2497
  lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = pickᴰ 83 Sᴰ
  lem-pass-X2-CS21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : St 2498
  lem-pass-X2-CS21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = pickᴰ 84 Sᴰ
  lem-pass-X2-CS21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : St 2499
  lem-pass-X2-CS21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = pickᴰ 85 Sᴰ
  lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : St 2500
  lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = pickᴰ 86 Sᴰ
  lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 2501
  lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 87 Sᴰ
  lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2502
  lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 88 Sᴰ
  lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2503
  lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 89 Sᴰ
  lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 2504
  lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 90 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3 : St 2505
  lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3 = pickᴰ 91 Sᴰ
  lem-pass-CS32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 : St 2506
  lem-pass-CS32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 = pickᴰ 92 Sᴰ
  lem-pass-CSd32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 : St 2507
  lem-pass-CSd32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 = pickᴰ 93 Sᴰ
  lem-pass-X3-CS31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 : St 2508
  lem-pass-X3-CS31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 = pickᴰ 94 Sᴰ
  lem-pass-X3-CS32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0 : St 2509
  lem-pass-X3-CS32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0 = pickᴰ 95 Sᴰ
  lem-pass-X3-CSd32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0 : St 2510
  lem-pass-X3-CSd32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0 = pickᴰ 96 Sᴰ
  lem-pass-X3-TOFF201-CS23-TOFF201-CSd23-X3-vs-TOFF013-CS02-TOFF013-CSd02 : St 2511
  lem-pass-X3-TOFF201-CS23-TOFF201-CSd23-X3-vs-TOFF013-CS02-TOFF013-CSd02 = pickᴰ 97 Sᴰ
  lem-pass-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3-vs-TOFF013-CS02-TOFF013-CSd02 : St 2512
  lem-pass-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3-vs-TOFF013-CS02-TOFF013-CSd02 = pickᴰ 98 Sᴰ
  lem-pass-X3-CSd30-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0 : St 2513
  lem-pass-X3-CSd30-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0 = pickᴰ 99 Sᴰ
  lem-pass-X3-CKd30-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0 : St 2514
  lem-pass-X3-CKd30-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0 = pickᴰ 100 Sᴰ

private
  q1 : Eqn
  q1 = sE 1425 lem-ROT≡cF
  q2 : Eqn
  q2 = sE 2018 lem-ROT-form
  q3 : Eqn
  q3 = wE 1339 W
  q4 : Eqn
  q4 = wE 2402 W
  q5 : Eqn
  q5 = wE 2403 W
  q6 : Eqn
  q6 = sE 2475 lem-PPi2≡E
  q7 : Eqn
  q7 = eqn (ℓ "下乜") (ℓ "乜下") (low₁-comm ((K • iI)) (CCZ))
  q8 : Eqn
  q8 = eqn (ℓ "三乜") (ℓ "乜三") (low₁-comm ((S • S • S)) (CCZ))
  q9 : Eqn
  q9 = eqn (ℓ "上乜") (ℓ "乜上") (low₁-comm (K) (CCZ))
  q10 : Eqn
  q10 = wE 2404 W
  q11 : Eqn
  q11 = wE 2405 W
  q12 : Eqn
  q12 = wE 1880 W
  q13 : Eqn
  q13 = wE 1846 W

-- ROT2=E: 17 steps
lem-ROT2≡E : ⟪ (ℓ "临乙习丿习乙丿与临乙习丿习乙丿临乙习丿习乙丿与临乙习丿习乙丿") ⟫ʷ ≈ ⟪ (ℓ "乜") ⟫ʷ
lem-ROT2≡E = derive (ℓ "临乙习丿习乙丿与临乙习丿习乙丿临乙习丿习乙丿与临乙习丿习乙丿") (ℓ "乜")
  (rw 0 q1 ∷
   rw 4 q1 ∷
   rw 0 q2 ∷
   rw 18 q2 ∷
   rw 17 q3 ∷
   rw 14 q4 ∷
   rw 11 q5 ∷
   rw 7 q6 ∷
   rw⁻ 7 q7 ∷
   rw⁻ 8 q8 ∷
   rw⁻ 9 q9 ∷
   rw 4 q10 ∷
   rw 3 q11 ∷
   rw 2 q12 ∷
   rw 1 q11 ∷
   rw 0 q9 ∷
   rw 1 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = sE 2474 lem-PP2≡E
  q15 : Eqn
  q15 = wE 33 W

-- PP4: 3 steps
lem-PP4 : ⟪ (ℓ "九中九丮九中九丮九中九丮九中九丮") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-PP4 = derive (ℓ "九中九丮九中九丮九中九丮九中九丮") []
  (rw 0 q14 ∷
   rw 1 q14 ∷
   rw 0 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = sE 2476 lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-TOFF013-CS02-TOFF013-CSd02

-- pass [TOFF013 CS02 TOFF013 CSd02] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 1 steps
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (ℓ "乞丧乞丨丞习丽习举丞") ⟫ʷ ≈ ⟪ (ℓ "丞习丽习举丞乞丧乞丨") ⟫ʷ
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (ℓ "乞丧乞丨丞习丽习举丞") (ℓ "丞习丽习举丞乞丧乞丨")
  (rw⁻ 0 q16 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = sE 2477 lem-pass-X1-X3-TOFF102-CS13-TOFF102-CSd13-X1-X3-vs-TOFF013-CS02-TOFF013-CSd02

-- pass [TOFF013 CS02 TOFF013 CSd02] [X1 X3 TOFF102 CS13 TOFF102 CSd13 X1 X3]: 1 steps
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X3-TOFF102-CS13-TOFF102-CSd13-X1-X3 : ⟪ (ℓ "乞丧乞丨丒丞习丽习举丒丞") ⟫ʷ ≈ ⟪ (ℓ "丒丞习丽习举丒丞乞丧乞丨") ⟫ʷ
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X3-TOFF102-CS13-TOFF102-CSd13-X1-X3 = derive (ℓ "乞丧乞丨丒丞习丽习举丒丞") (ℓ "丒丞习丽习举丒丞乞丧乞丨")
  (rw⁻ 0 q17 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = sE 2478 lem-pass-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3-vs-TOFF013-CS02-TOFF013-CSd02

-- pass [TOFF013 CS02 TOFF013 CSd02] [X0 X3 TOFF102 CS13 TOFF102 CSd13 X0 X3]: 1 steps
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : ⟪ (ℓ "乞丧乞丨丌丞习丽习举丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞习丽习举丌丞乞丧乞丨") ⟫ʷ
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = derive (ℓ "乞丧乞丨丌丞习丽习举丌丞") (ℓ "丌丞习丽习举丌丞乞丧乞丨")
  (rw⁻ 0 q18 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = sE 2479 lem-pass-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3-vs-TOFF013-CS02-TOFF013-CSd02

-- pass [TOFF013 CS02 TOFF013 CSd02] [X0 X1 X3 TOFF102 CS13 TOFF102 CSd13 X0 X1 X3]: 1 steps
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3 : ⟪ (ℓ "乞丧乞丨丌丒丞习丽习举丌丒丞") ⟫ʷ ≈ ⟪ (ℓ "丌丒丞习丽习举丌丒丞乞丧乞丨") ⟫ʷ
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3 = derive (ℓ "乞丧乞丨丌丒丞习丽习举丌丒丞") (ℓ "丌丒丞习丽习举丌丒丞乞丧乞丨")
  (rw⁻ 0 q19 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = eqn (ℓ "九丞") (ℓ "丞九") (low₃-comm (Toff) (X))
  q21 : Eqn
  q21 = wE 1 W
  q22 : Eqn
  q22 = wE 3 W
  q23 : Eqn
  q23 = wE 173 W
  q24 : Eqn
  q24 = wE 1962 W
  q25 : Eqn
  q25 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q26 : Eqn
  q26 = wE 175 W
  q27 : Eqn
  q27 = wE 2406 W
  q28 : Eqn
  q28 = eqn (ℓ "三乏") (ℓ "乏三") (low₁-comm ((S • S • S)) ((Swap ↑)))
  q29 : Eqn
  q29 = wE 45 W
  q30 : Eqn
  q30 = wE 2407 W
  q31 : Eqn
  q31 = sE 2490 lem-pass-CSd03-vs-TOFF012-CS03-TOFF012
  q32 : Eqn
  q32 = sE 2456 lem-pass-S0-vs-TOFF012-CS03-TOFF012
  q33 : Eqn
  q33 = sE 2453 lem-pass-CS12-vs-TOFF012-CS03-TOFF012
  q34 : Eqn
  q34 = sE 2455 lem-pass-CCZ012-vs-TOFF012-CS03-TOFF012
  q35 : Eqn
  q35 = wE 227 W
  q36 : Eqn
  q36 = wE 1342 W
  q37 : Eqn
  q37 = sE 818 lem-pass-S0-vs-CSd03
  q38 : Eqn
  q38 = sE 822 lem-pass-CCZ012-vs-CS03
  q39 : Eqn
  q39 = sE 2446 lem-pass-CCZ012-vs-Sd0
  q40 : Eqn
  q40 = sE 21 lem-pass-CS12-vs-CS03
  q41 : Eqn
  q41 = sE 2447 lem-pass-CS12-vs-Sd0
  q42 : Eqn
  q42 = sE 176 lem-pass-Sd0-vs-CS03
  q43 : Eqn
  q43 = sE 825 lem-pass-Sd0-vs-CSd03
  q44 : Eqn
  q44 = wE 1728 W
  q45 : Eqn
  q45 = wE 1358 W

-- merge3: 52 steps
lem-merge3 : ⟪ (ℓ "九中九丮丞九中九丮丞") ⟫ʷ ≈ ⟪ (ℓ "丶乙") ⟫ʷ
lem-merge3 = derive (ℓ "九中九丮丞九中九丮丞") (ℓ "丶乙")
  (rw⁻ 4 q20 ∷
   rw 7 q21 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q22 ∷
   rw 5 q23 ∷
   rw 6 q24 ∷
   rw⁻ 5 q25 ∷
   rw 8 q21 ∷
   re 6 3 (ℓ "丮") ∷
   rw 7 q26 ∷
   rw 8 q22 ∷
   rw⁻ 7 q20 ∷
   rw 11 q21 ∷
   rw 10 q23 ∷
   re 9 1 (ℓ "乏丨乏") ∷
   rw 11 q22 ∷
   rw 8 q23 ∷
   rw 9 q27 ∷
   rw 10 q21 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q28 ∷
   rw 10 q22 ∷
   rw 6 q29 ∷
   rw 4 q30 ∷
   rw⁻ 0 q31 ∷
   rw⁻ 1 q32 ∷
   rw⁻ 2 q33 ∷
   rw⁻ 3 q34 ∷
   rw 6 q35 ∷
   rw 7 q21 ∷
   re 6 1 (ℓ "乏丨乏") ∷
   rw 8 q22 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q22 ∷
   rw 6 q36 ∷
   rw 5 q22 ∷
   rw 4 q35 ∷
   rw⁻ 0 q37 ∷
   rw 3 q38 ∷
   rw 4 q39 ∷
   rw 2 q40 ∷
   rw 3 q41 ∷
   rw⁻ 2 q42 ∷
   rw⁻ 1 q43 ∷
   rw 0 q44 ∷
   rw 2 q21 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q22 ∷
   re 0 1 (ℓ "乏丨乏") ∷
   rw 2 q22 ∷
   rw 1 q45 ∷
   rw 0 q22 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = wE 54 W
  q47 : Eqn
  q47 = sE 2448 lem-K0-PPw3-Kd0
  q48 : Eqn
  q48 = sE 2486 lem-pass-CCZ012-X3-K0-CS03-Kd0-X3-CCZ012-X3-K0-CSd03-Kd0-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q49 : Eqn
  q49 = sE 2448 lem-K0-PPw3-Kd0

-- pass [X3 TOFF012 CS03 TOFF012 CSd03 X3] [Kd0 TOFF012 CS03 TOFF012 CSd03 K0]: 5 steps
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 : ⟪ (ℓ "丞九中九丮丞下九中九丮上") ⟫ʷ ≈ ⟪ (ℓ "下九中九丮上丞九中九丮丞") ⟫ʷ
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 = derive (ℓ "丞九中九丮丞下九中九丮上") (ℓ "下九中九丮上丞九中九丮丞")
  (rw 0 q46 ∷
   rw 1 q47 ∷
   rw 1 q48 ∷
   rw⁻ 5 q49 ∷
   rw 12 q3 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = sE 2452 lem-cocycle-S∣KdSKS
  q51 : Eqn
  q51 = sE 2449 lem-cocycle-KdSK∣S
  q52 : Eqn
  q52 = sE 2454 lem-C⟨U'⟩≡eps
  q53 : Eqn
  q53 = sE 2480 lem-CAw-KdSK-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩
  q54 : Eqn
  q54 = sE 2481 lem-CAw-S-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩

-- C(SU'S): 5 steps
lem-C⟨SU'S⟩ : ⟪ (ℓ "九中乒中乑中九丮乒丮乑丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮下三九中九丮丈上") ⟫ʷ
lem-C⟨SU'S⟩ = derive (ℓ "九中乒中乑中九丮乒丮乑丮") (ℓ "九中九丮下三九中九丮丈上")
  (rw 0 q50 ∷
   rw 5 q51 ∷
   rw 5 q52 ∷
   rw 5 q53 ∷
   rw 4 q54 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = sE 2450 lem-cocycle-KdSK∣SKdSK
  q56 : Eqn
  q56 = sE 2451 lem-cocycle-S∣KdSK

-- C(U'SU'): 12 steps
lem-C⟨U'SU'⟩ : ⟪ (ℓ "九乒中乑中乒中乑九乒丮乑丮乒丮乑") ⟫ʷ ≈ ⟪ (ℓ "三下三九中九丮丈上丈") ⟫ʷ
lem-C⟨U'SU'⟩ = derive (ℓ "九乒中乑中乒中乑九乒丮乑丮乒丮乑") (ℓ "三下三九中九丮丈上丈")
  (rw 0 q55 ∷
   rw 0 q52 ∷
   rw 3 q56 ∷
   rw 8 q52 ∷
   rw 9 q21 ∷
   re 8 1 (ℓ "乏丨乏") ∷
   rw 10 q22 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q22 ∷
   rw 8 q36 ∷
   rw 7 q22 ∷
   rw 0 q53 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = wE 1357 W
  q58 : Eqn
  q58 = wE 231 W
  q59 : Eqn
  q59 = sE 2473 lem-PP-flip
  q60 : Eqn
  q60 = wE 387 W

-- PP-flip ^-1: 35 steps
lem-PP-flip-ᵖ-1 : ⟪ (ℓ "丌中九丮九丌") ⟫ʷ ≈ ⟪ (ℓ "九中九丮") ⟫ʷ
lem-PP-flip-ᵖ-1 = derive (ℓ "丌中九丮九丌") (ℓ "九中九丮")
  (rw 6 q21 ∷
   rw 7 q57 ∷
   rw 8 q21 ∷
   re 6 3 (ℓ "中") ∷
   rw 9 q21 ∷
   re 7 3 (ℓ "丮") ∷
   rw 8 q22 ∷
   rw 7 q29 ∷
   rw 8 q21 ∷
   rw 9 q58 ∷
   rw 10 q21 ∷
   re 8 3 (ℓ "丮") ∷
   rw 11 q21 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q22 ∷
   rw 9 q29 ∷
   rw⁻ 6 q59 ∷
   rw 5 q60 ∷
   rw 4 q35 ∷
   rw 5 q21 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q22 ∷
   re 3 1 (ℓ "乏丨乏") ∷
   rw 5 q22 ∷
   rw 4 q45 ∷
   rw 3 q22 ∷
   rw 2 q35 ∷
   rw 3 q21 ∷
   re 2 1 (ℓ "乏丨乏") ∷
   rw 4 q22 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q22 ∷
   rw 2 q36 ∷
   rw 1 q22 ∷
   rw 0 q60 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = wE 5 W
  q62 : Eqn
  q62 = wE 217 W
  q63 : Eqn
  q63 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q64 : Eqn
  q64 = wE 9 W
  q65 : Eqn
  q65 = wE 127 W
  q66 : Eqn
  q66 = wE 271 W
  q67 : Eqn
  q67 = wE 7 W
  q68 : Eqn
  q68 = wE 8 W
  q69 : Eqn
  q69 = wE 10 W
  q70 : Eqn
  q70 = wE 272 W
  q71 : Eqn
  q71 = sE 2473 lem-PP-flip
  q72 : Eqn
  q72 = wE 25 W
  q73 : Eqn
  q73 = wE 123 W
  q74 : Eqn
  q74 = wE 27 W
  q75 : Eqn
  q75 = wE 28 W
  q76 : Eqn
  q76 = wE 29 W
  q77 : Eqn
  q77 = wE 124 W
  q78 : Eqn
  q78 = wE 274 W
  q79 : Eqn
  q79 = wE 322 W
  q80 : Eqn
  q80 = wE 31 W

-- PP-flip @1023: 69 steps
lem-PP-flip-at1023 : ⟪ (ℓ "丒习丽习举丒") ⟫ʷ ≈ ⟪ (ℓ "丽习举习") ⟫ʷ
lem-PP-flip-at1023 = derive (ℓ "丒习丽习举丒") (ℓ "丽习举习")
  (rw 6 q61 ∷
   rw 5 q62 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw⁻ 6 q63 ∷
   rw 5 q64 ∷
   rw⁻ 4 q63 ∷
   re 5 3 (ℓ "丮") ∷
   re 3 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 10 q65 ∷
   rw 9 q66 ∷
   rw 8 q67 ∷
   rw 7 q68 ∷
   rw 6 q64 ∷
   rw 5 q68 ∷
   rw 4 q69 ∷
   rw 3 q66 ∷
   rw 4 q70 ∷
   re 4 8 (ℓ "九") ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw⁻ 4 q63 ∷
   rw 3 q69 ∷
   rw⁻ 2 q63 ∷
   re 3 3 (ℓ "中") ∷
   re 1 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 8 q65 ∷
   rw 7 q66 ∷
   rw 6 q67 ∷
   rw 5 q68 ∷
   rw 4 q64 ∷
   rw 3 q68 ∷
   rw 2 q69 ∷
   rw 1 q66 ∷
   rw 2 q70 ∷
   re 2 8 (ℓ "九") ∷
   rw 0 q62 ∷
   rw 1 q71 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 0 q63 ∷
   rw 1 q72 ∷
   rw 2 q63 ∷
   re 0 3 (ℓ "丽") ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 1 q73 ∷
   rw 2 q74 ∷
   rw 3 q75 ∷
   rw 4 q76 ∷
   rw 5 q75 ∷
   rw 6 q72 ∷
   rw 7 q73 ∷
   rw 8 q77 ∷
   rw 1 q78 ∷
   re 1 8 (ℓ "习") ∷
   re 3 1 (ℓ "乏丨乏") ∷
   rw 2 q63 ∷
   rw 3 q79 ∷
   rw 4 q63 ∷
   re 2 3 (ℓ "举") ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 3 q73 ∷
   rw 4 q74 ∷
   rw 5 q75 ∷
   rw 6 q76 ∷
   rw 7 q75 ∷
   rw 8 q72 ∷
   rw 9 q73 ∷
   rw 10 q77 ∷
   rw 3 q78 ∷
   re 3 8 (ℓ "习") ∷
   rw 4 q80 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = sE 2474 lem-PP2≡E

-- E PPi: 17 steps
lem-E-PPi : ⟪ (ℓ "乜中九丮九") ⟫ʷ ≈ ⟪ (ℓ "九中九丮") ⟫ʷ
lem-E-PPi = derive (ℓ "乜中九丮九") (ℓ "九中九丮")
  (rw⁻ 0 q81 ∷
   rw 9 q21 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q22 ∷
   re 7 1 (ℓ "乏丨乏") ∷
   rw 9 q22 ∷
   rw 8 q45 ∷
   rw 7 q22 ∷
   rw 6 q35 ∷
   rw 7 q21 ∷
   re 6 1 (ℓ "乏丨乏") ∷
   rw 8 q22 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q22 ∷
   rw 6 q36 ∷
   rw 5 q22 ∷
   rw 4 q35 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = sE 2483 lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3
  q83 : Eqn
  q83 = sE 2469 lem-pass-X3-CSd30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2
  q84 : Eqn
  q84 = sE 2466 lem-pass-X3-CKd30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2
  q85 : Eqn
  q85 = sE 2467 lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2
  q86 : Eqn
  q86 = sE 2465 lem-pass-X3-CK30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2
  q87 : Eqn
  q87 = sE 2468 lem-pass-X3-CS30-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2
  q88 : Eqn
  q88 = sE 2483 lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩-3

-- pass [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3] [X2 TOFF102 CS13 TOFF102 CSd13 X2]: 7 steps
lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : ⟪ (ℓ "丞丈上中九丮九下三丞丘习丽习举丘") ⟫ʷ ≈ ⟪ (ℓ "丘习丽习举丘丞丈上中九丮九下三丞") ⟫ʷ
lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = derive (ℓ "丞丈上中九丮九下三丞丘习丽习举丘") (ℓ "丘习丽习举丘丞丈上中九丮九下三丞")
  (rw 0 q82 ∷
   rw 15 q83 ∷
   rw 12 q84 ∷
   rw 6 q85 ∷
   rw 3 q86 ∷
   rw 0 q87 ∷
   rw⁻ 6 q88 ∷ []) Eq.refl

private
  q89 : Eqn
  q89 = wE 225 W
  q90 : Eqn
  q90 = sE 2504 lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q91 : Eqn
  q91 = wE 390 W

-- pass [X3 CS03 TOFF012 CSd03 TOFF012 X3] [TOFF102 CS13 TOFF102 CSd13]: 37 steps
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丞中九丮九丞习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丞中九丮九丞") ⟫ʷ
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丞中九丮九丞习丽习举") (ℓ "习丽习举丞中九丮九丞")
  (rw 10 q89 ∷
   rw 11 q29 ∷
   rw 12 q21 ∷
   rw 13 q57 ∷
   rw 14 q21 ∷
   re 12 3 (ℓ "中") ∷
   rw 15 q21 ∷
   re 13 3 (ℓ "丮") ∷
   rw 14 q22 ∷
   rw 13 q29 ∷
   rw 14 q21 ∷
   rw 15 q58 ∷
   rw 16 q21 ∷
   re 14 3 (ℓ "丮") ∷
   rw 17 q21 ∷
   re 15 3 (ℓ "中") ∷
   rw 16 q22 ∷
   rw 15 q89 ∷
   rw⁻ 6 q90 ∷
   rw 5 q91 ∷
   rw 4 q35 ∷
   rw 5 q21 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q22 ∷
   re 3 1 (ℓ "乏丨乏") ∷
   rw 5 q22 ∷
   rw 4 q45 ∷
   rw 3 q22 ∷
   rw 2 q35 ∷
   rw 3 q21 ∷
   re 2 1 (ℓ "乏丨乏") ∷
   rw 4 q22 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q22 ∷
   rw 2 q36 ∷
   rw 1 q22 ∷
   rw 0 q91 ∷ []) Eq.refl

private
  q92 : Eqn
  q92 = sE 1930 lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q93 : Eqn
  q93 = sE 841 lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q94 : Eqn
  q94 = sE 2079 lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q95 : Eqn
  q95 = sE 38 lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q96 : Eqn
  q96 = sE 1926 lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3] [TOFF012 CS03 TOFF012 CSd03]: 7 steps
lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (ℓ "丞丈上中九丮九下三丞九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮丞丈上中九丮九下三丞") ⟫ʷ
lem-pass-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (ℓ "丞丈上中九丮九下三丞九中九丮") (ℓ "九中九丮丞丈上中九丮九下三丞")
  (rw 0 q82 ∷
   rw 15 q92 ∷
   rw 12 q93 ∷
   rw 6 q94 ∷
   rw 3 q95 ∷
   rw 0 q96 ∷
   rw⁻ 4 q88 ∷ []) Eq.refl

-- c -> ci E: 17 steps
lem-c--⟶-ci-E : ⟪ (ℓ "九中九丮") ⟫ʷ ≈ ⟪ (ℓ "中九丮九乜") ⟫ʷ
lem-c--⟶-ci-E = derive (ℓ "九中九丮") (ℓ "中九丮九乜")
  (rw 0 q21 ∷
   rw 1 q57 ∷
   rw 2 q21 ∷
   re 0 3 (ℓ "中") ∷
   rw 3 q21 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q22 ∷
   rw 1 q29 ∷
   rw 2 q21 ∷
   rw 3 q58 ∷
   rw 4 q21 ∷
   re 2 3 (ℓ "丮") ∷
   rw 5 q21 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q22 ∷
   rw 3 q29 ∷
   rw 4 q14 ∷ []) Eq.refl

private
  q97 : Eqn
  q97 = sE 2470 lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-3
  q98 : Eqn
  q98 = sE 2231 lem-pass-CS30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q99 : Eqn
  q99 = sE 2205 lem-pass-CK30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q100 : Eqn
  q100 = sE 2503 lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q101 : Eqn
  q101 = sE 2260 lem-pass-CKd30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q102 : Eqn
  q102 = sE 2262 lem-pass-CSd30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q103 : Eqn
  q103 = sE 2470 lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-3

-- pass [X3 CS03 TOFF012 CSd03 TOFF012 X3] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 7 steps
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (ℓ "丞中九丮九丞丈上中九丮九下三") ⟫ʷ ≈ ⟪ (ℓ "丈上中九丮九下三丞中九丮九丞") ⟫ʷ
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (ℓ "丞中九丮九丞丈上中九丮九下三") (ℓ "丈上中九丮九下三丞中九丮九丞")
  (rw 6 q97 ∷
   rw⁻ 0 q98 ∷
   rw⁻ 1 q99 ∷
   rw 2 q100 ∷
   rw⁻ 6 q101 ∷
   rw⁻ 7 q102 ∷
   rw⁻ 0 q103 ∷ []) Eq.refl

private
  q104 : Eqn
  q104 = sE 2230 lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2
  q105 : Eqn
  q105 = sE 2219 lem-pass-CS20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q106 : Eqn
  q106 = sE 2233 lem-pass-CK20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q107 : Eqn
  q107 = sE 2496 lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q108 : Eqn
  q108 = sE 2489 lem-pass-CKd20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q109 : Eqn
  q109 = sE 2462 lem-pass-CSd20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q110 : Eqn
  q110 = sE 2230 lem-ca-split-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-2

-- pass [X2 CS03 TOFF012 CSd03 TOFF012 X2] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 7 steps
lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (ℓ "丘中九丮九丘丈上中九丮九下三") ⟫ʷ ≈ ⟪ (ℓ "丈上中九丮九下三丘中九丮九丘") ⟫ʷ
lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (ℓ "丘中九丮九丘丈上中九丮九下三") (ℓ "丈上中九丮九下三丘中九丮九丘")
  (rw 6 q104 ∷
   rw⁻ 0 q105 ∷
   rw⁻ 1 q106 ∷
   rw 2 q107 ∷
   rw⁻ 6 q108 ∷
   rw⁻ 7 q109 ∷
   rw⁻ 0 q110 ∷ []) Eq.refl

private
  q111 : Eqn
  q111 = sE 2482 lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩-2
  q112 : Eqn
  q112 = sE 2460 lem-pass-X2-CSd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1
  q113 : Eqn
  q113 = sE 2458 lem-pass-X2-CKd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1
  q114 : Eqn
  q114 = sE 2497 lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1
  q115 : Eqn
  q115 = sE 2457 lem-pass-X2-CK20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1
  q116 : Eqn
  q116 = sE 2459 lem-pass-X2-CS20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1
  q117 : Eqn
  q117 = sE 2482 lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩-2

-- pass [X2 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 7 steps
lem-pass-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (ℓ "丘丈上中九丮九下三丘与丐习丽习举丑丏") ⟫ʷ ≈ ⟪ (ℓ "与丐习丽习举丑丏丘丈上中九丮九下三丘") ⟫ʷ
lem-pass-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (ℓ "丘丈上中九丮九下三丘与丐习丽习举丑丏") (ℓ "与丐习丽习举丑丏丘丈上中九丮九下三丘")
  (rw 0 q111 ∷
   rw 15 q112 ∷
   rw 12 q113 ∷
   rw 6 q114 ∷
   rw 3 q115 ∷
   rw 0 q116 ∷
   rw⁻ 8 q117 ∷ []) Eq.refl

private
  q118 : Eqn
  q118 = eqn (ℓ "丈丞") (ℓ "丞丈") (low₁-comm (S) ((X ↑ ↑)))
  q119 : Eqn
  q119 = eqn (ℓ "丈丘") (ℓ "丘丈") (low₁-comm (S) ((X ↑)))
  q120 : Eqn
  q120 = eqn (ℓ "上丞") (ℓ "丞上") (low₁-comm (K) ((X ↑ ↑)))
  q121 : Eqn
  q121 = eqn (ℓ "上丘") (ℓ "丘上") (low₁-comm (K) ((X ↑)))
  q122 : Eqn
  q122 = eqn (ℓ "三丘") (ℓ "丘三") (low₁-comm ((S • S • S)) ((X ↑)))
  q123 : Eqn
  q123 = eqn (ℓ "下丘") (ℓ "丘下") (low₁-comm ((K • iI)) ((X ↑)))
  q124 : Eqn
  q124 = eqn (ℓ "三丞") (ℓ "丞三") (low₁-comm ((S • S • S)) ((X ↑ ↑)))
  q125 : Eqn
  q125 = eqn (ℓ "下丞") (ℓ "丞下") (low₁-comm ((K • iI)) ((X ↑ ↑)))
  q126 : Eqn
  q126 = wE 2222 W
  q127 : Eqn
  q127 = wE 2223 W
  q128 : Eqn
  q128 = sE 2487 lem-pass-CK20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q129 : Eqn
  q129 = sE 1765 lem-pass-CS20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q130 : Eqn
  q130 = wE 2224 W

-- ca-split Gad(t=0, W=(2, 3), d=SK, e=-1) 2: 13 steps
lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2 : ⟪ (ℓ "丘丞丈上中九丮九下三丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丧丘丘乄丘丘丞中九丮九丘丞丘久丘丘丨丘") ⟫ʷ
lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SK-e≡-1⟩-2 = derive (ℓ "丘丞丈上中九丮九下三丘丞") (ℓ "丘丧丘丘乄丘丘丞中九丮九丘丞丘久丘丘丨丘")
  (rw⁻ 1 q118 ∷
   rw⁻ 0 q119 ∷
   rw⁻ 2 q120 ∷
   rw⁻ 1 q121 ∷
   rw 9 q122 ∷
   rw 8 q123 ∷
   rw 10 q124 ∷
   rw 9 q125 ∷
   rw 0 q126 ∷
   rw 16 q127 ∷
   rw 7 q128 ∷
   rw 6 q129 ∷
   rw 14 q130 ∷ []) Eq.refl

private
  q131 : Eqn
  q131 = wE 1464 W
  q132 : Eqn
  q132 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q133 : Eqn
  q133 = sE 2493 lem-pass-X2-CKd20-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q134 : Eqn
  q134 = wE 1465 W

-- pass [CKd20] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 5 steps
lem-pass-CKd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (ℓ "久丘丞中九丮九丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞中九丮九丘丞久") ⟫ʷ
lem-pass-CKd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (ℓ "久丘丞中九丮九丘丞") (ℓ "丘丞中九丮九丘丞久")
  (rw 0 q131 ∷
   rw 9 q132 ∷
   rw 1 q133 ∷
   rw 7 q134 ∷
   rw⁻ 6 q132 ∷ []) Eq.refl

private
  q135 : Eqn
  q135 = sE 2484 lem-ca-split-Gad⟨t≡1-W≡⟨2⟩-d≡SK-e≡1⟩-2
  q136 : Eqn
  q136 = sE 1144 lem-pass-X2-CSd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q137 : Eqn
  q137 = sE 1137 lem-pass-X2-CKd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q138 : Eqn
  q138 = sE 2500 lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q139 : Eqn
  q139 = sE 1135 lem-pass-X2-CK21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q140 : Eqn
  q140 = sE 1140 lem-pass-X2-CS21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q141 : Eqn
  q141 = sE 2484 lem-ca-split-Gad⟨t≡1-W≡⟨2⟩-d≡SK-e≡1⟩-2

-- pass [X2 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 7 steps
lem-pass-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (ℓ "丘与丐习丽习举丑丏丘丈上中九丮九下三") ⟫ʷ ≈ ⟪ (ℓ "丈上中九丮九下三丘与丐习丽习举丑丏丘") ⟫ʷ
lem-pass-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (ℓ "丘与丐习丽习举丑丏丘丈上中九丮九下三") (ℓ "丈上中九丮九下三丘与丐习丽习举丑丏丘")
  (rw 0 q135 ∷
   rw 15 q136 ∷
   rw 12 q137 ∷
   rw 6 q138 ∷
   rw 3 q139 ∷
   rw 0 q140 ∷
   rw⁻ 8 q141 ∷ []) Eq.refl

private
  q142 : Eqn
  q142 = eqn (ℓ "与丞") (ℓ "丞与") (low-comm ((S ↑)) ((X ↑)))
  q143 : Eqn
  q143 = eqn (ℓ "与丘") (ℓ "丘与") (low-comm ((S ↑)) (X))
  q144 : Eqn
  q144 = eqn (ℓ "丐丞") (ℓ "丞丐") (low-comm ((K ↑)) ((X ↑)))
  q145 : Eqn
  q145 = eqn (ℓ "丐丘") (ℓ "丘丐") (low-comm ((K ↑)) (X))
  q146 : Eqn
  q146 = eqn (ℓ "丏丘") (ℓ "丘丏") (low-comm (((S • S • S) ↑)) (X))
  q147 : Eqn
  q147 = eqn (ℓ "丑丘") (ℓ "丘丑") (low-comm (((K • iI) ↑)) (X))
  q148 : Eqn
  q148 = eqn (ℓ "丏丞") (ℓ "丞丏") (low-comm (((S • S • S) ↑)) ((X ↑)))
  q149 : Eqn
  q149 = eqn (ℓ "丑丞") (ℓ "丞丑") (low-comm (((K • iI) ↑)) ((X ↑)))
  q150 : Eqn
  q150 = wE 2228 W
  q151 : Eqn
  q151 = wE 2229 W
  q152 : Eqn
  q152 = sE 2488 lem-pass-CK21-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3
  q153 : Eqn
  q153 = sE 2461 lem-pass-CS21-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3
  q154 : Eqn
  q154 = wE 2230 W

-- ca-split Gad(t=1, W=(2, 3), d=SK, e=1) 2: 13 steps
lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡1⟩-2 : ⟪ (ℓ "丘丞与丐习丽习举丑丏丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丶丘丘乇丘丘丞习丽习举丘丞丘么丘丘丷丘") ⟫ʷ
lem-ca-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡1⟩-2 = derive (ℓ "丘丞与丐习丽习举丑丏丘丞") (ℓ "丘丶丘丘乇丘丘丞习丽习举丘丞丘么丘丘丷丘")
  (rw⁻ 1 q142 ∷
   rw⁻ 0 q143 ∷
   rw⁻ 2 q144 ∷
   rw⁻ 1 q145 ∷
   rw 9 q146 ∷
   rw 8 q147 ∷
   rw 10 q148 ∷
   rw 9 q149 ∷
   rw 0 q150 ∷
   rw 16 q151 ∷
   rw 7 q152 ∷
   rw 6 q153 ∷
   rw 14 q154 ∷ []) Eq.refl

private
  q155 : Eqn
  q155 = wE 1819 W
  q156 : Eqn
  q156 = sE 2491 lem-pass-X1-CSd10-X1-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0
  q157 : Eqn
  q157 = wE 2408 W
  q158 : Eqn
  q158 = wE 2409 W
  q159 : Eqn
  q159 = wE 1820 W

-- CA CS10 Gad(t=0, W=(), d=SK, e=-1): 5 steps
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "丠丈上中九丮九下三") ⟫ʷ ≈ ⟪ (ℓ "丈丈上中九丮九下三三丠") ⟫ʷ
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ = derive (ℓ "丠丈上中九丮九下三") (ℓ "丈丈上中九丮九下三三丠")
  (rw 0 q155 ∷
   rw 1 q156 ∷
   rw 0 q157 ∷
   rw 7 q158 ∷
   rw 10 q159 ∷ []) Eq.refl

private
  q160 : Eqn
  q160 = sE 2492 lem-pass-X1-CSd10-X1-vs-S0-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-Sd0
  q161 : Eqn
  q161 = wE 2410 W
  q162 : Eqn
  q162 = wE 2411 W

-- CA CS10 Gad(t=0, W=(), d=SSK, e=-1): 5 steps
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SSK-e≡-1⟩ : ⟪ (ℓ "丠丈丈上中九丮九下三三") ⟫ʷ ≈ ⟪ (ℓ "三上中九丮九下丈丠") ⟫ʷ
lem-CA-CS10-Gad⟨t≡0-W≡⟨⟩-d≡SSK-e≡-1⟩ = derive (ℓ "丠丈丈上中九丮九下三三") (ℓ "三上中九丮九下丈丠")
  (rw 0 q155 ∷
   rw 1 q160 ∷
   rw 0 q161 ∷
   rw 6 q162 ∷
   rw 8 q159 ∷ []) Eq.refl

private
  q163 : Eqn
  q163 = sE 852 lem-pass-X2-CS20-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q164 : Eqn
  q164 = sE 849 lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q165 : Eqn
  q165 = sE 2464 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q166 : Eqn
  q166 = sE 850 lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q167 : Eqn
  q167 = sE 853 lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [X2 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2]: 7 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 : ⟪ (ℓ "习丽习举丘丈上中九丮九下三丘") ⟫ʷ ≈ ⟪ (ℓ "丘丈上中九丮九下三丘习丽习举") ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 = derive (ℓ "习丽习举丘丈上中九丮九下三丘") (ℓ "丘丈上中九丮九下三丘习丽习举")
  (rw 4 q111 ∷
   rw⁻ 0 q163 ∷
   rw⁻ 3 q164 ∷
   rw 6 q165 ∷
   rw⁻ 12 q166 ∷
   rw⁻ 15 q167 ∷
   rw⁻ 0 q117 ∷ []) Eq.refl

private
  q168 : Eqn
  q168 = sE 2485 lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡1⟩-3
  q169 : Eqn
  q169 = sE 2048 lem-pass-X3-CS31-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q170 : Eqn
  q170 = sE 88 lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q171 : Eqn
  q171 = sE 2471 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3
  q172 : Eqn
  q172 = sE 1051 lem-pass-X3-CKd31-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q173 : Eqn
  q173 = sE 2060 lem-pass-X3-CSd31-X3-vs-TOFF102-CS13-TOFF102-CSd13
  q174 : Eqn
  q174 = sE 2485 lem-ca-split-Gad⟨t≡1-W≡⟨3⟩-d≡SK-e≡1⟩-3

-- pass [TOFF102 CS13 TOFF102 CSd13] [X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X3]: 7 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 : ⟪ (ℓ "习丽习举丞与丐习丽习举丑丏丞") ⟫ʷ ≈ ⟪ (ℓ "丞与丐习丽习举丑丏丞习丽习举") ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3 = derive (ℓ "习丽习举丞与丐习丽习举丑丏丞") (ℓ "丞与丐习丽习举丑丏丞习丽习举")
  (rw 4 q168 ∷
   rw⁻ 0 q169 ∷
   rw⁻ 3 q170 ∷
   rw 6 q171 ∷
   rw⁻ 12 q172 ∷
   rw⁻ 15 q173 ∷
   rw⁻ 0 q174 ∷ []) Eq.refl

private
  q175 : Eqn
  q175 = sE 2501 lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [X2 TOFF102 CS13 TOFF102 CSd13 X2]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : ⟪ (ℓ "习丽习举丘习丽习举丘") ⟫ʷ ≈ ⟪ (ℓ "丘习丽习举丘习丽习举") ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = derive (ℓ "习丽习举丘习丽习举丘") (ℓ "丘习丽习举丘习丽习举")
  (rw⁻ 0 q175 ∷ []) Eq.refl

private
  q176 : Eqn
  q176 = wE 1478 W
  q177 : Eqn
  q177 = sE 2494 lem-pass-X2-CKd21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1
  q178 : Eqn
  q178 = wE 1479 W

-- pass [CKd21] [X2 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2]: 3 steps
lem-pass-CKd21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 : ⟪ (ℓ "么丘与丐习丽习举丑丏丘") ⟫ʷ ≈ ⟪ (ℓ "丘与丐习丽习举丑丏丘么") ⟫ʷ
lem-pass-CKd21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 = derive (ℓ "么丘与丐习丽习举丑丏丘") (ℓ "丘与丐习丽习举丑丏丘么")
  (rw 0 q176 ∷
   rw 1 q177 ∷
   rw 9 q178 ∷ []) Eq.refl

private
  q179 : Eqn
  q179 = wE 1474 W
  q180 : Eqn
  q180 = sE 2498 lem-pass-X2-CS21-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1
  q181 : Eqn
  q181 = wE 1475 W

-- pass [CS21] [X2 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2]: 3 steps
lem-pass-CS21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 : ⟪ (ℓ "丶丘与丐习丽习举丑丏丘") ⟫ʷ ≈ ⟪ (ℓ "丘与丐习丽习举丑丏丘丶") ⟫ʷ
lem-pass-CS21-vs-X2-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2 = derive (ℓ "丶丘与丐习丽习举丑丏丘") (ℓ "丘与丐习丽习举丑丏丘丶")
  (rw 0 q179 ∷
   rw 1 q180 ∷
   rw 9 q181 ∷ []) Eq.refl

private
  q182 : Eqn
  q182 = sE 2502 lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : ⟪ (ℓ "习丽习举丘丞习丽习举丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞习丽习举丘丞习丽习举") ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = derive (ℓ "习丽习举丘丞习丽习举丘丞") (ℓ "丘丞习丽习举丘丞习丽习举")
  (rw⁻ 0 q182 ∷ []) Eq.refl

private
  q183 : Eqn
  q183 = sE 2495 lem-pass-X2-CKd21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3

-- pass [CKd21] [X2 X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2 X3]: 5 steps
lem-pass-CKd21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 : ⟪ (ℓ "么丘丞与丐习丽习举丑丏丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞与丐习丽习举丑丏丘丞么") ⟫ʷ
lem-pass-CKd21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 = derive (ℓ "么丘丞与丐习丽习举丑丏丘丞") (ℓ "丘丞与丐习丽习举丑丏丘丞么")
  (rw 0 q176 ∷
   rw 13 q132 ∷
   rw 1 q183 ∷
   rw 11 q178 ∷
   rw⁻ 10 q132 ∷ []) Eq.refl

private
  q184 : Eqn
  q184 = sE 2499 lem-pass-X2-CS21-X2-vs-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X3

-- pass [CS21] [X2 X3 S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1 X2 X3]: 5 steps
lem-pass-CS21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 : ⟪ (ℓ "丶丘丞与丐习丽习举丑丏丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞与丐习丽习举丑丏丘丞丶") ⟫ʷ
lem-pass-CS21-vs-X2-X3-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-X2-X3 = derive (ℓ "丶丘丞与丐习丽习举丑丏丘丞") (ℓ "丘丞与丐习丽习举丑丏丘丞丶")
  (rw 0 q179 ∷
   rw 13 q132 ∷
   rw 1 q184 ∷
   rw 11 q181 ∷
   rw⁻ 10 q132 ∷ []) Eq.refl

-- cls 0000PP0 1000PP0 = e: 17 steps
lem-cls-0000PP0-1000PP0-≡-e : ⟪ (ℓ "九中九丮丌九中九丮丌") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-cls-0000PP0-1000PP0-≡-e = derive (ℓ "九中九丮丌九中九丮丌") []
  (rw 4 q71 ∷
   rw 5 q21 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q22 ∷
   re 3 1 (ℓ "乏丨乏") ∷
   rw 5 q22 ∷
   rw 4 q45 ∷
   rw 3 q22 ∷
   rw 2 q35 ∷
   rw 3 q21 ∷
   re 2 1 (ℓ "乏丨乏") ∷
   rw 4 q22 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q22 ∷
   rw 2 q36 ∷
   rw 1 q22 ∷
   rw 0 q35 ∷ []) Eq.refl

private
  q185 : Eqn
  q185 = sE 2505 lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3
  q186 : Eqn
  q186 = sE 1930 lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q187 : Eqn
  q187 = sE 841 lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q188 : Eqn
  q188 = sE 1926 lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q189 : Eqn
  q189 = sE 2472 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q190 : Eqn
  q190 = sE 38 lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q191 : Eqn
  q191 = sE 2505 lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3

-- pass [TOFF012 CS03 TOFF012 CSd03] [X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X3]: 11 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : ⟪ (ℓ "九中九丮丞三下丈丈中九丮九三三上丈丞") ⟫ʷ ≈ ⟪ (ℓ "丞三下丈丈中九丮九三三上丈丞九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = derive (ℓ "九中九丮丞三下丈丈中九丮九三三上丈丞") (ℓ "丞三下丈丈中九丮九三三上丈丞九中九丮")
  (rw 4 q185 ∷
   rw⁻ 0 q186 ∷
   rw⁻ 3 q187 ∷
   rw⁻ 6 q188 ∷
   rw⁻ 9 q188 ∷
   rw 12 q189 ∷
   rw⁻ 18 q186 ∷
   rw⁻ 21 q186 ∷
   rw⁻ 24 q190 ∷
   rw⁻ 27 q188 ∷
   rw⁻ 0 q191 ∷ []) Eq.refl

private
  q192 : Eqn
  q192 = eqn (ℓ "丕丞") (ℓ "丞丕") (low₃-comm (((S • S • S) ↑ ↑)) (X))
  q193 : Eqn
  q193 = eqn (ℓ "丗丞") (ℓ "丞丗") (low₃-comm (((K • iI) ↑ ↑)) (X))
  q194 : Eqn
  q194 = eqn (ℓ "且丞") (ℓ "丞且") (low₃-comm ((S ↑ ↑)) (X))
  q195 : Eqn
  q195 = eqn (ℓ "世丞") (ℓ "丞世") (low₃-comm ((K ↑ ↑)) (X))
  q196 : Eqn
  q196 = wE 2412 W
  q197 : Eqn
  q197 = wE 2413 W
  q198 : Eqn
  q198 = sE 2506 lem-pass-CS32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3
  q199 : Eqn
  q199 = sE 2463 lem-pass-CKd32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3
  q200 : Eqn
  q200 = sE 2507 lem-pass-CSd32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3
  q201 : Eqn
  q201 = wE 2414 W

-- ca-split Gad(t=2, W=(3,), d=SdKdSS, e=-1) 3: 15 steps
lem-ca-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3 : ⟪ (ℓ "丞丕丗且且义乣乊乣丕丕世且丞") ⟫ʷ ≈ ⟪ (ℓ "丞乊丞丞乘丞丞义丞丞义丞丞义乣乊乣丞丞乊丞丞乊丞丞乗丞丞义丞") ⟫ʷ
lem-ca-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3 = derive (ℓ "丞丕丗且且义乣乊乣丕丕世且丞") (ℓ "丞乊丞丞乘丞丞义丞丞义丞丞义乣乊乣丞丞乊丞丞乊丞丞乗丞丞义丞")
  (rw⁻ 0 q192 ∷
   rw⁻ 1 q193 ∷
   rw⁻ 2 q194 ∷
   rw⁻ 3 q194 ∷
   rw 12 q194 ∷
   rw 11 q195 ∷
   rw 10 q192 ∷
   rw 9 q192 ∷
   rw 0 q196 ∷
   rw 22 q197 ∷
   rw 15 q198 ∷
   rw 14 q198 ∷
   rw 13 q199 ∷
   rw 12 q200 ∷
   rw 18 q201 ∷ []) Eq.refl

private
  q202 : Eqn
  q202 = sE 2511 lem-pass-X3-TOFF201-CS23-TOFF201-CSd23-X3-vs-TOFF013-CS02-TOFF013-CSd02

-- pass [TOFF013 CS02 TOFF013 CSd02] [X3 TOFF201 CS23 TOFF201 CSd23 X3]: 1 steps
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 : ⟪ (ℓ "乞丧乞丨丞乣义乣乊丞") ⟫ʷ ≈ ⟪ (ℓ "丞乣义乣乊丞乞丧乞丨") ⟫ʷ
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 = derive (ℓ "乞丧乞丨丞乣义乣乊丞") (ℓ "丞乣义乣乊丞乞丧乞丨")
  (rw⁻ 0 q202 ∷ []) Eq.refl

private
  q203 : Eqn
  q203 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q204 : Eqn
  q204 = wE 2111 W
  q205 : Eqn
  q205 = sE 2508 lem-pass-X3-CS31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0
  q206 : Eqn
  q206 = wE 2112 W

-- pass [CS31] [X0 X3 CS13 TOFF102 CSd13 TOFF102 X0 X3]: 5 steps
lem-pass-CS31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : ⟪ (ℓ "丽丌丞丽习举习丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丽习举习丌丞丽") ⟫ʷ
lem-pass-CS31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = derive (ℓ "丽丌丞丽习举习丌丞") (ℓ "丌丞丽习举习丌丞丽")
  (rw 1 q203 ∷
   rw 0 q204 ∷
   rw 1 q205 ∷
   rw 7 q206 ∷
   rw⁻ 0 q203 ∷ []) Eq.refl

private
  q207 : Eqn
  q207 = sE 2503 lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [CS03 TOFF012 CSd03 TOFF012] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (ℓ "中九丮九丞中九丮九丞") ⟫ʷ ≈ ⟪ (ℓ "丞中九丮九丞中九丮九") ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (ℓ "中九丮九丞中九丮九丞") (ℓ "丞中九丮九丞中九丮九")
  (rw⁻ 0 q207 ∷ []) Eq.refl

private
  q208 : Eqn
  q208 = wE 2154 W
  q209 : Eqn
  q209 = sE 2509 lem-pass-X3-CS32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0
  q210 : Eqn
  q210 = wE 2155 W

-- pass [CS32] [X0 X3 CS23 TOFF201 CSd23 TOFF201 X0 X3]: 5 steps
lem-pass-CS32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 : ⟪ (ℓ "义丌丞义乣乊乣丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞义乣乊乣丌丞义") ⟫ʷ
lem-pass-CS32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 = derive (ℓ "义丌丞义乣乊乣丌丞") (ℓ "丌丞义乣乊乣丌丞义")
  (rw 1 q203 ∷
   rw 0 q208 ∷
   rw 1 q209 ∷
   rw 7 q210 ∷
   rw⁻ 0 q203 ∷ []) Eq.refl

private
  q211 : Eqn
  q211 = wE 2242 W
  q212 : Eqn
  q212 = sE 2510 lem-pass-X3-CSd32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0
  q213 : Eqn
  q213 = wE 2243 W

-- pass [CSd32] [X0 X3 CS23 TOFF201 CSd23 TOFF201 X0 X3]: 5 steps
lem-pass-CSd32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 : ⟪ (ℓ "乊丌丞义乣乊乣丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞义乣乊乣丌丞乊") ⟫ʷ
lem-pass-CSd32-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 = derive (ℓ "乊丌丞义乣乊乣丌丞") (ℓ "丌丞义乣乊乣丌丞乊")
  (rw 1 q203 ∷
   rw 0 q211 ∷
   rw 1 q212 ∷
   rw 7 q213 ∷
   rw⁻ 0 q203 ∷ []) Eq.refl

private
  q214 : Eqn
  q214 = sE 2512 lem-pass-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3-vs-TOFF013-CS02-TOFF013-CSd02

-- pass [TOFF013 CS02 TOFF013 CSd02] [X0 X3 TOFF201 CS23 TOFF201 CSd23 X0 X3]: 1 steps
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 : ⟪ (ℓ "乞丧乞丨丌丞乣义乣乊丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞乣义乣乊丌丞乞丧乞丨") ⟫ʷ
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 = derive (ℓ "乞丧乞丨丌丞乣义乣乊丌丞") (ℓ "丌丞乣义乣乊丌丞乞丧乞丨")
  (rw⁻ 0 q214 ∷ []) Eq.refl

private
  q215 : Eqn
  q215 = wE 1466 W
  q216 : Eqn
  q216 = sE 2513 lem-pass-X3-CSd30-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0
  q217 : Eqn
  q217 = wE 1467 W

-- pass [CSd30] [X0 X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X0 X3]: 25 steps
lem-pass-CSd30-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 : ⟪ (ℓ "丮丌丞丕丗且且义乣乊乣丕丕世且丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丕丗且且义乣乊乣丕丕世且丌丞丮") ⟫ʷ
lem-pass-CSd30-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 = derive (ℓ "丮丌丞丕丗且且义乣乊乣丕丕世且丌丞") (ℓ "丌丞丕丗且且义乣乊乣丕丕世且丌丞丮")
  (rw 1 q203 ∷
   rw 2 q21 ∷
   rw 1 q23 ∷
   re 0 1 (ℓ "乏丨乏") ∷
   rw 2 q22 ∷
   rw 1 q215 ∷
   rw 0 q26 ∷
   rw 1 q26 ∷
   rw 4 q21 ∷
   re 2 3 (ℓ "丮") ∷
   rw 3 q26 ∷
   rw 4 q22 ∷
   rw 1 q216 ∷
   rw 19 q21 ∷
   rw 18 q23 ∷
   rw 17 q23 ∷
   re 16 1 (ℓ "乏丨乏") ∷
   rw 18 q22 ∷
   rw 15 q23 ∷
   rw 16 q217 ∷
   rw 15 q26 ∷
   rw 18 q21 ∷
   re 16 3 (ℓ "丮") ∷
   rw 17 q22 ∷
   rw⁻ 0 q203 ∷ []) Eq.refl

private
  q218 : Eqn
  q218 = sE 2514 lem-pass-X3-CKd30-X3-vs-X0-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0

-- pass [CKd30] [X0 X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X0 X3]: 25 steps
lem-pass-CKd30-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 : ⟪ (ℓ "乒丌丞丕丗且且义乣乊乣丕丕世且丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丕丗且且义乣乊乣丕丕世且丌丞乒") ⟫ʷ
lem-pass-CKd30-vs-X0-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X0-X3 = derive (ℓ "乒丌丞丕丗且且义乣乊乣丕丕世且丌丞") (ℓ "丌丞丕丗且且义乣乊乣丕丕世且丌丞乒")
  (rw 1 q203 ∷
   rw 2 q21 ∷
   rw 1 q23 ∷
   re 0 1 (ℓ "乏久乏") ∷
   rw 2 q22 ∷
   rw 1 q131 ∷
   rw 0 q26 ∷
   rw 1 q26 ∷
   rw 4 q21 ∷
   re 2 3 (ℓ "乒") ∷
   rw 3 q26 ∷
   rw 4 q22 ∷
   rw 1 q218 ∷
   rw 19 q21 ∷
   rw 18 q23 ∷
   rw 17 q23 ∷
   re 16 1 (ℓ "乏久乏") ∷
   rw 18 q22 ∷
   rw 15 q23 ∷
   rw 16 q134 ∷
   rw 15 q26 ∷
   rw 18 q21 ∷
   re 16 3 (ℓ "乒") ∷
   rw 17 q22 ∷
   rw⁻ 0 q203 ∷ []) Eq.refl
