{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SR010 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.R010 (Sᴰ : SR010) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

-- The lemmas of other derivation modules (DSig).
private
  lem-comm-push-SBOXd⟨0·1·2·3⟩-sw1-L : WsL → St 2472
  lem-comm-push-SBOXd⟨0·1·2·3⟩-sw1-L = pickᴰ 0 Sᴰ
  lem-comm-push-SBOXd⟨0·1·2·3⟩-sw2-R : WsL → St 2473
  lem-comm-push-SBOXd⟨0·1·2·3⟩-sw2-R = pickᴰ 1 Sᴰ
  lem-comm-push-SBOXd⟨0·1·3·2⟩-sw0-R : WsL → St 2474
  lem-comm-push-SBOXd⟨0·1·3·2⟩-sw0-R = pickᴰ 2 Sᴰ
  lem-comm-push-SBOXd⟨0·1·3·2⟩-sw2-L : WsL → St 2475
  lem-comm-push-SBOXd⟨0·1·3·2⟩-sw2-L = pickᴰ 3 Sᴰ
  lem-comm-push-SBOXd⟨0·2·1·3⟩-sw0-R : WsL → St 2476
  lem-comm-push-SBOXd⟨0·2·1·3⟩-sw0-R = pickᴰ 4 Sᴰ
  lem-comm-push-SBOXd⟨0·2·1·3⟩-sw1-R : WsL → St 2477
  lem-comm-push-SBOXd⟨0·2·1·3⟩-sw1-R = pickᴰ 5 Sᴰ
  lem-comm-push-SBOXd⟨0·2·1·3⟩-sw2-R : WsL → St 2478
  lem-comm-push-SBOXd⟨0·2·1·3⟩-sw2-R = pickᴰ 6 Sᴰ
  lem-comm-push-SBOXd⟨0·3·1·2⟩-sw2-L : WsL → St 2479
  lem-comm-push-SBOXd⟨0·3·1·2⟩-sw2-L = pickᴰ 7 Sᴰ
  lem-comm-push-SBOXd⟨0·4·1·2⟩-sw1-R : WsL → St 2480
  lem-comm-push-SBOXd⟨0·4·1·2⟩-sw1-R = pickᴰ 8 Sᴰ
  lem-comm-push-SBOXd⟨0·4·2·1⟩-sw1-L : WsL → St 2481
  lem-comm-push-SBOXd⟨0·4·2·1⟩-sw1-L = pickᴰ 9 Sᴰ
  lem-comm-push-SBOXd⟨1·0·3·2⟩-sw0-L : WsL → St 2482
  lem-comm-push-SBOXd⟨1·0·3·2⟩-sw0-L = pickᴰ 10 Sᴰ
  lem-comm-push-SBOXd⟨1·0·3·2⟩-sw1-R : WsL → St 2483
  lem-comm-push-SBOXd⟨1·0·3·2⟩-sw1-R = pickᴰ 11 Sᴰ
  lem-comm-push-SBOXd⟨1·2·0·3⟩-sw1-R : WsL → St 2484
  lem-comm-push-SBOXd⟨1·2·0·3⟩-sw1-R = pickᴰ 12 Sᴰ
  lem-comm-push-SBOXd⟨2·0·3·1⟩-sw1-L : WsL → St 2485
  lem-comm-push-SBOXd⟨2·0·3·1⟩-sw1-L = pickᴰ 13 Sᴰ
  lem-comm-push-SBOXd⟨2·0·3·1⟩-sw2-R : WsL → St 2486
  lem-comm-push-SBOXd⟨2·0·3·1⟩-sw2-R = pickᴰ 14 Sᴰ
  lem-comm-push-SBOXd⟨4·0·3·1⟩-sw1-R : WsL → St 2487
  lem-comm-push-SBOXd⟨4·0·3·1⟩-sw1-R = pickᴰ 15 Sᴰ
  lem-comm-push-SBOXd⟨4·1·0·3⟩-sw1-R : WsL → St 2488
  lem-comm-push-SBOXd⟨4·1·0·3⟩-sw1-R = pickᴰ 16 Sᴰ
  lem-comm-push-SBOXd⟨4·2·0·3⟩-sw0-R : WsL → St 2489
  lem-comm-push-SBOXd⟨4·2·0·3⟩-sw0-R = pickᴰ 17 Sᴰ
  lem-comm-push-SBOX⟨0·1·2·3⟩-sw1-L : WsL → St 2490
  lem-comm-push-SBOX⟨0·1·2·3⟩-sw1-L = pickᴰ 18 Sᴰ
  lem-comm-push-SBOX⟨0·1·2·3⟩-sw2-R : WsL → St 2491
  lem-comm-push-SBOX⟨0·1·2·3⟩-sw2-R = pickᴰ 19 Sᴰ
  lem-comm-push-SBOX⟨0·1·3·2⟩-sw0-R : WsL → St 2492
  lem-comm-push-SBOX⟨0·1·3·2⟩-sw0-R = pickᴰ 20 Sᴰ
  lem-comm-push-SBOX⟨0·1·3·2⟩-sw2-L : WsL → St 2493
  lem-comm-push-SBOX⟨0·1·3·2⟩-sw2-L = pickᴰ 21 Sᴰ
  lem-comm-push-SBOX⟨0·2·1·3⟩-sw0-R : WsL → St 2494
  lem-comm-push-SBOX⟨0·2·1·3⟩-sw0-R = pickᴰ 22 Sᴰ
  lem-comm-push-SBOX⟨0·2·1·3⟩-sw1-R : WsL → St 2495
  lem-comm-push-SBOX⟨0·2·1·3⟩-sw1-R = pickᴰ 23 Sᴰ
  lem-comm-push-SBOX⟨0·2·1·3⟩-sw2-R : WsL → St 2496
  lem-comm-push-SBOX⟨0·2·1·3⟩-sw2-R = pickᴰ 24 Sᴰ
  lem-comm-push-SBOX⟨0·3·1·2⟩-sw2-L : WsL → St 2497
  lem-comm-push-SBOX⟨0·3·1·2⟩-sw2-L = pickᴰ 25 Sᴰ
  lem-comm-push-SBOX⟨0·4·1·2⟩-sw1-R : WsL → St 2498
  lem-comm-push-SBOX⟨0·4·1·2⟩-sw1-R = pickᴰ 26 Sᴰ
  lem-comm-push-SBOX⟨0·4·2·1⟩-sw1-L : WsL → St 2499
  lem-comm-push-SBOX⟨0·4·2·1⟩-sw1-L = pickᴰ 27 Sᴰ
  lem-comm-push-SBOX⟨1·0·3·2⟩-sw0-L : WsL → St 2500
  lem-comm-push-SBOX⟨1·0·3·2⟩-sw0-L = pickᴰ 28 Sᴰ
  lem-comm-push-SBOX⟨1·0·3·2⟩-sw1-R : WsL → St 2501
  lem-comm-push-SBOX⟨1·0·3·2⟩-sw1-R = pickᴰ 29 Sᴰ
  lem-comm-push-SBOX⟨1·2·0·3⟩-sw1-R : WsL → St 2502
  lem-comm-push-SBOX⟨1·2·0·3⟩-sw1-R = pickᴰ 30 Sᴰ
  lem-comm-push-SBOX⟨2·0·3·1⟩-sw1-L : WsL → St 2503
  lem-comm-push-SBOX⟨2·0·3·1⟩-sw1-L = pickᴰ 31 Sᴰ
  lem-comm-push-SBOX⟨2·0·3·1⟩-sw2-R : WsL → St 2504
  lem-comm-push-SBOX⟨2·0·3·1⟩-sw2-R = pickᴰ 32 Sᴰ
  lem-comm-push-SBOX⟨4·0·3·1⟩-sw1-R : WsL → St 2505
  lem-comm-push-SBOX⟨4·0·3·1⟩-sw1-R = pickᴰ 33 Sᴰ
  lem-comm-push-SBOX⟨4·1·0·3⟩-sw1-R : WsL → St 2506
  lem-comm-push-SBOX⟨4·1·0·3⟩-sw1-R = pickᴰ 34 Sᴰ
  lem-comm-push-SBOX⟨4·2·0·3⟩-sw0-R : WsL → St 2507
  lem-comm-push-SBOX⟨4·2·0·3⟩-sw0-R = pickᴰ 35 Sᴰ
  lem-comm-push-CCZ024-sw0-L : WsL → St 2403
  lem-comm-push-CCZ024-sw0-L = pickᴰ 36 Sᴰ
  lem-comm-push-TOFF204-sw0-L : WsL → St 2411
  lem-comm-push-TOFF204-sw0-L = pickᴰ 37 Sᴰ
  lem-comm-push-CCZ014-sw0-R : WsL → St 2443
  lem-comm-push-CCZ014-sw0-R = pickᴰ 38 Sᴰ
  lem-comm-push-CCZ034-sw3-L : WsL → St 2508
  lem-comm-push-CCZ034-sw3-L = pickᴰ 39 Sᴰ
  lem-comm-push-CCZ034-sw3-R : WsL → St 2446
  lem-comm-push-CCZ034-sw3-R = pickᴰ 40 Sᴰ
  lem-comm-push-CCZ124-sw0-L : WsL → St 2447
  lem-comm-push-CCZ124-sw0-L = pickᴰ 41 Sᴰ
  lem-comm-push-TOFF034-sw1-R : WsL → St 2449
  lem-comm-push-TOFF034-sw1-R = pickᴰ 42 Sᴰ
  lem-comm-push-TOFF034-sw3-L : WsL → St 2509
  lem-comm-push-TOFF034-sw3-L = pickᴰ 43 Sᴰ
  lem-comm-push-TOFF034-sw3-R : WsL → St 2510
  lem-comm-push-TOFF034-sw3-R = pickᴰ 44 Sᴰ
  lem-comm-push-TOFF124-sw0-L : WsL → St 2511
  lem-comm-push-TOFF124-sw0-L = pickᴰ 45 Sᴰ
  lem-comm-push-CCZ024-sw0-R : WsL → St 2463
  lem-comm-push-CCZ024-sw0-R = pickᴰ 46 Sᴰ
  lem-comm-push-CCZ124-sw0-R : WsL → St 2464
  lem-comm-push-CCZ124-sw0-R = pickᴰ 47 Sᴰ
  lem-comm-push-TOFF024-sw0-R : WsL → St 2465
  lem-comm-push-TOFF024-sw0-R = pickᴰ 48 Sᴰ
  lem-comm-push-TOFF134-sw0-R : WsL → St 2512
  lem-comm-push-TOFF134-sw0-R = pickᴰ 49 Sᴰ
  lem-comm-push-TOFF214-sw0-R : WsL → St 2513
  lem-comm-push-TOFF214-sw0-R = pickᴰ 50 Sᴰ
  lem-comm-push-TOFF401-sw0-R : WsL → St 2468
  lem-comm-push-TOFF401-sw0-R = pickᴰ 51 Sᴰ
  lem-comm-push-BOX⟨0·1423⟩-sw0-R : WsL → St 2514
  lem-comm-push-BOX⟨0·1423⟩-sw0-R = pickᴰ 52 Sᴰ
  lem-comm-push-BOX⟨0·1423⟩-sw2-L : WsL → St 2515
  lem-comm-push-BOX⟨0·1423⟩-sw2-L = pickᴰ 53 Sᴰ
  lem-comm-push-BOX⟨0·1432⟩-sw1-L : WsL → St 2516
  lem-comm-push-BOX⟨0·1432⟩-sw1-L = pickᴰ 54 Sᴰ
  lem-comm-push-BOX⟨0·1432⟩-sw2-R : WsL → St 2517
  lem-comm-push-BOX⟨0·1432⟩-sw2-R = pickᴰ 55 Sᴰ
  lem-comm-push-BOX⟨0·2431⟩-sw0-R : WsL → St 2518
  lem-comm-push-BOX⟨0·2431⟩-sw0-R = pickᴰ 56 Sᴰ
  lem-comm-push-BOX⟨0·2431⟩-sw1-R : WsL → St 2519
  lem-comm-push-BOX⟨0·2431⟩-sw1-R = pickᴰ 57 Sᴰ
  lem-comm-push-BOX⟨0·2431⟩-sw2-R : WsL → St 2520
  lem-comm-push-BOX⟨0·2431⟩-sw2-R = pickᴰ 58 Sᴰ
  lem-comm-push-BOX⟨0·3421⟩-sw2-L : WsL → St 2521
  lem-comm-push-BOX⟨0·3421⟩-sw2-L = pickᴰ 59 Sᴰ
  lem-comm-push-BOX⟨0·412⟩-sw2-R : WsL → St 2522
  lem-comm-push-BOX⟨0·412⟩-sw2-R = pickᴰ 60 Sᴰ
  lem-comm-push-BOX⟨0·423⟩-sw0-R : WsL → St 2523
  lem-comm-push-BOX⟨0·423⟩-sw0-R = pickᴰ 61 Sᴰ
  lem-comm-push-BOX⟨0·4312⟩-sw1-L : WsL → St 2524
  lem-comm-push-BOX⟨0·4312⟩-sw1-L = pickᴰ 62 Sᴰ
  lem-comm-push-BOX⟨0·4321⟩-sw1-R : WsL → St 2525
  lem-comm-push-BOX⟨0·4321⟩-sw1-R = pickᴰ 63 Sᴰ
  lem-comm-push-BOX⟨1·0423⟩-sw0-L : WsL → St 2526
  lem-comm-push-BOX⟨1·0423⟩-sw0-L = pickᴰ 64 Sᴰ
  lem-comm-push-BOX⟨1·0423⟩-sw1-R : WsL → St 2527
  lem-comm-push-BOX⟨1·0423⟩-sw1-R = pickᴰ 65 Sᴰ
  lem-comm-push-BOX⟨1·2430⟩-sw1-R : WsL → St 2528
  lem-comm-push-BOX⟨1·2430⟩-sw1-R = pickᴰ 66 Sᴰ
  lem-comm-push-BOX⟨2·0413⟩-sw1-L : WsL → St 2529
  lem-comm-push-BOX⟨2·0413⟩-sw1-L = pickᴰ 67 Sᴰ
  lem-comm-push-BOX⟨2·0413⟩-sw2-R : WsL → St 2530
  lem-comm-push-BOX⟨2·0413⟩-sw2-R = pickᴰ 68 Sᴰ
  lem-comm-push-BOX⟨3·021⟩-sw3-R : WsL → St 2531
  lem-comm-push-BOX⟨3·021⟩-sw3-R = pickᴰ 69 Sᴰ
  lem-comm-push-BOX⟨3·0412⟩-sw3-R : WsL → St 2532
  lem-comm-push-BOX⟨3·0412⟩-sw3-R = pickᴰ 70 Sᴰ
  lem-comm-push-BOX⟨4·012⟩-sw2-R : WsL → St 2533
  lem-comm-push-BOX⟨4·012⟩-sw2-R = pickᴰ 71 Sᴰ
  lem-comm-push-BOX⟨4·013⟩-sw0-R : WsL → St 2534
  lem-comm-push-BOX⟨4·013⟩-sw0-R = pickᴰ 72 Sᴰ
  lem-comm-push-BOX⟨4·013⟩-sw2-L : WsL → St 2535
  lem-comm-push-BOX⟨4·013⟩-sw2-L = pickᴰ 73 Sᴰ
  lem-comm-push-BOX⟨4·0213⟩-sw1-R : WsL → St 2536
  lem-comm-push-BOX⟨4·0213⟩-sw1-R = pickᴰ 74 Sᴰ
  lem-comm-push-BOX⟨4·021⟩-sw3-L : WsL → St 2537
  lem-comm-push-BOX⟨4·021⟩-sw3-L = pickᴰ 75 Sᴰ
  lem-comm-push-BOX⟨4·103⟩-sw0-L : WsL → St 2538
  lem-comm-push-BOX⟨4·103⟩-sw0-L = pickᴰ 76 Sᴰ
  lem-comm-push-BOX⟨4·1230⟩-sw1-R : WsL → St 2539
  lem-comm-push-BOX⟨4·1230⟩-sw1-R = pickᴰ 77 Sᴰ
  lem-comm-push-BOX⟨4·203⟩-sw0-R : WsL → St 2540
  lem-comm-push-BOX⟨4·203⟩-sw0-R = pickᴰ 78 Sᴰ
  lem-comm-push-BOX⟨4·2130⟩-sw0-R : WsL → St 2541
  lem-comm-push-BOX⟨4·2130⟩-sw0-R = pickᴰ 79 Sᴰ
  lem-comm-push-BOX⟨4·213⟩-sw0-L : WsL → St 2542
  lem-comm-push-BOX⟨4·213⟩-sw0-L = pickᴰ 80 Sᴰ

private
  q1 : WsL → Eqn
  q1 c4 = sE 2485 (lem-comm-push-SBOXd⟨2·0·3·1⟩-sw1-L c4)
  q2 : WsL → Eqn
  q2 c4 = wlE 38 c4
  q3 : WsL → Eqn
  q3 c4 = sE 2503 (lem-comm-push-SBOX⟨2·0·3·1⟩-sw1-L c4)
  q4 : WsL → Eqn
  q4 c4 = sE 2529 (lem-comm-push-BOX⟨2·0413⟩-sw1-L c4)

-- comm push SBOX(2;0;41;3) sw1 L: 7 steps
lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L : WsL → ⟪ (ℓ "俄乊") ⟫ʷ ≈ ⟪ (ℓ "乊侻") ⟫ʷ
lem-comm-push-SBOX⟨2·0·41·3⟩-sw1-L c4 = derive (ℓ "俄乊") (ℓ "乊侻")
  (re 0 1 (ℓ "伱亮係亮促") ∷
   rw 4 (q1 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   rw 0 (q4 c4) ∷
   re 1 5 (ℓ "侻") ∷ []) Eq.refl

private
  q5 : WsL → Eqn
  q5 c4 = sE 2482 (lem-comm-push-SBOXd⟨1·0·3·2⟩-sw0-L c4)
  q6 : WsL → Eqn
  q6 c4 = eqn (ℓ "丫亲") (ℓ "亲丫") (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))
  q7 : WsL → Eqn
  q7 c4 = sE 2500 (lem-comm-push-SBOX⟨1·0·3·2⟩-sw0-L c4)
  q8 : WsL → Eqn
  q8 c4 = sE 2526 (lem-comm-push-BOX⟨1·0423⟩-sw0-L c4)

-- comm push SBOX(1;0;42;3) sw0 L: 7 steps
lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L : WsL → ⟪ (ℓ "侻丫") ⟫ʷ ≈ ⟪ (ℓ "丫侧") ⟫ʷ
lem-comm-push-SBOX⟨1·0·42·3⟩-sw0-L c4 = derive (ℓ "侻丫") (ℓ "丫侧")
  (re 0 1 (ℓ "伏亲侹亲侺") ∷
   rw 4 (q5 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw 2 (q7 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw 0 (q8 c4) ∷
   re 1 5 (ℓ "侧") ∷ []) Eq.refl

private
  q9 : WsL → Eqn
  q9 c4 = sE 2475 (lem-comm-push-SBOXd⟨0·1·3·2⟩-sw2-L c4)
  q10 : WsL → Eqn
  q10 c4 = wlE 111 c4
  q11 : WsL → Eqn
  q11 c4 = sE 2493 (lem-comm-push-SBOX⟨0·1·3·2⟩-sw2-L c4)
  q12 : WsL → Eqn
  q12 c4 = sE 2515 (lem-comm-push-BOX⟨0·1423⟩-sw2-L c4)

-- comm push SBOX(0;1;42;3) sw2 L: 7 steps
lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L : WsL → ⟪ (ℓ "侧乥") ⟫ʷ ≈ ⟪ (ℓ "乥侩") ⟫ʷ
lem-comm-push-SBOX⟨0·1·42·3⟩-sw2-L c4 = derive (ℓ "侧乥") (ℓ "乥侩")
  (re 0 1 (ℓ "仄亲侥亲侦") ∷
   rw 4 (q9 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   rw 2 (q11 c4) ∷
   rw⁻ 1 (q10 c4) ∷
   rw 0 (q12 c4) ∷
   re 1 5 (ℓ "侩") ∷ []) Eq.refl

private
  q13 : WsL → Eqn
  q13 c4 = sE 2472 (lem-comm-push-SBOXd⟨0·1·2·3⟩-sw1-L c4)
  q14 : WsL → Eqn
  q14 c4 = wlE 83 c4
  q15 : WsL → Eqn
  q15 c4 = sE 2490 (lem-comm-push-SBOX⟨0·1·2·3⟩-sw1-L c4)
  q16 : WsL → Eqn
  q16 c4 = sE 2516 (lem-comm-push-BOX⟨0·1432⟩-sw1-L c4)

-- comm push SBOX(0;1;43;2) sw1 L: 7 steps
lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L : WsL → ⟪ (ℓ "侩乊") ⟫ʷ ≈ ⟪ (ℓ "乊侬") ⟫ʷ
lem-comm-push-SBOX⟨0·1·43·2⟩-sw1-L c4 = derive (ℓ "侩乊") (ℓ "乊侬")
  (re 0 1 (ℓ "仆亱侤亱侨") ∷
   rw 4 (q13 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw 2 (q15 c4) ∷
   rw⁻ 1 (q14 c4) ∷
   rw 0 (q16 c4) ∷
   re 1 5 (ℓ "侬") ∷ []) Eq.refl

private
  q17 : WsL → Eqn
  q17 c4 = sE 2519 (lem-comm-push-BOX⟨0·2431⟩-sw1-R c4)
  q18 : WsL → Eqn
  q18 c4 = sE 2495 (lem-comm-push-SBOX⟨0·2·1·3⟩-sw1-R c4)
  q19 : WsL → Eqn
  q19 c4 = sE 2477 (lem-comm-push-SBOXd⟨0·2·1·3⟩-sw1-R c4)

-- comm push SBOX(0;2;43;1) sw1 R: 7 steps
lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R : WsL → ⟪ (ℓ "乊侬") ⟫ʷ ≈ ⟪ (ℓ "侩乊") ⟫ʷ
lem-comm-push-SBOX⟨0·2·43·1⟩-sw1-R c4 = derive (ℓ "乊侬") (ℓ "侩乊")
  (re 1 1 (ℓ "仞亭侪亭侫") ∷
   rw 0 (q17 c4) ∷
   rw 1 (q14 c4) ∷
   rw 2 (q18 c4) ∷
   rw 3 (q14 c4) ∷
   rw 4 (q19 c4) ∷
   re 0 5 (ℓ "侩") ∷ []) Eq.refl

private
  q20 : WsL → Eqn
  q20 c4 = sE 2517 (lem-comm-push-BOX⟨0·1432⟩-sw2-R c4)
  q21 : WsL → Eqn
  q21 c4 = sE 2491 (lem-comm-push-SBOX⟨0·1·2·3⟩-sw2-R c4)
  q22 : WsL → Eqn
  q22 c4 = sE 2473 (lem-comm-push-SBOXd⟨0·1·2·3⟩-sw2-R c4)

-- comm push SBOX(0;1;43;2) sw2 R: 7 steps
lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R : WsL → ⟪ (ℓ "乥侩") ⟫ʷ ≈ ⟪ (ℓ "侧乥") ⟫ʷ
lem-comm-push-SBOX⟨0·1·43·2⟩-sw2-R c4 = derive (ℓ "乥侩") (ℓ "侧乥")
  (re 1 1 (ℓ "仆亱侤亱侨") ∷
   rw 0 (q20 c4) ∷
   rw 1 (q10 c4) ∷
   rw 2 (q21 c4) ∷
   rw 3 (q10 c4) ∷
   rw 4 (q22 c4) ∷
   re 0 5 (ℓ "侧") ∷ []) Eq.refl

private
  q23 : WsL → Eqn
  q23 c4 = sE 2514 (lem-comm-push-BOX⟨0·1423⟩-sw0-R c4)
  q24 : WsL → Eqn
  q24 c4 = sE 2492 (lem-comm-push-SBOX⟨0·1·3·2⟩-sw0-R c4)
  q25 : WsL → Eqn
  q25 c4 = sE 2474 (lem-comm-push-SBOXd⟨0·1·3·2⟩-sw0-R c4)

-- comm push SBOX(0;1;42;3) sw0 R: 7 steps
lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R : WsL → ⟪ (ℓ "丫侧") ⟫ʷ ≈ ⟪ (ℓ "侻丫") ⟫ʷ
lem-comm-push-SBOX⟨0·1·42·3⟩-sw0-R c4 = derive (ℓ "丫侧") (ℓ "侻丫")
  (re 1 1 (ℓ "仄亲侥亲侦") ∷
   rw 0 (q23 c4) ∷
   rw 1 (q6 c4) ∷
   rw 2 (q24 c4) ∷
   rw 3 (q6 c4) ∷
   rw 4 (q25 c4) ∷
   re 0 5 (ℓ "侻") ∷ []) Eq.refl

private
  q26 : WsL → Eqn
  q26 c4 = sE 2527 (lem-comm-push-BOX⟨1·0423⟩-sw1-R c4)
  q27 : WsL → Eqn
  q27 c4 = sE 2501 (lem-comm-push-SBOX⟨1·0·3·2⟩-sw1-R c4)
  q28 : WsL → Eqn
  q28 c4 = sE 2483 (lem-comm-push-SBOXd⟨1·0·3·2⟩-sw1-R c4)

-- comm push SBOX(1;0;42;3) sw1 R: 7 steps
lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R : WsL → ⟪ (ℓ "乊侻") ⟫ʷ ≈ ⟪ (ℓ "俄乊") ⟫ʷ
lem-comm-push-SBOX⟨1·0·42·3⟩-sw1-R c4 = derive (ℓ "乊侻") (ℓ "俄乊")
  (re 1 1 (ℓ "伏亲侹亲侺") ∷
   rw 0 (q26 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q27 c4) ∷
   rw 3 (q2 c4) ∷
   rw 4 (q28 c4) ∷
   re 0 5 (ℓ "俄") ∷ []) Eq.refl

private
  q29 : WsL → Eqn
  q29 c4 = sE 2542 (lem-comm-push-BOX⟨4·213⟩-sw0-L c4)
  q30 : WsL → Eqn
  q30 c4 = sE 2403 (lem-comm-push-CCZ024-sw0-L c4)
  q31 : WsL → Eqn
  q31 c4 = sE 2411 (lem-comm-push-TOFF204-sw0-L c4)

-- comm push BOX(2;4013) sw0 L: 8 steps
lem-comm-push-BOX⟨2·4013⟩-sw0-L : WsL → ⟪ (ℓ "佔丫") ⟫ʷ ≈ ⟪ (ℓ "丫佝") ⟫ʷ
lem-comm-push-BOX⟨2·4013⟩-sw0-L c4 = derive (ℓ "佔丫") (ℓ "丫佝")
  (re 0 1 (ℓ "亜亞体亞亜体") ∷
   rw 5 (q29 c4) ∷
   rw 4 (q30 c4) ∷
   rw 3 (q31 c4) ∷
   rw 2 (q29 c4) ∷
   rw 1 (q31 c4) ∷
   rw 0 (q30 c4) ∷
   re 1 6 (ℓ "佝") ∷ []) Eq.refl

private
  q32 : WsL → Eqn
  q32 c4 = sE 2538 (lem-comm-push-BOX⟨4·103⟩-sw0-L c4)
  q33 : WsL → Eqn
  q33 c4 = sE 2447 (lem-comm-push-CCZ124-sw0-L c4)
  q34 : WsL → Eqn
  q34 c4 = sE 2511 (lem-comm-push-TOFF124-sw0-L c4)

-- comm push BOX(1;4203) sw0 L: 8 steps
lem-comm-push-BOX⟨1·4203⟩-sw0-L : WsL → ⟪ (ℓ "伪丫") ⟫ʷ ≈ ⟪ (ℓ "丫伅") ⟫ʷ
lem-comm-push-BOX⟨1·4203⟩-sw0-L c4 = derive (ℓ "伪丫") (ℓ "丫伅")
  (re 0 1 (ℓ "亨亩伩亩亨伩") ∷
   rw 5 (q32 c4) ∷
   rw 4 (q33 c4) ∷
   rw 3 (q34 c4) ∷
   rw 2 (q32 c4) ∷
   rw 1 (q34 c4) ∷
   rw 0 (q33 c4) ∷
   re 1 6 (ℓ "伅") ∷ []) Eq.refl

private
  q35 : WsL → Eqn
  q35 c4 = sE 2535 (lem-comm-push-BOX⟨4·013⟩-sw2-L c4)
  q36 : WsL → Eqn
  q36 c4 = wlE 3 c4

-- comm push BOX(0;4213) sw2 L: 12 steps
lem-comm-push-BOX⟨0·4213⟩-sw2-L : WsL → ⟪ (ℓ "伅乥") ⟫ʷ ≈ ⟪ (ℓ "乥伋") ⟫ʷ
lem-comm-push-BOX⟨0·4213⟩-sw2-L c4 = derive (ℓ "伅乥") (ℓ "乥伋")
  (re 0 1 (ℓ "亜亝伄亝亜伄") ∷
   rw 5 (q35 c4) ∷
   rw⁻ 4 (q36 c4) ∷
   re 5 3 (ℓ "亠") ∷
   rw⁻ 3 (q36 c4) ∷
   re 4 3 (ℓ "亡") ∷
   rw 2 (q35 c4) ∷
   rw⁻ 1 (q36 c4) ∷
   re 2 3 (ℓ "亡") ∷
   rw⁻ 0 (q36 c4) ∷
   re 1 3 (ℓ "亠") ∷
   re 1 6 (ℓ "伋") ∷ []) Eq.refl

private
  q37 : WsL → Eqn
  q37 c4 = sE 2481 (lem-comm-push-SBOXd⟨0·4·2·1⟩-sw1-L c4)
  q38 : WsL → Eqn
  q38 c4 = wlE 127 c4
  q39 : WsL → Eqn
  q39 c4 = sE 2499 (lem-comm-push-SBOX⟨0·4·2·1⟩-sw1-L c4)
  q40 : WsL → Eqn
  q40 c4 = sE 2524 (lem-comm-push-BOX⟨0·4312⟩-sw1-L c4)

-- comm push SBOX(0;4;31;2) sw1 L: 7 steps
lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L : WsL → ⟪ (ℓ "侶乊") ⟫ʷ ≈ ⟪ (ℓ "乊侸") ⟫ʷ
lem-comm-push-SBOX⟨0·4·31·2⟩-sw1-L c4 = derive (ℓ "侶乊") (ℓ "乊侸")
  (re 0 1 (ℓ "伋亦侱亦侵") ∷
   rw 4 (q37 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   rw 2 (q39 c4) ∷
   rw⁻ 1 (q38 c4) ∷
   rw 0 (q40 c4) ∷
   re 1 5 (ℓ "侸") ∷ []) Eq.refl

private
  q41 : WsL → Eqn
  q41 c4 = sE 2537 (lem-comm-push-BOX⟨4·021⟩-sw3-L c4)
  q42 : WsL → Eqn
  q42 c4 = sE 2508 (lem-comm-push-CCZ034-sw3-L c4)
  q43 : WsL → Eqn
  q43 c4 = sE 2509 (lem-comm-push-TOFF034-sw3-L c4)

-- comm push BOX(0;4321) sw3 L: 8 steps
lem-comm-push-BOX⟨0·4321⟩-sw3-L : WsL → ⟪ (ℓ "伍乼") ⟫ʷ ≈ ⟪ (ℓ "乼件") ⟫ʷ
lem-comm-push-BOX⟨0·4321⟩-sw3-L c4 = derive (ℓ "伍乼") (ℓ "乼件")
  (re 0 1 (ℓ "亠亡伌亡亠伌") ∷
   rw 5 (q41 c4) ∷
   rw 4 (q42 c4) ∷
   rw 3 (q43 c4) ∷
   rw 2 (q41 c4) ∷
   rw 1 (q43 c4) ∷
   rw 0 (q42 c4) ∷
   re 1 6 (ℓ "件") ∷ []) Eq.refl

private
  q44 : WsL → Eqn
  q44 c4 = sE 2479 (lem-comm-push-SBOXd⟨0·3·1·2⟩-sw2-L c4)
  q45 : WsL → Eqn
  q45 c4 = sE 2497 (lem-comm-push-SBOX⟨0·3·1·2⟩-sw2-L c4)
  q46 : WsL → Eqn
  q46 c4 = sE 2521 (lem-comm-push-BOX⟨0·3421⟩-sw2-L c4)

-- comm push SBOX(0;3;42;1) sw2 L: 9 steps
lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L : WsL → ⟪ (ℓ "侯乥") ⟫ʷ ≈ ⟪ (ℓ "乥侬") ⟫ʷ
lem-comm-push-SBOX⟨0·3·42·1⟩-sw2-L c4 = derive (ℓ "侯乥") (ℓ "乥侬")
  (re 0 1 (ℓ "件亩侭亩侮") ∷
   rw 4 (q44 c4) ∷
   rw⁻ 3 (q36 c4) ∷
   re 4 3 (ℓ "亭") ∷
   rw 2 (q45 c4) ∷
   rw⁻ 1 (q36 c4) ∷
   re 2 3 (ℓ "亭") ∷
   rw 0 (q46 c4) ∷
   re 1 5 (ℓ "侬") ∷ []) Eq.refl

private
  q47 : WsL → Eqn
  q47 c4 = sE 2520 (lem-comm-push-BOX⟨0·2431⟩-sw2-R c4)
  q48 : WsL → Eqn
  q48 c4 = sE 2496 (lem-comm-push-SBOX⟨0·2·1·3⟩-sw2-R c4)
  q49 : WsL → Eqn
  q49 c4 = sE 2478 (lem-comm-push-SBOXd⟨0·2·1·3⟩-sw2-R c4)

-- comm push SBOX(0;2;43;1) sw2 R: 9 steps
lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R : WsL → ⟪ (ℓ "乥侬") ⟫ʷ ≈ ⟪ (ℓ "侯乥") ⟫ʷ
lem-comm-push-SBOX⟨0·2·43·1⟩-sw2-R c4 = derive (ℓ "乥侬") (ℓ "侯乥")
  (re 1 1 (ℓ "仞亭侪亭侫") ∷
   rw 0 (q47 c4) ∷
   re 2 1 (ℓ "乥亩乥") ∷
   rw 1 (q36 c4) ∷
   rw 2 (q48 c4) ∷
   re 4 1 (ℓ "乥亩乥") ∷
   rw 3 (q36 c4) ∷
   rw 4 (q49 c4) ∷
   re 0 5 (ℓ "侯") ∷ []) Eq.refl

private
  q50 : WsL → Eqn
  q50 c4 = sE 2446 (lem-comm-push-CCZ034-sw3-R c4)
  q51 : WsL → Eqn
  q51 c4 = sE 2510 (lem-comm-push-TOFF034-sw3-R c4)
  q52 : WsL → Eqn
  q52 c4 = sE 2531 (lem-comm-push-BOX⟨3·021⟩-sw3-R c4)

-- comm push BOX(0;3421) sw3 R: 8 steps
lem-comm-push-BOX⟨0·3421⟩-sw3-R : WsL → ⟪ (ℓ "乼件") ⟫ʷ ≈ ⟪ (ℓ "伍乼") ⟫ʷ
lem-comm-push-BOX⟨0·3421⟩-sw3-R c4 = derive (ℓ "乼件") (ℓ "伍乼")
  (re 1 1 (ℓ "亠亡仵亡亠仵") ∷
   rw 0 (q50 c4) ∷
   rw 1 (q51 c4) ∷
   rw 2 (q52 c4) ∷
   rw 3 (q51 c4) ∷
   rw 4 (q50 c4) ∷
   rw 5 (q52 c4) ∷
   re 0 6 (ℓ "伍") ∷ []) Eq.refl

private
  q53 : WsL → Eqn
  q53 c4 = sE 2525 (lem-comm-push-BOX⟨0·4321⟩-sw1-R c4)
  q54 : WsL → Eqn
  q54 c4 = sE 2498 (lem-comm-push-SBOX⟨0·4·1·2⟩-sw1-R c4)
  q55 : WsL → Eqn
  q55 c4 = sE 2480 (lem-comm-push-SBOXd⟨0·4·1·2⟩-sw1-R c4)

-- comm push SBOX(0;4;32;1) sw1 R: 7 steps
lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R : WsL → ⟪ (ℓ "乊侸") ⟫ʷ ≈ ⟪ (ℓ "侶乊") ⟫ʷ
lem-comm-push-SBOX⟨0·4·32·1⟩-sw1-R c4 = derive (ℓ "乊侸") (ℓ "侶乊")
  (re 1 1 (ℓ "伍亥侰亥侷") ∷
   rw 0 (q53 c4) ∷
   rw 1 (q38 c4) ∷
   rw 2 (q54 c4) ∷
   rw 3 (q38 c4) ∷
   rw 4 (q55 c4) ∷
   re 0 5 (ℓ "侶") ∷ []) Eq.refl

private
  q56 : WsL → Eqn
  q56 c4 = sE 2533 (lem-comm-push-BOX⟨4·012⟩-sw2-R c4)

-- comm push BOX(0;4312) sw2 R: 12 steps
lem-comm-push-BOX⟨0·4312⟩-sw2-R : WsL → ⟪ (ℓ "乥伋") ⟫ʷ ≈ ⟪ (ℓ "伅乥") ⟫ʷ
lem-comm-push-BOX⟨0·4312⟩-sw2-R c4 = derive (ℓ "乥伋") (ℓ "伅乥")
  (re 1 1 (ℓ "亠亡伊亡亠伊") ∷
   re 1 1 (ℓ "乥亜乥") ∷
   rw 0 (q36 c4) ∷
   re 2 1 (ℓ "乥亝乥") ∷
   rw 1 (q36 c4) ∷
   rw 2 (q56 c4) ∷
   re 4 1 (ℓ "乥亝乥") ∷
   rw 3 (q36 c4) ∷
   re 5 1 (ℓ "乥亜乥") ∷
   rw 4 (q36 c4) ∷
   rw 5 (q56 c4) ∷
   re 0 6 (ℓ "伅") ∷ []) Eq.refl

private
  q57 : WsL → Eqn
  q57 c4 = sE 2463 (lem-comm-push-CCZ024-sw0-R c4)
  q58 : WsL → Eqn
  q58 c4 = sE 2465 (lem-comm-push-TOFF024-sw0-R c4)
  q59 : WsL → Eqn
  q59 c4 = sE 2534 (lem-comm-push-BOX⟨4·013⟩-sw0-R c4)

-- comm push BOX(0;4213) sw0 R: 8 steps
lem-comm-push-BOX⟨0·4213⟩-sw0-R : WsL → ⟪ (ℓ "丫伅") ⟫ʷ ≈ ⟪ (ℓ "伪丫") ⟫ʷ
lem-comm-push-BOX⟨0·4213⟩-sw0-R c4 = derive (ℓ "丫伅") (ℓ "伪丫")
  (re 1 1 (ℓ "亜亝伄亝亜伄") ∷
   rw 0 (q57 c4) ∷
   rw 1 (q58 c4) ∷
   rw 2 (q59 c4) ∷
   rw 3 (q58 c4) ∷
   rw 4 (q57 c4) ∷
   rw 5 (q59 c4) ∷
   re 0 6 (ℓ "伪") ∷ []) Eq.refl

private
  q60 : WsL → Eqn
  q60 c4 = sE 2464 (lem-comm-push-CCZ124-sw0-R c4)
  q61 : WsL → Eqn
  q61 c4 = sE 2513 (lem-comm-push-TOFF214-sw0-R c4)
  q62 : WsL → Eqn
  q62 c4 = sE 2540 (lem-comm-push-BOX⟨4·203⟩-sw0-R c4)

-- comm push BOX(2;4103) sw0 R: 8 steps
lem-comm-push-BOX⟨2·4103⟩-sw0-R : WsL → ⟪ (ℓ "丫佝") ⟫ʷ ≈ ⟪ (ℓ "佔丫") ⟫ʷ
lem-comm-push-BOX⟨2·4103⟩-sw0-R c4 = derive (ℓ "丫佝") (ℓ "佔丫")
  (re 1 1 (ℓ "亨亪作亪亨作") ∷
   rw 0 (q60 c4) ∷
   rw 1 (q61 c4) ∷
   rw 2 (q62 c4) ∷
   rw 3 (q61 c4) ∷
   rw 4 (q60 c4) ∷
   rw 5 (q62 c4) ∷
   re 0 6 (ℓ "佔") ∷ []) Eq.refl

private
  q63 : WsL → Eqn
  q63 c4 = sE 2518 (lem-comm-push-BOX⟨0·2431⟩-sw0-R c4)
  q64 : WsL → Eqn
  q64 c4 = sE 2512 (lem-comm-push-TOFF134-sw0-R c4)
  q65 : WsL → Eqn
  q65 c4 = sE 2494 (lem-comm-push-SBOX⟨0·2·1·3⟩-sw0-R c4)
  q66 : WsL → Eqn
  q66 c4 = sE 2476 (lem-comm-push-SBOXd⟨0·2·1·3⟩-sw0-R c4)

-- comm push SBOX(0;2;43;1) sw0 R: 7 steps
lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R : WsL → ⟪ (ℓ "丫侬") ⟫ʷ ≈ ⟪ (ℓ "侾丫") ⟫ʷ
lem-comm-push-SBOX⟨0·2·43·1⟩-sw0-R c4 = derive (ℓ "丫侬") (ℓ "侾丫")
  (re 1 1 (ℓ "仞亭侪亭侫") ∷
   rw 0 (q63 c4) ∷
   rw 1 (q64 c4) ∷
   rw 2 (q65 c4) ∷
   rw 3 (q64 c4) ∷
   rw 4 (q66 c4) ∷
   re 0 5 (ℓ "侾") ∷ []) Eq.refl

private
  q67 : WsL → Eqn
  q67 c4 = sE 2528 (lem-comm-push-BOX⟨1·2430⟩-sw1-R c4)
  q68 : WsL → Eqn
  q68 c4 = sE 2449 (lem-comm-push-TOFF034-sw1-R c4)
  q69 : WsL → Eqn
  q69 c4 = sE 2502 (lem-comm-push-SBOX⟨1·2·0·3⟩-sw1-R c4)
  q70 : WsL → Eqn
  q70 c4 = sE 2484 (lem-comm-push-SBOXd⟨1·2·0·3⟩-sw1-R c4)

-- comm push SBOX(1;2;43;0) sw1 R: 7 steps
lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R : WsL → ⟪ (ℓ "乊侾") ⟫ʷ ≈ ⟪ (ℓ "俇乊") ⟫ʷ
lem-comm-push-SBOX⟨1·2·43·0⟩-sw1-R c4 = derive (ℓ "乊侾") (ℓ "俇乊")
  (re 1 1 (ℓ "优亡侼亡侽") ∷
   rw 0 (q67 c4) ∷
   rw 1 (q68 c4) ∷
   rw 2 (q69 c4) ∷
   rw 3 (q68 c4) ∷
   rw 4 (q70 c4) ∷
   re 0 5 (ℓ "俇") ∷ []) Eq.refl

private
  q71 : WsL → Eqn
  q71 c4 = sE 2539 (lem-comm-push-BOX⟨4·1230⟩-sw1-R c4)
  q72 : WsL → Eqn
  q72 c4 = wlE 6 c4
  q73 : WsL → Eqn
  q73 c4 = sE 2506 (lem-comm-push-SBOX⟨4·1·0·3⟩-sw1-R c4)
  q74 : WsL → Eqn
  q74 c4 = sE 2488 (lem-comm-push-SBOXd⟨4·1·0·3⟩-sw1-R c4)

-- comm push SBOX(4;1;23;0) sw1 R: 9 steps
lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R : WsL → ⟪ (ℓ "乊俯") ⟫ʷ ≈ ⟪ (ℓ "俷乊") ⟫ʷ
lem-comm-push-SBOX⟨4·1·23·0⟩-sw1-R c4 = derive (ℓ "乊俯") (ℓ "俷乊")
  (re 1 1 (ℓ "侔亙俪亙修") ∷
   rw 0 (q71 c4) ∷
   re 2 1 (ℓ "乊云乊") ∷
   rw 1 (q72 c4) ∷
   rw 2 (q73 c4) ∷
   re 4 1 (ℓ "乊云乊") ∷
   rw 3 (q72 c4) ∷
   rw 4 (q74 c4) ∷
   re 0 5 (ℓ "俷") ∷ []) Eq.refl

private
  q75 : WsL → Eqn
  q75 c4 = sE 2541 (lem-comm-push-BOX⟨4·2130⟩-sw0-R c4)
  q76 : WsL → Eqn
  q76 c4 = wlE 148 c4
  q77 : WsL → Eqn
  q77 c4 = sE 2507 (lem-comm-push-SBOX⟨4·2·0·3⟩-sw0-R c4)
  q78 : WsL → Eqn
  q78 c4 = sE 2489 (lem-comm-push-SBOXd⟨4·2·0·3⟩-sw0-R c4)

-- comm push SBOX(4;2;13;0) sw0 R: 7 steps
lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R : WsL → ⟪ (ℓ "丫俷") ⟫ʷ ≈ ⟪ (ℓ "俵丫") ⟫ʷ
lem-comm-push-SBOX⟨4·2·13·0⟩-sw0-R c4 = derive (ℓ "丫俷") (ℓ "俵丫")
  (re 1 1 (ℓ "侙云俲云俶") ∷
   rw 0 (q75 c4) ∷
   rw 1 (q76 c4) ∷
   rw 2 (q77 c4) ∷
   rw 3 (q76 c4) ∷
   rw 4 (q78 c4) ∷
   re 0 5 (ℓ "俵") ∷ []) Eq.refl

private
  q79 : WsL → Eqn
  q79 c4 = sE 2530 (lem-comm-push-BOX⟨2·0413⟩-sw2-R c4)
  q80 : WsL → Eqn
  q80 c4 = sE 2504 (lem-comm-push-SBOX⟨2·0·3·1⟩-sw2-R c4)
  q81 : WsL → Eqn
  q81 c4 = sE 2486 (lem-comm-push-SBOXd⟨2·0·3·1⟩-sw2-R c4)

-- comm push SBOX(2;0;41;3) sw2 R: 9 steps
lem-comm-push-SBOX⟨2·0·41·3⟩-sw2-R : WsL → ⟪ (ℓ "乥俄") ⟫ʷ ≈ ⟪ (ℓ "俖乥") ⟫ʷ
lem-comm-push-SBOX⟨2·0·41·3⟩-sw2-R c4 = derive (ℓ "乥俄") (ℓ "俖乥")
  (re 1 1 (ℓ "伱亮係亮促") ∷
   rw 0 (q79 c4) ∷
   re 2 1 (ℓ "乥亪乥") ∷
   rw 1 (q36 c4) ∷
   rw 2 (q80 c4) ∷
   re 4 1 (ℓ "乥亪乥") ∷
   rw 3 (q36 c4) ∷
   rw 4 (q81 c4) ∷
   re 0 5 (ℓ "俖") ∷ []) Eq.refl

private
  q82 : WsL → Eqn
  q82 c4 = sE 2532 (lem-comm-push-BOX⟨3·0412⟩-sw3-R c4)
  q83 : WsL → Eqn
  q83 c4 = wlE 4 c4
  q84 : WsL → Eqn
  q84 c4 = eqn (ℓ "俑乼") (ℓ "乼俑") (c₃ (Swap ↑ • CS • Swap ↑) (Swap))
  q85 : WsL → Eqn
  q85 c4 = eqn (ℓ "俕乼") (ℓ "乼俕") (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (Swap))

-- comm push SBOX(3;0;41;2) sw3 R: 9 steps
lem-comm-push-SBOX⟨3·0·41·2⟩-sw3-R : WsL → ⟪ (ℓ "乼俖") ⟫ʷ ≈ ⟪ (ℓ "俨乼") ⟫ʷ
lem-comm-push-SBOX⟨3·0·41·2⟩-sw3-R c4 = derive (ℓ "乼俖") (ℓ "俨乼")
  (re 1 1 (ℓ "佨亪俑亪俕") ∷
   rw 0 (q82 c4) ∷
   re 2 1 (ℓ "乼亦乼") ∷
   rw 1 (q83 c4) ∷
   rw⁻ 2 (q84 c4) ∷
   re 4 1 (ℓ "乼亦乼") ∷
   rw 3 (q83 c4) ∷
   rw⁻ 4 (q85 c4) ∷
   re 0 5 (ℓ "俨") ∷ []) Eq.refl

private
  q86 : WsL → Eqn
  q86 c4 = sE 2522 (lem-comm-push-BOX⟨0·412⟩-sw2-R c4)

-- comm push BOX(4;0312) sw2 R: 12 steps
lem-comm-push-BOX⟨4·0312⟩-sw2-R : WsL → ⟪ (ℓ "乥侐") ⟫ʷ ≈ ⟪ (ℓ "侎乥") ⟫ʷ
lem-comm-push-BOX⟨4·0312⟩-sw2-R c4 = derive (ℓ "乥侐") (ℓ "侎乥")
  (re 1 1 (ℓ "亠亣仹亣亠仹") ∷
   re 1 1 (ℓ "乥亜乥") ∷
   rw 0 (q36 c4) ∷
   re 2 1 (ℓ "乥亟乥") ∷
   rw 1 (q36 c4) ∷
   rw 2 (q86 c4) ∷
   re 4 1 (ℓ "乥亟乥") ∷
   rw 3 (q36 c4) ∷
   re 5 1 (ℓ "乥亜乥") ∷
   rw 4 (q36 c4) ∷
   rw 5 (q86 c4) ∷
   re 0 6 (ℓ "侎") ∷ []) Eq.refl

private
  q87 : WsL → Eqn
  q87 c4 = sE 2536 (lem-comm-push-BOX⟨4·0213⟩-sw1-R c4)
  q88 : WsL → Eqn
  q88 c4 = wlE 150 c4
  q89 : WsL → Eqn
  q89 c4 = sE 2505 (lem-comm-push-SBOX⟨4·0·3·1⟩-sw1-R c4)
  q90 : WsL → Eqn
  q90 c4 = sE 2487 (lem-comm-push-SBOXd⟨4·0·3·1⟩-sw1-R c4)

-- comm push SBOX(4;0;21;3) sw1 R: 7 steps
lem-comm-push-SBOX⟨4·0·21·3⟩-sw1-R : WsL → ⟪ (ℓ "乊俦") ⟫ʷ ≈ ⟪ (ℓ "俢乊") ⟫ʷ
lem-comm-push-SBOX⟨4·0·21·3⟩-sw1-R c4 = derive (ℓ "乊俦") (ℓ "俢乊")
  (re 1 1 (ℓ "侎产俤产俥") ∷
   rw 0 (q87 c4) ∷
   rw 1 (q88 c4) ∷
   rw 2 (q89 c4) ∷
   rw 3 (q88 c4) ∷
   rw 4 (q90 c4) ∷
   re 0 5 (ℓ "俢") ∷ []) Eq.refl

private
  q91 : WsL → Eqn
  q91 c4 = sE 2443 (lem-comm-push-CCZ014-sw0-R c4)
  q92 : WsL → Eqn
  q92 c4 = sE 2468 (lem-comm-push-TOFF401-sw0-R c4)
  q93 : WsL → Eqn
  q93 c4 = sE 2523 (lem-comm-push-BOX⟨0·423⟩-sw0-R c4)

-- comm push BOX(4;0123) sw0 R: 8 steps
lem-comm-push-BOX⟨4·0123⟩-sw0-R : WsL → ⟪ (ℓ "丫侍") ⟫ʷ ≈ ⟪ (ℓ "侒丫") ⟫ʷ
lem-comm-push-BOX⟨4·0123⟩-sw0-R c4 = derive (ℓ "丫侍") (ℓ "侒丫")
  (re 1 1 (ℓ "五亗伆亗五伆") ∷
   rw 0 (q91 c4) ∷
   rw 1 (q92 c4) ∷
   rw 2 (q93 c4) ∷
   rw 3 (q92 c4) ∷
   rw 4 (q91 c4) ∷
   rw 5 (q93 c4) ∷
   re 0 6 (ℓ "侒") ∷ []) Eq.refl
