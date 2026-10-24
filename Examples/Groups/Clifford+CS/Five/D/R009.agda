{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SR009 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.R009 (Sᴰ : SR009) where

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
  lem-comm-push-BOX⟨0·312⟩-sw3-R : WsL → St 2395
  lem-comm-push-BOX⟨0·312⟩-sw3-R = pickᴰ 0 Sᴰ
  lem-comm-push-BOX⟨0·31⟩-sw3-R : WsL → St 2396
  lem-comm-push-BOX⟨0·31⟩-sw3-R = pickᴰ 1 Sᴰ
  lem-comm-push-BOX⟨0·41⟩-sw3-L : WsL → St 2397
  lem-comm-push-BOX⟨0·41⟩-sw3-L = pickᴰ 2 Sᴰ
  lem-comm-push-BOX⟨0·42⟩-sw2-R : WsL → St 2398
  lem-comm-push-BOX⟨0·42⟩-sw2-R = pickᴰ 3 Sᴰ
  lem-comm-push-BOX⟨0·43⟩-sw2-L : WsL → St 2399
  lem-comm-push-BOX⟨0·43⟩-sw2-L = pickᴰ 4 Sᴰ
  lem-comm-push-BOX⟨4·02⟩-sw2-R : WsL → St 2400
  lem-comm-push-BOX⟨4·02⟩-sw2-R = pickᴰ 5 Sᴰ
  lem-comm-push-BOX⟨4·03⟩-sw0-R : WsL → St 2401
  lem-comm-push-BOX⟨4·03⟩-sw0-R = pickᴰ 6 Sᴰ
  lem-comm-push-CCZ014-sw2-L : WsL → St 2402
  lem-comm-push-CCZ014-sw2-L = pickᴰ 7 Sᴰ
  lem-comm-push-CCZ024-sw0-L : WsL → St 2403
  lem-comm-push-CCZ024-sw0-L = pickᴰ 8 Sᴰ
  lem-comm-push-CCZ034-sw0-L : WsL → St 2404
  lem-comm-push-CCZ034-sw0-L = pickᴰ 9 Sᴰ
  lem-comm-push-CCZ034-sw1-L : WsL → St 2405
  lem-comm-push-CCZ034-sw1-L = pickᴰ 10 Sᴰ
  lem-comm-push-TOFF023-sw3-L : WsL → St 2406
  lem-comm-push-TOFF023-sw3-L = pickᴰ 11 Sᴰ
  lem-comm-push-TOFF024-sw0-L : WsL → St 2407
  lem-comm-push-TOFF024-sw0-L = pickᴰ 12 Sᴰ
  lem-comm-push-TOFF024-sw3-L : WsL → St 2408
  lem-comm-push-TOFF024-sw3-L = pickᴰ 13 Sᴰ
  lem-comm-push-TOFF034-sw0-L : WsL → St 2409
  lem-comm-push-TOFF034-sw0-L = pickᴰ 14 Sᴰ
  lem-comm-push-TOFF034-sw1-L : WsL → St 2410
  lem-comm-push-TOFF034-sw1-L = pickᴰ 15 Sᴰ
  lem-comm-push-TOFF204-sw0-L : WsL → St 2411
  lem-comm-push-TOFF204-sw0-L = pickᴰ 16 Sᴰ
  lem-comm-push-TOFF304-sw0-L : WsL → St 2412
  lem-comm-push-TOFF304-sw0-L = pickᴰ 17 Sᴰ
  lem-comm-push-TOFF304-sw1-L : WsL → St 2413
  lem-comm-push-TOFF304-sw1-L = pickᴰ 18 Sᴰ
  lem-comm-push-TOFF401-sw2-L : WsL → St 2414
  lem-comm-push-TOFF401-sw2-L = pickᴰ 19 Sᴰ
  lem-comm-push-TOFF402-sw0-L : WsL → St 2415
  lem-comm-push-TOFF402-sw0-L = pickᴰ 20 Sᴰ
  lem-comm-push-BOX⟨0·123⟩-sw0-L : WsL → St 2416
  lem-comm-push-BOX⟨0·123⟩-sw0-L = pickᴰ 21 Sᴰ
  lem-comm-push-BOX⟨0·213⟩-sw1-L : WsL → St 2417
  lem-comm-push-BOX⟨0·213⟩-sw1-L = pickᴰ 22 Sᴰ
  lem-comm-push-BOX⟨1·023⟩-sw2-L : WsL → St 2418
  lem-comm-push-BOX⟨1·023⟩-sw2-L = pickᴰ 23 Sᴰ
  lem-comm-push-BOX⟨1·032⟩-sw1-L : WsL → St 2419
  lem-comm-push-BOX⟨1·032⟩-sw1-L = pickᴰ 24 Sᴰ
  lem-comm-push-BOX⟨1·032⟩-sw2-R : WsL → St 2420
  lem-comm-push-BOX⟨1·032⟩-sw2-R = pickᴰ 25 Sᴰ
  lem-comm-push-BOX⟨2·031⟩-sw1-R : WsL → St 2421
  lem-comm-push-BOX⟨2·031⟩-sw1-R = pickᴰ 26 Sᴰ
  lem-comm-push-CCZ014-sw0-L : WsL → St 2422
  lem-comm-push-CCZ014-sw0-L = pickᴰ 27 Sᴰ
  lem-comm-push-CCZ014-sw2-R : WsL → St 2423
  lem-comm-push-CCZ014-sw2-R = pickᴰ 28 Sᴰ
  lem-comm-push-CCZ023-sw3-L : WsL → St 2424
  lem-comm-push-CCZ023-sw3-L = pickᴰ 29 Sᴰ
  lem-comm-push-CCZ024-sw3-L : WsL → St 2425
  lem-comm-push-CCZ024-sw3-L = pickᴰ 30 Sᴰ
  lem-comm-push-TOFF014-sw2-L : WsL → St 2426
  lem-comm-push-TOFF014-sw2-L = pickᴰ 31 Sᴰ
  lem-comm-push-TOFF014-sw2-R : WsL → St 2427
  lem-comm-push-TOFF014-sw2-R = pickᴰ 32 Sᴰ
  lem-comm-push-TOFF104-sw0-L : WsL → St 2428
  lem-comm-push-TOFF104-sw0-L = pickᴰ 33 Sᴰ
  lem-comm-push-TOFF104-sw2-L : WsL → St 2429
  lem-comm-push-TOFF104-sw2-L = pickᴰ 34 Sᴰ
  lem-comm-push-TOFF203-sw3-L : WsL → St 2430
  lem-comm-push-TOFF203-sw3-L = pickᴰ 35 Sᴰ
  lem-comm-push-TOFF204-sw3-L : WsL → St 2431
  lem-comm-push-TOFF204-sw3-L = pickᴰ 36 Sᴰ
  lem-comm-push-TOFF302-sw3-L : WsL → St 2432
  lem-comm-push-TOFF302-sw3-L = pickᴰ 37 Sᴰ
  lem-comm-push-TOFF402-sw3-L : WsL → St 2433
  lem-comm-push-TOFF402-sw3-L = pickᴰ 38 Sᴰ
  lem-comm-push-TOFF403-sw0-L : WsL → St 2434
  lem-comm-push-TOFF403-sw0-L = pickᴰ 39 Sᴰ
  lem-comm-push-TOFF403-sw1-L : WsL → St 2435
  lem-comm-push-TOFF403-sw1-L = pickᴰ 40 Sᴰ
  lem-comm-push-BOX⟨0·123⟩-sw1-R : WsL → St 2436
  lem-comm-push-BOX⟨0·123⟩-sw1-R = pickᴰ 41 Sᴰ
  lem-comm-push-BOX⟨1·023⟩-sw0-R : WsL → St 2437
  lem-comm-push-BOX⟨1·023⟩-sw0-R = pickᴰ 42 Sᴰ
  lem-comm-push-BOX⟨2·031⟩-sw2-R : WsL → St 2438
  lem-comm-push-BOX⟨2·031⟩-sw2-R = pickᴰ 43 Sᴰ
  lem-comm-push-BOX⟨2·4103⟩-sw1-L : WsL → St 2439
  lem-comm-push-BOX⟨2·4103⟩-sw1-L = pickᴰ 44 Sᴰ
  lem-comm-push-BOX⟨3·021⟩-sw2-L : WsL → St 2440
  lem-comm-push-BOX⟨3·021⟩-sw2-L = pickᴰ 45 Sᴰ
  lem-comm-push-BOX⟨4·012⟩-sw1-L : WsL → St 2441
  lem-comm-push-BOX⟨4·012⟩-sw1-L = pickᴰ 46 Sᴰ
  lem-comm-push-BOX⟨4·021⟩-sw1-R : WsL → St 2442
  lem-comm-push-BOX⟨4·021⟩-sw1-R = pickᴰ 47 Sᴰ
  lem-comm-push-CCZ014-sw0-R : WsL → St 2443
  lem-comm-push-CCZ014-sw0-R = pickᴰ 48 Sᴰ
  lem-comm-push-CCZ023-sw3-R : WsL → St 2444
  lem-comm-push-CCZ023-sw3-R = pickᴰ 49 Sᴰ
  lem-comm-push-CCZ034-sw1-R : WsL → St 2445
  lem-comm-push-CCZ034-sw1-R = pickᴰ 50 Sᴰ
  lem-comm-push-CCZ034-sw3-R : WsL → St 2446
  lem-comm-push-CCZ034-sw3-R = pickᴰ 51 Sᴰ
  lem-comm-push-CCZ124-sw0-L : WsL → St 2447
  lem-comm-push-CCZ124-sw0-L = pickᴰ 52 Sᴰ
  lem-comm-push-TOFF014-sw0-R : WsL → St 2448
  lem-comm-push-TOFF014-sw0-R = pickᴰ 53 Sᴰ
  lem-comm-push-TOFF034-sw1-R : WsL → St 2449
  lem-comm-push-TOFF034-sw1-R = pickᴰ 54 Sᴰ
  lem-comm-push-TOFF302-sw3-R : WsL → St 2450
  lem-comm-push-TOFF302-sw3-R = pickᴰ 55 Sᴰ
  lem-comm-push-TOFF401-sw0-L : WsL → St 2451
  lem-comm-push-TOFF401-sw0-L = pickᴰ 56 Sᴰ
  lem-comm-push-TOFF412-sw0-L : WsL → St 2452
  lem-comm-push-TOFF412-sw0-L = pickᴰ 57 Sᴰ
  lem-comm-push-BOX⟨0·213⟩-sw2-R : WsL → St 2453
  lem-comm-push-BOX⟨0·213⟩-sw2-R = pickᴰ 58 Sᴰ
  lem-comm-push-BOX⟨0·413⟩-sw1-R : WsL → St 2454
  lem-comm-push-BOX⟨0·413⟩-sw1-R = pickᴰ 59 Sᴰ
  lem-comm-push-BOX⟨1·4203⟩-sw1-R : WsL → St 2455
  lem-comm-push-BOX⟨1·4203⟩-sw1-R = pickᴰ 60 Sᴰ
  lem-comm-push-BOX⟨1·430⟩-sw1-R : WsL → St 2456
  lem-comm-push-BOX⟨1·430⟩-sw1-R = pickᴰ 61 Sᴰ
  lem-comm-push-BOX⟨2·031⟩-sw0-R : WsL → St 2457
  lem-comm-push-BOX⟨2·031⟩-sw0-R = pickᴰ 62 Sᴰ
  lem-comm-push-BOX⟨2·130⟩-sw1-R : WsL → St 2458
  lem-comm-push-BOX⟨2·130⟩-sw1-R = pickᴰ 63 Sᴰ
  lem-comm-push-BOX⟨2·1430⟩-sw2-R : WsL → St 2459
  lem-comm-push-BOX⟨2·1430⟩-sw2-R = pickᴰ 64 Sᴰ
  lem-comm-push-BOX⟨2·430⟩-sw0-R : WsL → St 2460
  lem-comm-push-BOX⟨2·430⟩-sw0-R = pickᴰ 65 Sᴰ
  lem-comm-push-BOX⟨3·1420⟩-sw3-R : WsL → St 2461
  lem-comm-push-BOX⟨3·1420⟩-sw3-R = pickᴰ 66 Sᴰ
  lem-comm-push-BOX⟨4·1320⟩-sw2-R : WsL → St 2462
  lem-comm-push-BOX⟨4·1320⟩-sw2-R = pickᴰ 67 Sᴰ
  lem-comm-push-CCZ024-sw0-R : WsL → St 2463
  lem-comm-push-CCZ024-sw0-R = pickᴰ 68 Sᴰ
  lem-comm-push-CCZ124-sw0-R : WsL → St 2464
  lem-comm-push-CCZ124-sw0-R = pickᴰ 69 Sᴰ
  lem-comm-push-TOFF024-sw0-R : WsL → St 2465
  lem-comm-push-TOFF024-sw0-R = pickᴰ 70 Sᴰ
  lem-comm-push-TOFF024-sw3-R : WsL → St 2466
  lem-comm-push-TOFF024-sw3-R = pickᴰ 71 Sᴰ
  lem-comm-push-TOFF304-sw3-R : WsL → St 2467
  lem-comm-push-TOFF304-sw3-R = pickᴰ 72 Sᴰ
  lem-comm-push-TOFF401-sw0-R : WsL → St 2468
  lem-comm-push-TOFF401-sw0-R = pickᴰ 73 Sᴰ
  lem-comm-push-TOFF401-sw2-R : WsL → St 2469
  lem-comm-push-TOFF401-sw2-R = pickᴰ 74 Sᴰ
  lem-comm-push-TOFF402-sw0-R : WsL → St 2470
  lem-comm-push-TOFF402-sw0-R = pickᴰ 75 Sᴰ
  lem-comm-push-TOFF412-sw0-R : WsL → St 2471
  lem-comm-push-TOFF412-sw0-R = pickᴰ 76 Sᴰ

private
  q1 : WsL → Eqn
  q1 c4 = wlE 6 c4
  q2 : WsL → Eqn
  q2 c4 = sE 2405 (lem-comm-push-CCZ034-sw1-L c4)
  q3 : WsL → Eqn
  q3 c4 = wlE 18 c4
  q4 : WsL → Eqn
  q4 c4 = sE 2404 (lem-comm-push-CCZ034-sw0-L c4)

-- resp CCZ034 at 2: 4 steps
lem-resp-CCZ034-at-2 : WsL → ⟪ (ℓ "亠") ⟫ʷ ≈ ⟪ (ℓ "乊丫京丫乊") ⟫ʷ
lem-resp-CCZ034-at-2 c4 = derive (ℓ "亠") (ℓ "乊丫京丫乊")
  (rw⁻ 1 (q1 c4) ∷
   rw 0 (q2 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 1 (q4 c4) ∷ []) Eq.refl

-- resp CCZ034 at 1: 2 steps
lem-resp-CCZ034-at-1 : WsL → ⟪ (ℓ "亠") ⟫ʷ ≈ ⟪ (ℓ "丫京丫") ⟫ʷ
lem-resp-CCZ034-at-1 c4 = derive (ℓ "亠") (ℓ "丫京丫")
  (rw⁻ 1 (q3 c4) ∷
   rw 0 (q4 c4) ∷ []) Eq.refl

private
  q5 : WsL → Eqn
  q5 c4 = sE 2409 (lem-comm-push-TOFF034-sw0-L c4)

-- resp TOFF034 at 1: 2 steps
lem-resp-TOFF034-at-1 : WsL → ⟪ (ℓ "亡") ⟫ʷ ≈ ⟪ (ℓ "丫亭丫") ⟫ʷ
lem-resp-TOFF034-at-1 c4 = derive (ℓ "亡") (ℓ "丫亭丫")
  (rw⁻ 1 (q3 c4) ∷
   rw 0 (q5 c4) ∷ []) Eq.refl

private
  q6 : WsL → Eqn
  q6 c4 = sE 2410 (lem-comm-push-TOFF034-sw1-L c4)

-- resp TOFF034 at 2: 4 steps
lem-resp-TOFF034-at-2 : WsL → ⟪ (ℓ "亡") ⟫ʷ ≈ ⟪ (ℓ "乊丫亭丫乊") ⟫ʷ
lem-resp-TOFF034-at-2 c4 = derive (ℓ "亡") (ℓ "乊丫亭丫乊")
  (rw⁻ 1 (q1 c4) ∷
   rw 0 (q6 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 1 (q5 c4) ∷ []) Eq.refl

private
  q7 : WsL → Eqn
  q7 c4 = sE 2403 (lem-comm-push-CCZ024-sw0-L c4)

-- resp CCZ014 at 2: 5 steps
lem-resp-CCZ014-at-2 : WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "乊丫亨丫乊") ⟫ʷ
lem-resp-CCZ014-at-2 c4 = derive (ℓ "五") (ℓ "乊丫亨丫乊")
  (rw⁻ 1 (q1 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "亜") ∷
   rw⁻ 2 (q3 c4) ∷
   rw 1 (q7 c4) ∷ []) Eq.refl

private
  q8 : WsL → Eqn
  q8 c4 = sE 2411 (lem-comm-push-TOFF204-sw0-L c4)

-- resp TOFF204 at 1: 2 steps
lem-resp-TOFF204-at-1 : WsL → ⟪ (ℓ "亞") ⟫ʷ ≈ ⟪ (ℓ "丫亪丫") ⟫ʷ
lem-resp-TOFF204-at-1 c4 = derive (ℓ "亞") (ℓ "丫亪丫")
  (rw⁻ 1 (q3 c4) ∷
   rw 0 (q8 c4) ∷ []) Eq.refl

-- resp CCZ024 at 1: 2 steps
lem-resp-CCZ024-at-1 : WsL → ⟪ (ℓ "亜") ⟫ʷ ≈ ⟪ (ℓ "丫亨丫") ⟫ʷ
lem-resp-CCZ024-at-1 c4 = derive (ℓ "亜") (ℓ "丫亨丫")
  (rw⁻ 1 (q3 c4) ∷
   rw 0 (q7 c4) ∷ []) Eq.refl

private
  q9 : WsL → Eqn
  q9 c4 = wlE 3 c4

-- resp CCZ024 at 3: 7 steps
lem-resp-CCZ024-at-3 : WsL → ⟪ (ℓ "亜") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫京丫乊乥") ⟫ʷ
lem-resp-CCZ024-at-3 c4 = derive (ℓ "亜") (ℓ "乥乊丫京丫乊乥")
  (rw⁻ 1 (q9 c4) ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (ℓ "亠") ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw 2 (q4 c4) ∷ []) Eq.refl

private
  q10 : WsL → Eqn
  q10 c4 = sE 2402 (lem-comm-push-CCZ014-sw2-L c4)

-- resp CCZ014 at 3: 7 steps
lem-resp-CCZ014-at-3 : WsL → ⟪ (ℓ "五") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫亨丫乊乥") ⟫ʷ
lem-resp-CCZ014-at-3 c4 = derive (ℓ "五") (ℓ "乥乊丫亨丫乊乥")
  (rw⁻ 1 (q9 c4) ∷
   rw 0 (q10 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (ℓ "亜") ∷
   rw⁻ 3 (q3 c4) ∷
   rw 2 (q7 c4) ∷ []) Eq.refl

private
  q11 : WsL → Eqn
  q11 c4 = sE 2407 (lem-comm-push-TOFF024-sw0-L c4)

-- resp TOFF014 at 2: 5 steps
lem-resp-TOFF014-at-2 : WsL → ⟪ (ℓ "井") ⟫ʷ ≈ ⟪ (ℓ "乊丫亩丫乊") ⟫ʷ
lem-resp-TOFF014-at-2 c4 = derive (ℓ "井") (ℓ "乊丫亩丫乊")
  (rw⁻ 1 (q1 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "亝") ∷
   rw⁻ 2 (q3 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

-- resp TOFF024 at 1: 2 steps
lem-resp-TOFF024-at-1 : WsL → ⟪ (ℓ "亝") ⟫ʷ ≈ ⟪ (ℓ "丫亩丫") ⟫ʷ
lem-resp-TOFF024-at-1 c4 = derive (ℓ "亝") (ℓ "丫亩丫")
  (rw⁻ 1 (q3 c4) ∷
   rw 0 (q11 c4) ∷ []) Eq.refl

-- resp TOFF024 at 3: 7 steps
lem-resp-TOFF024-at-3 : WsL → ⟪ (ℓ "亝") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫亭丫乊乥") ⟫ʷ
lem-resp-TOFF024-at-3 c4 = derive (ℓ "亝") (ℓ "乥乊丫亭丫乊乥")
  (rw⁻ 1 (q9 c4) ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (ℓ "亡") ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q6 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw 2 (q5 c4) ∷ []) Eq.refl

private
  q12 : WsL → Eqn
  q12 c4 = sE 2414 (lem-comm-push-TOFF401-sw2-L c4)
  q13 : WsL → Eqn
  q13 c4 = sE 2415 (lem-comm-push-TOFF402-sw0-L c4)

-- resp TOFF401 at 3: 7 steps
lem-resp-TOFF401-at-3 : WsL → ⟪ (ℓ "亗") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫享丫乊乥") ⟫ʷ
lem-resp-TOFF401-at-3 c4 = derive (ℓ "亗") (ℓ "乥乊丫享丫乊乥")
  (rw⁻ 1 (q9 c4) ∷
   rw 0 (q12 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (ℓ "亟") ∷
   rw⁻ 3 (q3 c4) ∷
   rw 2 (q13 c4) ∷ []) Eq.refl

private
  q14 : WsL → Eqn
  q14 c4 = sE 2413 (lem-comm-push-TOFF304-sw1-L c4)
  q15 : WsL → Eqn
  q15 c4 = sE 2412 (lem-comm-push-TOFF304-sw0-L c4)

-- resp TOFF304 at 2: 4 steps
lem-resp-TOFF304-at-2 : WsL → ⟪ (ℓ "亢") ⟫ʷ ≈ ⟪ (ℓ "乊丫亮丫乊") ⟫ʷ
lem-resp-TOFF304-at-2 c4 = derive (ℓ "亢") (ℓ "乊丫亮丫乊")
  (rw⁻ 1 (q1 c4) ∷
   rw 0 (q14 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 1 (q15 c4) ∷ []) Eq.refl

private
  q16 : WsL → Eqn
  q16 c4 = sE 2406 (lem-comm-push-TOFF023-sw3-L c4)
  q17 : WsL → Eqn
  q17 c4 = wlE 29 c4
  q18 : WsL → Eqn
  q18 c4 = wlE 4 c4
  q19 : WsL → Eqn
  q19 c4 = wlE 9 c4
  q20 : WsL → Eqn
  q20 c4 = eqn (ℓ "亍乺") (ℓ "乺亍") (c₃ (Toff) (CS • CS • CS))
  q21 : WsL → Eqn
  q21 c4 = wlE 12 c4
  q22 : WsL → Eqn
  q22 c4 = wlE 28 c4
  q23 : WsL → Eqn
  q23 c4 = sE 2408 (lem-comm-push-TOFF024-sw3-L c4)

-- comm TOFF023 CSd14: 23 steps
lem-comm-TOFF023-CSd14 : WsL → ⟪ (ℓ "亙乖") ⟫ʷ ≈ ⟪ (ℓ "乖亙") ⟫ʷ
lem-comm-TOFF023-CSd14 c4 = derive (ℓ "亙乖") (ℓ "乖亙")
  (re 1 1 (ℓ "乼乥么乥乼") ∷
   rw 0 (q16 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (ℓ "亡") ∷
   re 2 1 (ℓ "乥乊乼乥亍乥乼乊乥") ∷
   rw⁻ 12 (q9 c4) ∷
   re 10 3 (ℓ "乏") ∷
   rw⁻ 9 (q17 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   re 8 3 (ℓ "乪") ∷
   rw⁻ 7 (q19 c4) ∷
   rw 6 (q20 c4) ∷
   rw⁻ 5 (q21 c4) ∷
   re 5 1 (ℓ "乼乣乼") ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q22 c4) ∷
   re 3 1 (ℓ "乥么乥") ∷
   rw 2 (q9 c4) ∷
   re 3 9 (ℓ "亡") ∷
   re 3 1 (ℓ "乥亝乥") ∷
   rw 5 (q9 c4) ∷
   rw 4 (q23 c4) ∷
   re 0 5 (ℓ "乖") ∷ []) Eq.refl

private
  q24 : WsL → Eqn
  q24 c4 = sE 2435 (lem-comm-push-TOFF403-sw1-L c4)
  q25 : WsL → Eqn
  q25 c4 = sE 2434 (lem-comm-push-TOFF403-sw0-L c4)

-- resp TOFF402 at 3: 7 steps
lem-resp-TOFF402-at-3 : WsL → ⟪ (ℓ "亟") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫亯丫乊乥") ⟫ʷ
lem-resp-TOFF402-at-3 c4 = derive (ℓ "亟") (ℓ "乥乊丫亯丫乊乥")
  (rw⁻ 1 (q9 c4) ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (ℓ "亣") ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q24 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw 2 (q25 c4) ∷ []) Eq.refl

-- resp TOFF304 at 1: 2 steps
lem-resp-TOFF304-at-1 : WsL → ⟪ (ℓ "亢") ⟫ʷ ≈ ⟪ (ℓ "丫亮丫") ⟫ʷ
lem-resp-TOFF304-at-1 c4 = derive (ℓ "亢") (ℓ "丫亮丫")
  (rw⁻ 1 (q3 c4) ∷
   rw 0 (q15 c4) ∷ []) Eq.refl

-- resp TOFF401 at 2: 5 steps
lem-resp-TOFF401-at-2 : WsL → ⟪ (ℓ "亗") ⟫ʷ ≈ ⟪ (ℓ "乊丫享丫乊") ⟫ʷ
lem-resp-TOFF401-at-2 c4 = derive (ℓ "亗") (ℓ "乊丫享丫乊")
  (rw⁻ 1 (q1 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "亟") ∷
   rw⁻ 2 (q3 c4) ∷
   rw 1 (q13 c4) ∷ []) Eq.refl

-- resp TOFF204 at 3: 7 steps
lem-resp-TOFF204-at-3 : WsL → ⟪ (ℓ "亞") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫亮丫乊乥") ⟫ʷ
lem-resp-TOFF204-at-3 c4 = derive (ℓ "亞") (ℓ "乥乊丫亮丫乊乥")
  (rw⁻ 1 (q9 c4) ∷
   rw⁻ 0 (q9 c4) ∷
   re 1 3 (ℓ "亢") ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q14 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw 2 (q15 c4) ∷ []) Eq.refl

private
  q26 : WsL → Eqn
  q26 c4 = sE 2426 (lem-comm-push-TOFF014-sw2-L c4)

-- resp TOFF014 at 3: 7 steps
lem-resp-TOFF014-at-3 : WsL → ⟪ (ℓ "井") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫亩丫乊乥") ⟫ʷ
lem-resp-TOFF014-at-3 c4 = derive (ℓ "井") (ℓ "乥乊丫亩丫乊乥")
  (rw⁻ 1 (q9 c4) ∷
   rw 0 (q26 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (ℓ "亝") ∷
   rw⁻ 3 (q3 c4) ∷
   rw 2 (q11 c4) ∷ []) Eq.refl

-- resp TOFF403 at 2: 4 steps
lem-resp-TOFF403-at-2 : WsL → ⟪ (ℓ "亣") ⟫ʷ ≈ ⟪ (ℓ "乊丫亯丫乊") ⟫ʷ
lem-resp-TOFF403-at-2 c4 = derive (ℓ "亣") (ℓ "乊丫亯丫乊")
  (rw⁻ 1 (q1 c4) ∷
   rw 0 (q24 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 1 (q25 c4) ∷ []) Eq.refl

-- resp TOFF104 at 2: 5 steps
lem-resp-TOFF104-at-2 : WsL → ⟪ (ℓ "亖") ⟫ʷ ≈ ⟪ (ℓ "乊丫亪丫乊") ⟫ʷ
lem-resp-TOFF104-at-2 c4 = derive (ℓ "亖") (ℓ "乊丫亪丫乊")
  (rw⁻ 1 (q1 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "亞") ∷
   rw⁻ 2 (q3 c4) ∷
   rw 1 (q8 c4) ∷ []) Eq.refl

private
  q27 : WsL → Eqn
  q27 c4 = sE 2429 (lem-comm-push-TOFF104-sw2-L c4)

-- resp TOFF104 at 3: 7 steps
lem-resp-TOFF104-at-3 : WsL → ⟪ (ℓ "亖") ⟫ʷ ≈ ⟪ (ℓ "乥乊丫亪丫乊乥") ⟫ʷ
lem-resp-TOFF104-at-3 c4 = derive (ℓ "亖") (ℓ "乥乊丫亪丫乊乥")
  (rw⁻ 1 (q9 c4) ∷
   rw 0 (q27 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (ℓ "亞") ∷
   rw⁻ 3 (q3 c4) ∷
   rw 2 (q8 c4) ∷ []) Eq.refl

-- resp TOFF402 at 1: 2 steps
lem-resp-TOFF402-at-1 : WsL → ⟪ (ℓ "亟") ⟫ʷ ≈ ⟪ (ℓ "丫享丫") ⟫ʷ
lem-resp-TOFF402-at-1 c4 = derive (ℓ "亟") (ℓ "丫享丫")
  (rw⁻ 1 (q3 c4) ∷
   rw 0 (q13 c4) ∷ []) Eq.refl

-- resp TOFF403 at 1: 2 steps
lem-resp-TOFF403-at-1 : WsL → ⟪ (ℓ "亣") ⟫ʷ ≈ ⟪ (ℓ "丫亯丫") ⟫ʷ
lem-resp-TOFF403-at-1 c4 = derive (ℓ "亣") (ℓ "丫亯丫")
  (rw⁻ 1 (q3 c4) ∷
   rw 0 (q25 c4) ∷ []) Eq.refl

private
  q28 : WsL → Eqn
  q28 c4 = sE 2430 (lem-comm-push-TOFF203-sw3-L c4)
  q29 : WsL → Eqn
  q29 c4 = eqn (ℓ "于乺") (ℓ "乺于") (c₃ (K ↑ • CCZ • K ↑ • iI) (CS • CS • CS))
  q30 : WsL → Eqn
  q30 c4 = sE 2431 (lem-comm-push-TOFF204-sw3-L c4)

-- comm TOFF203 CSd14: 23 steps
lem-comm-TOFF203-CSd14 : WsL → ⟪ (ℓ "亚乖") ⟫ʷ ≈ ⟪ (ℓ "乖亚") ⟫ʷ
lem-comm-TOFF203-CSd14 c4 = derive (ℓ "亚乖") (ℓ "乖亚")
  (re 1 1 (ℓ "乼乥么乥乼") ∷
   rw 0 (q28 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (ℓ "亢") ∷
   re 2 1 (ℓ "乥乊乼乥于乥乼乊乥") ∷
   rw⁻ 12 (q9 c4) ∷
   re 10 3 (ℓ "乏") ∷
   rw⁻ 9 (q17 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   re 8 3 (ℓ "乪") ∷
   rw⁻ 7 (q19 c4) ∷
   rw 6 (q29 c4) ∷
   rw⁻ 5 (q21 c4) ∷
   re 5 1 (ℓ "乼乣乼") ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q22 c4) ∷
   re 3 1 (ℓ "乥么乥") ∷
   rw 2 (q9 c4) ∷
   re 3 9 (ℓ "亢") ∷
   re 3 1 (ℓ "乥亞乥") ∷
   rw 5 (q9 c4) ∷
   rw 4 (q30 c4) ∷
   re 0 5 (ℓ "乖") ∷ []) Eq.refl

private
  q31 : WsL → Eqn
  q31 c4 = sE 2424 (lem-comm-push-CCZ023-sw3-L c4)
  q32 : WsL → Eqn
  q32 c4 = wlE 94 c4
  q33 : WsL → Eqn
  q33 c4 = wlE 91 c4
  q34 : WsL → Eqn
  q34 c4 = eqn (ℓ "二亊") (ℓ "亊二") (c₃ (CCZ) (CK₁₀))
  q35 : WsL → Eqn
  q35 c4 = wlE 90 c4
  q36 : WsL → Eqn
  q36 c4 = wlE 95 c4
  q37 : WsL → Eqn
  q37 c4 = sE 2425 (lem-comm-push-CCZ024-sw3-L c4)

-- comm CCZ023 CK41: 23 steps
lem-comm-CCZ023-CK41 : WsL → ⟪ (ℓ "亘亄") ⟫ʷ ≈ ⟪ (ℓ "亄亘") ⟫ʷ
lem-comm-CCZ023-CK41 c4 = derive (ℓ "亘亄") (ℓ "亄亘")
  (re 1 1 (ℓ "乼乥习乥乼") ∷
   rw 0 (q31 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (ℓ "亠") ∷
   re 2 1 (ℓ "乥乊乼乥二乥乼乊乥") ∷
   rw⁻ 12 (q9 c4) ∷
   re 10 3 (ℓ "乴") ∷
   rw⁻ 9 (q32 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   re 8 3 (ℓ "亇") ∷
   rw⁻ 7 (q33 c4) ∷
   rw 6 (q34 c4) ∷
   rw⁻ 5 (q35 c4) ∷
   re 5 1 (ℓ "乼乷乼") ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q36 c4) ∷
   re 3 1 (ℓ "乥习乥") ∷
   rw 2 (q9 c4) ∷
   re 3 9 (ℓ "亠") ∷
   re 3 1 (ℓ "乥亜乥") ∷
   rw 5 (q9 c4) ∷
   rw 4 (q37 c4) ∷
   re 0 5 (ℓ "亄") ∷ []) Eq.refl

private
  q38 : WsL → Eqn
  q38 c4 = eqn (ℓ "亍亊") (ℓ "亊亍") (c₃ (Toff) (CK₁₀))

-- comm TOFF023 CK41: 23 steps
lem-comm-TOFF023-CK41 : WsL → ⟪ (ℓ "亙亄") ⟫ʷ ≈ ⟪ (ℓ "亄亙") ⟫ʷ
lem-comm-TOFF023-CK41 c4 = derive (ℓ "亙亄") (ℓ "亄亙")
  (re 1 1 (ℓ "乼乥习乥乼") ∷
   rw 0 (q16 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (ℓ "亡") ∷
   re 2 1 (ℓ "乥乊乼乥亍乥乼乊乥") ∷
   rw⁻ 12 (q9 c4) ∷
   re 10 3 (ℓ "乴") ∷
   rw⁻ 9 (q32 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   re 8 3 (ℓ "亇") ∷
   rw⁻ 7 (q33 c4) ∷
   rw 6 (q38 c4) ∷
   rw⁻ 5 (q35 c4) ∷
   re 5 1 (ℓ "乼乷乼") ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q36 c4) ∷
   re 3 1 (ℓ "乥习乥") ∷
   rw 2 (q9 c4) ∷
   re 3 9 (ℓ "亡") ∷
   re 3 1 (ℓ "乥亝乥") ∷
   rw 5 (q9 c4) ∷
   rw 4 (q23 c4) ∷
   re 0 5 (ℓ "亄") ∷ []) Eq.refl

private
  q39 : WsL → Eqn
  q39 c4 = wlE 22 c4
  q40 : WsL → Eqn
  q40 c4 = wlE 21 c4
  q41 : WsL → Eqn
  q41 c4 = eqn (ℓ "亍乽") (ℓ "乽亍") (c₃ (Toff) (CX₀₁))
  q42 : WsL → Eqn
  q42 c4 = wlE 20 c4
  q43 : WsL → Eqn
  q43 c4 = wlE 19 c4

-- comm TOFF023 CX14: 23 steps
lem-comm-TOFF023-CX14 : WsL → ⟪ (ℓ "亙乙") ⟫ʷ ≈ ⟪ (ℓ "乙亙") ⟫ʷ
lem-comm-TOFF023-CX14 c4 = derive (ℓ "亙乙") (ℓ "乙亙")
  (re 1 1 (ℓ "乼乥之乥乼") ∷
   rw 0 (q16 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (ℓ "亡") ∷
   re 2 1 (ℓ "乥乊乼乥亍乥乼乊乥") ∷
   rw⁻ 12 (q9 c4) ∷
   re 10 3 (ℓ "乒") ∷
   rw⁻ 9 (q39 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   re 8 3 (ℓ "乭") ∷
   rw⁻ 7 (q40 c4) ∷
   rw 6 (q41 c4) ∷
   rw⁻ 5 (q42 c4) ∷
   re 5 1 (ℓ "乼书乼") ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   re 3 1 (ℓ "乥之乥") ∷
   rw 2 (q9 c4) ∷
   re 3 9 (ℓ "亡") ∷
   re 3 1 (ℓ "乥亝乥") ∷
   rw 5 (q9 c4) ∷
   rw 4 (q23 c4) ∷
   re 0 5 (ℓ "乙") ∷ []) Eq.refl

private
  q44 : WsL → Eqn
  q44 c4 = wlE 47 c4
  q45 : WsL → Eqn
  q45 c4 = wlE 8 c4
  q46 : WsL → Eqn
  q46 c4 = eqn (ℓ "亍乹") (ℓ "乹亍") (c₃ (Toff) (CS))
  q47 : WsL → Eqn
  q47 c4 = wlE 11 c4
  q48 : WsL → Eqn
  q48 c4 = wlE 46 c4

-- comm TOFF023 CS14: 23 steps
lem-comm-TOFF023-CS14 : WsL → ⟪ (ℓ "亙乕") ⟫ʷ ≈ ⟪ (ℓ "乕亙") ⟫ʷ
lem-comm-TOFF023-CS14 c4 = derive (ℓ "亙乕") (ℓ "乕亙")
  (re 1 1 (ℓ "乼乥乇乥乼") ∷
   rw 0 (q16 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (ℓ "亡") ∷
   re 2 1 (ℓ "乥乊乼乥亍乥乼乊乥") ∷
   rw⁻ 12 (q9 c4) ∷
   re 10 3 (ℓ "乎") ∷
   rw⁻ 9 (q44 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   re 8 3 (ℓ "乩") ∷
   rw⁻ 7 (q45 c4) ∷
   rw 6 (q46 c4) ∷
   rw⁻ 5 (q47 c4) ∷
   re 5 1 (ℓ "乼乢乼") ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q48 c4) ∷
   re 3 1 (ℓ "乥乇乥") ∷
   rw 2 (q9 c4) ∷
   re 3 9 (ℓ "亡") ∷
   re 3 1 (ℓ "乥亝乥") ∷
   rw 5 (q9 c4) ∷
   rw 4 (q23 c4) ∷
   re 0 5 (ℓ "乕") ∷ []) Eq.refl

private
  q49 : WsL → Eqn
  q49 c4 = eqn (ℓ "于亊") (ℓ "亊于") (c₃ (K ↑ • CCZ • K ↑ • iI) (CK₁₀))

-- comm TOFF203 CK41: 23 steps
lem-comm-TOFF203-CK41 : WsL → ⟪ (ℓ "亚亄") ⟫ʷ ≈ ⟪ (ℓ "亄亚") ⟫ʷ
lem-comm-TOFF203-CK41 c4 = derive (ℓ "亚亄") (ℓ "亄亚")
  (re 1 1 (ℓ "乼乥习乥乼") ∷
   rw 0 (q28 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (ℓ "亢") ∷
   re 2 1 (ℓ "乥乊乼乥于乥乼乊乥") ∷
   rw⁻ 12 (q9 c4) ∷
   re 10 3 (ℓ "乴") ∷
   rw⁻ 9 (q32 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   re 8 3 (ℓ "亇") ∷
   rw⁻ 7 (q33 c4) ∷
   rw 6 (q49 c4) ∷
   rw⁻ 5 (q35 c4) ∷
   re 5 1 (ℓ "乼乷乼") ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q36 c4) ∷
   re 3 1 (ℓ "乥习乥") ∷
   rw 2 (q9 c4) ∷
   re 3 9 (ℓ "亢") ∷
   re 3 1 (ℓ "乥亞乥") ∷
   rw 5 (q9 c4) ∷
   rw 4 (q30 c4) ∷
   re 0 5 (ℓ "亄") ∷ []) Eq.refl

private
  q50 : WsL → Eqn
  q50 c4 = sE 2432 (lem-comm-push-TOFF302-sw3-L c4)
  q51 : WsL → Eqn
  q51 c4 = eqn (ℓ "亏乽") (ℓ "乽亏") (c₃ (Toffᵗ) (CX₀₁))
  q52 : WsL → Eqn
  q52 c4 = sE 2433 (lem-comm-push-TOFF402-sw3-L c4)

-- comm TOFF302 CX14: 23 steps
lem-comm-TOFF302-CX14 : WsL → ⟪ (ℓ "些乙") ⟫ʷ ≈ ⟪ (ℓ "乙些") ⟫ʷ
lem-comm-TOFF302-CX14 c4 = derive (ℓ "些乙") (ℓ "乙些")
  (re 1 1 (ℓ "乼乥之乥乼") ∷
   rw 0 (q50 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (ℓ "亣") ∷
   re 2 1 (ℓ "乥乊乼乥亏乥乼乊乥") ∷
   rw⁻ 12 (q9 c4) ∷
   re 10 3 (ℓ "乒") ∷
   rw⁻ 9 (q39 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   re 8 3 (ℓ "乭") ∷
   rw⁻ 7 (q40 c4) ∷
   rw 6 (q51 c4) ∷
   rw⁻ 5 (q42 c4) ∷
   re 5 1 (ℓ "乼书乼") ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   re 3 1 (ℓ "乥之乥") ∷
   rw 2 (q9 c4) ∷
   re 3 9 (ℓ "亣") ∷
   re 3 1 (ℓ "乥亟乥") ∷
   rw 5 (q9 c4) ∷
   rw 4 (q52 c4) ∷
   re 0 5 (ℓ "乙") ∷ []) Eq.refl

private
  q53 : WsL → Eqn
  q53 c4 = eqn (ℓ "亏乹") (ℓ "乹亏") (c₃ (Toffᵗ) (CS))

-- comm TOFF302 CS14: 23 steps
lem-comm-TOFF302-CS14 : WsL → ⟪ (ℓ "些乕") ⟫ʷ ≈ ⟪ (ℓ "乕些") ⟫ʷ
lem-comm-TOFF302-CS14 c4 = derive (ℓ "些乕") (ℓ "乕些")
  (re 1 1 (ℓ "乼乥乇乥乼") ∷
   rw 0 (q50 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (ℓ "亣") ∷
   re 2 1 (ℓ "乥乊乼乥亏乥乼乊乥") ∷
   rw⁻ 12 (q9 c4) ∷
   re 10 3 (ℓ "乎") ∷
   rw⁻ 9 (q44 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   re 8 3 (ℓ "乩") ∷
   rw⁻ 7 (q45 c4) ∷
   rw 6 (q53 c4) ∷
   rw⁻ 5 (q47 c4) ∷
   re 5 1 (ℓ "乼乢乼") ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q48 c4) ∷
   re 3 1 (ℓ "乥乇乥") ∷
   rw 2 (q9 c4) ∷
   re 3 9 (ℓ "亣") ∷
   re 3 1 (ℓ "乥亟乥") ∷
   rw 5 (q9 c4) ∷
   rw 4 (q52 c4) ∷
   re 0 5 (ℓ "乕") ∷ []) Eq.refl

private
  q54 : WsL → Eqn
  q54 c4 = eqn (ℓ "亏乺") (ℓ "乺亏") (c₃ (Toffᵗ) (CS • CS • CS))

-- comm TOFF302 CSd14: 23 steps
lem-comm-TOFF302-CSd14 : WsL → ⟪ (ℓ "些乖") ⟫ʷ ≈ ⟪ (ℓ "乖些") ⟫ʷ
lem-comm-TOFF302-CSd14 c4 = derive (ℓ "些乖") (ℓ "乖些")
  (re 1 1 (ℓ "乼乥么乥乼") ∷
   rw 0 (q50 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (ℓ "亣") ∷
   re 2 1 (ℓ "乥乊乼乥亏乥乼乊乥") ∷
   rw⁻ 12 (q9 c4) ∷
   re 10 3 (ℓ "乏") ∷
   rw⁻ 9 (q17 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   re 8 3 (ℓ "乪") ∷
   rw⁻ 7 (q19 c4) ∷
   rw 6 (q54 c4) ∷
   rw⁻ 5 (q21 c4) ∷
   re 5 1 (ℓ "乼乣乼") ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q22 c4) ∷
   re 3 1 (ℓ "乥么乥") ∷
   rw 2 (q9 c4) ∷
   re 3 9 (ℓ "亣") ∷
   re 3 1 (ℓ "乥亟乥") ∷
   rw 5 (q9 c4) ∷
   rw 4 (q52 c4) ∷
   re 0 5 (ℓ "乖") ∷ []) Eq.refl

private
  q55 : WsL → Eqn
  q55 c4 = eqn (ℓ "二乽") (ℓ "乽二") (c₃ (CCZ) (CX₀₁))

-- comm CCZ023 CX14: 23 steps
lem-comm-CCZ023-CX14 : WsL → ⟪ (ℓ "亘乙") ⟫ʷ ≈ ⟪ (ℓ "乙亘") ⟫ʷ
lem-comm-CCZ023-CX14 c4 = derive (ℓ "亘乙") (ℓ "乙亘")
  (re 1 1 (ℓ "乼乥之乥乼") ∷
   rw 0 (q31 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (ℓ "亠") ∷
   re 2 1 (ℓ "乥乊乼乥二乥乼乊乥") ∷
   rw⁻ 12 (q9 c4) ∷
   re 10 3 (ℓ "乒") ∷
   rw⁻ 9 (q39 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   re 8 3 (ℓ "乭") ∷
   rw⁻ 7 (q40 c4) ∷
   rw 6 (q55 c4) ∷
   rw⁻ 5 (q42 c4) ∷
   re 5 1 (ℓ "乼书乼") ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   re 3 1 (ℓ "乥之乥") ∷
   rw 2 (q9 c4) ∷
   re 3 9 (ℓ "亠") ∷
   re 3 1 (ℓ "乥亜乥") ∷
   rw 5 (q9 c4) ∷
   rw 4 (q37 c4) ∷
   re 0 5 (ℓ "乙") ∷ []) Eq.refl

private
  q56 : WsL → Eqn
  q56 c4 = eqn (ℓ "亏亊") (ℓ "亊亏") (c₃ (Toffᵗ) (CK₁₀))

-- comm TOFF302 CK41: 23 steps
lem-comm-TOFF302-CK41 : WsL → ⟪ (ℓ "些亄") ⟫ʷ ≈ ⟪ (ℓ "亄些") ⟫ʷ
lem-comm-TOFF302-CK41 c4 = derive (ℓ "些亄") (ℓ "亄些")
  (re 1 1 (ℓ "乼乥习乥乼") ∷
   rw 0 (q50 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   re 2 3 (ℓ "亣") ∷
   re 2 1 (ℓ "乥乊乼乥亏乥乼乊乥") ∷
   rw⁻ 12 (q9 c4) ∷
   re 10 3 (ℓ "乴") ∷
   rw⁻ 9 (q32 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   re 8 3 (ℓ "亇") ∷
   rw⁻ 7 (q33 c4) ∷
   rw 6 (q56 c4) ∷
   rw⁻ 5 (q35 c4) ∷
   re 5 1 (ℓ "乼乷乼") ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q36 c4) ∷
   re 3 1 (ℓ "乥习乥") ∷
   rw 2 (q9 c4) ∷
   re 3 9 (ℓ "亣") ∷
   re 3 1 (ℓ "乥亟乥") ∷
   rw 5 (q9 c4) ∷
   rw 4 (q52 c4) ∷
   re 0 5 (ℓ "亄") ∷ []) Eq.refl

private
  q57 : WsL → Eqn
  q57 c4 = sE 2417 (lem-comm-push-BOX⟨0·213⟩-sw1-L c4)

-- comm push BOX(2;0413) sw1 L: 12 steps
lem-comm-push-BOX⟨2·0413⟩-sw1-L : WsL → ⟪ (ℓ "伱乊") ⟫ʷ ≈ ⟪ (ℓ "乊伏") ⟫ʷ
lem-comm-push-BOX⟨2·0413⟩-sw1-L c4 = derive (ℓ "伱乊") (ℓ "乊伏")
  (re 0 1 (ℓ "亜亞仉亞亜仉") ∷
   rw 5 (q57 c4) ∷
   re 4 1 (ℓ "乊五乊") ∷
   rw 6 (q1 c4) ∷
   re 3 1 (ℓ "乊亖乊") ∷
   rw 5 (q1 c4) ∷
   rw 2 (q57 c4) ∷
   re 1 1 (ℓ "乊亖乊") ∷
   rw 3 (q1 c4) ∷
   re 0 1 (ℓ "乊五乊") ∷
   rw 2 (q1 c4) ∷
   re 1 6 (ℓ "伏") ∷ []) Eq.refl

private
  q58 : WsL → Eqn
  q58 c4 = sE 2416 (lem-comm-push-BOX⟨0·123⟩-sw0-L c4)
  q59 : WsL → Eqn
  q59 c4 = sE 2422 (lem-comm-push-CCZ014-sw0-L c4)
  q60 : WsL → Eqn
  q60 c4 = sE 2428 (lem-comm-push-TOFF104-sw0-L c4)

-- comm push BOX(1;0423) sw0 L: 8 steps
lem-comm-push-BOX⟨1·0423⟩-sw0-L : WsL → ⟪ (ℓ "伏丫") ⟫ʷ ≈ ⟪ (ℓ "丫仄") ⟫ʷ
lem-comm-push-BOX⟨1·0423⟩-sw0-L c4 = derive (ℓ "伏丫") (ℓ "丫仄")
  (re 0 1 (ℓ "五亖亶亖五亶") ∷
   rw 5 (q58 c4) ∷
   rw 4 (q59 c4) ∷
   rw 3 (q60 c4) ∷
   rw 2 (q58 c4) ∷
   rw 1 (q60 c4) ∷
   rw 0 (q59 c4) ∷
   re 1 6 (ℓ "仄") ∷ []) Eq.refl

private
  q61 : WsL → Eqn
  q61 c4 = sE 2418 (lem-comm-push-BOX⟨1·023⟩-sw2-L c4)

-- comm push BOX(0;1423) sw2 L: 8 steps
lem-comm-push-BOX⟨0·1423⟩-sw2-L : WsL → ⟪ (ℓ "仄乥") ⟫ʷ ≈ ⟪ (ℓ "乥仆") ⟫ʷ
lem-comm-push-BOX⟨0·1423⟩-sw2-L c4 = derive (ℓ "仄乥") (ℓ "乥仆")
  (re 0 1 (ℓ "五井仃井五仃") ∷
   rw 5 (q61 c4) ∷
   rw 4 (q10 c4) ∷
   rw 3 (q26 c4) ∷
   rw 2 (q61 c4) ∷
   rw 1 (q26 c4) ∷
   rw 0 (q10 c4) ∷
   re 1 6 (ℓ "仆") ∷ []) Eq.refl

private
  q62 : WsL → Eqn
  q62 c4 = sE 2419 (lem-comm-push-BOX⟨1·032⟩-sw1-L c4)

-- comm push BOX(0;1432) sw1 L: 12 steps
lem-comm-push-BOX⟨0·1432⟩-sw1-L : WsL → ⟪ (ℓ "仆乊") ⟫ʷ ≈ ⟪ (ℓ "乊仞") ⟫ʷ
lem-comm-push-BOX⟨0·1432⟩-sw1-L c4 = derive (ℓ "仆乊") (ℓ "乊仞")
  (re 0 1 (ℓ "五井仅井五仅") ∷
   rw 5 (q62 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 5 3 (ℓ "亜") ∷
   rw⁻ 3 (q1 c4) ∷
   re 4 3 (ℓ "亝") ∷
   rw 2 (q62 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (ℓ "亝") ∷
   rw⁻ 0 (q1 c4) ∷
   re 1 3 (ℓ "亜") ∷
   re 1 6 (ℓ "仞") ∷ []) Eq.refl

private
  q63 : WsL → Eqn
  q63 c4 = sE 2421 (lem-comm-push-BOX⟨2·031⟩-sw1-R c4)

-- comm push BOX(0;2431) sw1 R: 12 steps
lem-comm-push-BOX⟨0·2431⟩-sw1-R : WsL → ⟪ (ℓ "乊仞") ⟫ʷ ≈ ⟪ (ℓ "仆乊") ⟫ʷ
lem-comm-push-BOX⟨0·2431⟩-sw1-R c4 = derive (ℓ "乊仞") (ℓ "仆乊")
  (re 1 1 (ℓ "亜亝仝亝亜仝") ∷
   re 1 1 (ℓ "乊五乊") ∷
   rw 0 (q1 c4) ∷
   re 2 1 (ℓ "乊井乊") ∷
   rw 1 (q1 c4) ∷
   rw 2 (q63 c4) ∷
   re 4 1 (ℓ "乊井乊") ∷
   rw 3 (q1 c4) ∷
   re 5 1 (ℓ "乊五乊") ∷
   rw 4 (q1 c4) ∷
   rw 5 (q63 c4) ∷
   re 0 6 (ℓ "仆") ∷ []) Eq.refl

private
  q64 : WsL → Eqn
  q64 c4 = sE 2423 (lem-comm-push-CCZ014-sw2-R c4)
  q65 : WsL → Eqn
  q65 c4 = sE 2427 (lem-comm-push-TOFF014-sw2-R c4)
  q66 : WsL → Eqn
  q66 c4 = sE 2420 (lem-comm-push-BOX⟨1·032⟩-sw2-R c4)

-- comm push BOX(0;1432) sw2 R: 8 steps
lem-comm-push-BOX⟨0·1432⟩-sw2-R : WsL → ⟪ (ℓ "乥仆") ⟫ʷ ≈ ⟪ (ℓ "仄乥") ⟫ʷ
lem-comm-push-BOX⟨0·1432⟩-sw2-R c4 = derive (ℓ "乥仆") (ℓ "仄乥")
  (re 1 1 (ℓ "五井仅井五仅") ∷
   rw 0 (q64 c4) ∷
   rw 1 (q65 c4) ∷
   rw 2 (q66 c4) ∷
   rw 3 (q65 c4) ∷
   rw 4 (q64 c4) ∷
   rw 5 (q66 c4) ∷
   re 0 6 (ℓ "仄") ∷ []) Eq.refl

private
  q67 : WsL → Eqn
  q67 c4 = sE 2443 (lem-comm-push-CCZ014-sw0-R c4)
  q68 : WsL → Eqn
  q68 c4 = sE 2448 (lem-comm-push-TOFF014-sw0-R c4)
  q69 : WsL → Eqn
  q69 c4 = sE 2437 (lem-comm-push-BOX⟨1·023⟩-sw0-R c4)

-- comm push BOX(0;1423) sw0 R: 8 steps
lem-comm-push-BOX⟨0·1423⟩-sw0-R : WsL → ⟪ (ℓ "丫仄") ⟫ʷ ≈ ⟪ (ℓ "伏丫") ⟫ʷ
lem-comm-push-BOX⟨0·1423⟩-sw0-R c4 = derive (ℓ "丫仄") (ℓ "伏丫")
  (re 1 1 (ℓ "五井仃井五仃") ∷
   rw 0 (q67 c4) ∷
   rw 1 (q68 c4) ∷
   rw 2 (q69 c4) ∷
   rw 3 (q68 c4) ∷
   rw 4 (q67 c4) ∷
   rw 5 (q69 c4) ∷
   re 0 6 (ℓ "伏") ∷ []) Eq.refl

private
  q70 : WsL → Eqn
  q70 c4 = sE 2436 (lem-comm-push-BOX⟨0·123⟩-sw1-R c4)

-- comm push BOX(1;0423) sw1 R: 12 steps
lem-comm-push-BOX⟨1·0423⟩-sw1-R : WsL → ⟪ (ℓ "乊伏") ⟫ʷ ≈ ⟪ (ℓ "伱乊") ⟫ʷ
lem-comm-push-BOX⟨1·0423⟩-sw1-R c4 = derive (ℓ "乊伏") (ℓ "伱乊")
  (re 1 1 (ℓ "五亖亶亖五亶") ∷
   rw⁻ 2 (q1 c4) ∷
   re 0 3 (ℓ "亜") ∷
   rw⁻ 3 (q1 c4) ∷
   re 1 3 (ℓ "亞") ∷
   rw 2 (q70 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (ℓ "亞") ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (ℓ "亜") ∷
   rw 5 (q70 c4) ∷
   re 0 6 (ℓ "伱") ∷ []) Eq.refl

private
  q71 : WsL → Eqn
  q71 c4 = eqn (ℓ "丫佒") (ℓ "佒丫") (c₂ (Swap) (CZ ↑))
  q72 : WsL → Eqn
  q72 c4 = sE 2447 (lem-comm-push-CCZ124-sw0-L c4)
  q73 : WsL → Eqn
  q73 c4 = sE 2452 (lem-comm-push-TOFF412-sw0-L c4)

-- comm push BOX(4;213) sw0 L: 8 steps
lem-comm-push-BOX⟨4·213⟩-sw0-L : WsL → ⟪ (ℓ "体丫") ⟫ʷ ≈ ⟪ (ℓ "丫作") ⟫ʷ
lem-comm-push-BOX⟨4·213⟩-sw0-L c4 = derive (ℓ "体丫") (ℓ "丫作")
  (re 0 1 (ℓ "亨享佒享亨佒") ∷
   rw⁻ 5 (q71 c4) ∷
   rw 4 (q72 c4) ∷
   rw 3 (q73 c4) ∷
   rw⁻ 2 (q71 c4) ∷
   rw 1 (q73 c4) ∷
   rw 0 (q72 c4) ∷
   re 1 6 (ℓ "作") ∷ []) Eq.refl

private
  q74 : WsL → Eqn
  q74 c4 = eqn (ℓ "乊俌") (ℓ "俌乊") (c₃ (Swap ↑) (CS • CS • CS))
  q75 : WsL → Eqn
  q75 c4 = eqn (ℓ "乊俋") (ℓ "俋乊") (c₃ (Swap ↑) (CS))
  q76 : WsL → Eqn
  q76 c4 = sE 2439 (lem-comm-push-BOX⟨2·4103⟩-sw1-L c4)

-- comm push SBOX(2;4;10;3) sw1 L: 9 steps
lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L : WsL → ⟪ (ℓ "俍乊") ⟫ʷ ≈ ⟪ (ℓ "乊俁") ⟫ʷ
lem-comm-push-SBOX⟨2·4·10·3⟩-sw1-L c4 = derive (ℓ "俍乊") (ℓ "乊俁")
  (re 0 1 (ℓ "佝亓俋亓俌") ∷
   rw⁻ 4 (q74 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   re 4 3 (ℓ "些") ∷
   rw⁻ 2 (q75 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 2 3 (ℓ "些") ∷
   rw 0 (q76 c4) ∷
   re 1 5 (ℓ "俁") ∷ []) Eq.refl

private
  q77 : WsL → Eqn
  q77 c4 = eqn (ℓ "丫伨") (ℓ "伨丫") (c₂ (Swap) (CZ ↑))
  q78 : WsL → Eqn
  q78 c4 = sE 2451 (lem-comm-push-TOFF401-sw0-L c4)

-- comm push BOX(4;103) sw0 L: 8 steps
lem-comm-push-BOX⟨4·103⟩-sw0-L : WsL → ⟪ (ℓ "伩丫") ⟫ʷ ≈ ⟪ (ℓ "丫伄") ⟫ʷ
lem-comm-push-BOX⟨4·103⟩-sw0-L c4 = derive (ℓ "伩丫") (ℓ "丫伄")
  (re 0 1 (ℓ "五亗伨亗五伨") ∷
   rw⁻ 5 (q77 c4) ∷
   rw 4 (q59 c4) ∷
   rw 3 (q78 c4) ∷
   rw⁻ 2 (q77 c4) ∷
   rw 1 (q78 c4) ∷
   rw 0 (q59 c4) ∷
   re 1 6 (ℓ "伄") ∷ []) Eq.refl

private
  q79 : WsL → Eqn
  q79 c4 = sE 2399 (lem-comm-push-BOX⟨0·43⟩-sw2-L c4)

-- comm push BOX(4;013) sw2 L: 8 steps
lem-comm-push-BOX⟨4·013⟩-sw2-L : WsL → ⟪ (ℓ "伄乥") ⟫ʷ ≈ ⟪ (ℓ "乥伊") ⟫ʷ
lem-comm-push-BOX⟨4·013⟩-sw2-L c4 = derive (ℓ "伄乥") (ℓ "乥伊")
  (re 0 1 (ℓ "五亗仺亗五仺") ∷
   rw 5 (q79 c4) ∷
   rw 4 (q10 c4) ∷
   rw 3 (q12 c4) ∷
   rw 2 (q79 c4) ∷
   rw 1 (q12 c4) ∷
   rw 0 (q10 c4) ∷
   re 1 6 (ℓ "伊") ∷ []) Eq.refl

private
  q80 : WsL → Eqn
  q80 c4 = sE 2441 (lem-comm-push-BOX⟨4·012⟩-sw1-L c4)

-- comm push BOX(0;4312) sw1 L: 8 steps
lem-comm-push-BOX⟨0·4312⟩-sw1-L : WsL → ⟪ (ℓ "伋乊") ⟫ʷ ≈ ⟪ (ℓ "乊伍") ⟫ʷ
lem-comm-push-BOX⟨0·4312⟩-sw1-L c4 = derive (ℓ "伋乊") (ℓ "乊伍")
  (re 0 1 (ℓ "亠亡伊亡亠伊") ∷
   rw 5 (q80 c4) ∷
   rw 4 (q2 c4) ∷
   rw 3 (q6 c4) ∷
   rw 2 (q80 c4) ∷
   rw 1 (q6 c4) ∷
   rw 0 (q2 c4) ∷
   re 1 6 (ℓ "伍") ∷ []) Eq.refl

private
  q81 : WsL → Eqn
  q81 c4 = sE 2397 (lem-comm-push-BOX⟨0·41⟩-sw3-L c4)

-- comm push BOX(4;021) sw3 L: 8 steps
lem-comm-push-BOX⟨4·021⟩-sw3-L : WsL → ⟪ (ℓ "伌乼") ⟫ʷ ≈ ⟪ (ℓ "乼仵") ⟫ʷ
lem-comm-push-BOX⟨4·021⟩-sw3-L c4 = derive (ℓ "伌乼") (ℓ "乼仵")
  (re 0 1 (ℓ "亜亟价亟亜价") ∷
   rw 5 (q81 c4) ∷
   rw 4 (q37 c4) ∷
   rw 3 (q52 c4) ∷
   rw 2 (q81 c4) ∷
   rw 1 (q52 c4) ∷
   rw 0 (q37 c4) ∷
   re 1 6 (ℓ "仵") ∷ []) Eq.refl

private
  q82 : WsL → Eqn
  q82 c4 = sE 2440 (lem-comm-push-BOX⟨3·021⟩-sw2-L c4)

-- comm push BOX(0;3421) sw2 L: 12 steps
lem-comm-push-BOX⟨0·3421⟩-sw2-L : WsL → ⟪ (ℓ "件乥") ⟫ʷ ≈ ⟪ (ℓ "乥仞") ⟫ʷ
lem-comm-push-BOX⟨0·3421⟩-sw2-L c4 = derive (ℓ "件乥") (ℓ "乥仞")
  (re 0 1 (ℓ "亠亡仵亡亠仵") ∷
   rw 5 (q82 c4) ∷
   re 4 1 (ℓ "乥亜乥") ∷
   rw 6 (q9 c4) ∷
   re 3 1 (ℓ "乥亝乥") ∷
   rw 5 (q9 c4) ∷
   rw 2 (q82 c4) ∷
   re 1 1 (ℓ "乥亝乥") ∷
   rw 3 (q9 c4) ∷
   re 0 1 (ℓ "乥亜乥") ∷
   rw 2 (q9 c4) ∷
   re 1 6 (ℓ "仞") ∷ []) Eq.refl

private
  q83 : WsL → Eqn
  q83 c4 = sE 2438 (lem-comm-push-BOX⟨2·031⟩-sw2-R c4)

-- comm push BOX(0;2431) sw2 R: 12 steps
lem-comm-push-BOX⟨0·2431⟩-sw2-R : WsL → ⟪ (ℓ "乥仞") ⟫ʷ ≈ ⟪ (ℓ "件乥") ⟫ʷ
lem-comm-push-BOX⟨0·2431⟩-sw2-R c4 = derive (ℓ "乥仞") (ℓ "件乥")
  (re 1 1 (ℓ "亜亝仝亝亜仝") ∷
   rw⁻ 2 (q9 c4) ∷
   re 0 3 (ℓ "亠") ∷
   rw⁻ 3 (q9 c4) ∷
   re 1 3 (ℓ "亡") ∷
   rw 2 (q83 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   re 3 3 (ℓ "亡") ∷
   rw⁻ 6 (q9 c4) ∷
   re 4 3 (ℓ "亠") ∷
   rw 5 (q83 c4) ∷
   re 0 6 (ℓ "件") ∷ []) Eq.refl

private
  q84 : WsL → Eqn
  q84 c4 = sE 2444 (lem-comm-push-CCZ023-sw3-R c4)
  q85 : WsL → Eqn
  q85 c4 = sE 2450 (lem-comm-push-TOFF302-sw3-R c4)
  q86 : WsL → Eqn
  q86 c4 = sE 2396 (lem-comm-push-BOX⟨0·31⟩-sw3-R c4)

-- comm push BOX(3;021) sw3 R: 8 steps
lem-comm-push-BOX⟨3·021⟩-sw3-R : WsL → ⟪ (ℓ "乼仵") ⟫ʷ ≈ ⟪ (ℓ "伌乼") ⟫ʷ
lem-comm-push-BOX⟨3·021⟩-sw3-R c4 = derive (ℓ "乼仵") (ℓ "伌乼")
  (re 1 1 (ℓ "亘些仟些亘仟") ∷
   rw 0 (q84 c4) ∷
   rw 1 (q85 c4) ∷
   rw 2 (q86 c4) ∷
   rw 3 (q85 c4) ∷
   rw 4 (q84 c4) ∷
   rw 5 (q86 c4) ∷
   re 0 6 (ℓ "伌") ∷ []) Eq.refl

private
  q87 : WsL → Eqn
  q87 c4 = sE 2445 (lem-comm-push-CCZ034-sw1-R c4)
  q88 : WsL → Eqn
  q88 c4 = sE 2449 (lem-comm-push-TOFF034-sw1-R c4)
  q89 : WsL → Eqn
  q89 c4 = sE 2442 (lem-comm-push-BOX⟨4·021⟩-sw1-R c4)

-- comm push BOX(0;4321) sw1 R: 8 steps
lem-comm-push-BOX⟨0·4321⟩-sw1-R : WsL → ⟪ (ℓ "乊伍") ⟫ʷ ≈ ⟪ (ℓ "伋乊") ⟫ʷ
lem-comm-push-BOX⟨0·4321⟩-sw1-R c4 = derive (ℓ "乊伍") (ℓ "伋乊")
  (re 1 1 (ℓ "亠亡伌亡亠伌") ∷
   rw 0 (q87 c4) ∷
   rw 1 (q88 c4) ∷
   rw 2 (q89 c4) ∷
   rw 3 (q88 c4) ∷
   rw 4 (q87 c4) ∷
   rw 5 (q89 c4) ∷
   re 0 6 (ℓ "伋") ∷ []) Eq.refl

private
  q90 : WsL → Eqn
  q90 c4 = sE 2469 (lem-comm-push-TOFF401-sw2-R c4)
  q91 : WsL → Eqn
  q91 c4 = sE 2398 (lem-comm-push-BOX⟨0·42⟩-sw2-R c4)

-- comm push BOX(4;012) sw2 R: 8 steps
lem-comm-push-BOX⟨4·012⟩-sw2-R : WsL → ⟪ (ℓ "乥伊") ⟫ʷ ≈ ⟪ (ℓ "伄乥") ⟫ʷ
lem-comm-push-BOX⟨4·012⟩-sw2-R c4 = derive (ℓ "乥伊") (ℓ "伄乥")
  (re 1 1 (ℓ "五亗仿亗五仿") ∷
   rw 0 (q64 c4) ∷
   rw 1 (q90 c4) ∷
   rw 2 (q91 c4) ∷
   rw 3 (q90 c4) ∷
   rw 4 (q64 c4) ∷
   rw 5 (q91 c4) ∷
   re 0 6 (ℓ "伄") ∷ []) Eq.refl

private
  q92 : WsL → Eqn
  q92 c4 = sE 2468 (lem-comm-push-TOFF401-sw0-R c4)
  q93 : WsL → Eqn
  q93 c4 = eqn (ℓ "丫仺") (ℓ "仺丫") (c₂ (Swap) (CZ ↑))

-- comm push BOX(4;013) sw0 R: 8 steps
lem-comm-push-BOX⟨4·013⟩-sw0-R : WsL → ⟪ (ℓ "丫伄") ⟫ʷ ≈ ⟪ (ℓ "伩丫") ⟫ʷ
lem-comm-push-BOX⟨4·013⟩-sw0-R c4 = derive (ℓ "丫伄") (ℓ "伩丫")
  (re 1 1 (ℓ "五亗仺亗五仺") ∷
   rw 0 (q67 c4) ∷
   rw 1 (q92 c4) ∷
   rw 2 (q93 c4) ∷
   rw 3 (q92 c4) ∷
   rw 4 (q67 c4) ∷
   rw 5 (q93 c4) ∷
   re 0 6 (ℓ "伩") ∷ []) Eq.refl

private
  q94 : WsL → Eqn
  q94 c4 = sE 2455 (lem-comm-push-BOX⟨1·4203⟩-sw1-R c4)
  q95 : WsL → Eqn
  q95 c4 = eqn (ℓ "乊便") (ℓ "便乊") (c₃ (Swap ↑) (CS))
  q96 : WsL → Eqn
  q96 c4 = eqn (ℓ "乊俀") (ℓ "俀乊") (c₃ (Swap ↑) (CS • CS • CS))

-- comm push SBOX(1;4;20;3) sw1 R: 9 steps
lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R : WsL → ⟪ (ℓ "乊俁") ⟫ʷ ≈ ⟪ (ℓ "俍乊") ⟫ʷ
lem-comm-push-SBOX⟨1·4·20·3⟩-sw1-R c4 = derive (ℓ "乊俁") (ℓ "俍乊")
  (re 1 1 (ℓ "伪些便些俀") ∷
   rw 0 (q94 c4) ∷
   re 2 1 (ℓ "乊亓乊") ∷
   rw 1 (q1 c4) ∷
   rw 2 (q95 c4) ∷
   re 4 1 (ℓ "乊亓乊") ∷
   rw 3 (q1 c4) ∷
   rw 4 (q96 c4) ∷
   re 0 5 (ℓ "俍") ∷ []) Eq.refl

private
  q97 : WsL → Eqn
  q97 c4 = sE 2463 (lem-comm-push-CCZ024-sw0-R c4)
  q98 : WsL → Eqn
  q98 c4 = sE 2470 (lem-comm-push-TOFF402-sw0-R c4)

-- comm push BOX(4;203) sw0 R: 8 steps
lem-comm-push-BOX⟨4·203⟩-sw0-R : WsL → ⟪ (ℓ "丫作") ⟫ʷ ≈ ⟪ (ℓ "体丫") ⟫ʷ
lem-comm-push-BOX⟨4·203⟩-sw0-R c4 = derive (ℓ "丫作") (ℓ "体丫")
  (re 1 1 (ℓ "亜亟佒亟亜佒") ∷
   rw 0 (q97 c4) ∷
   rw 1 (q98 c4) ∷
   rw 2 (q71 c4) ∷
   rw 3 (q98 c4) ∷
   rw 4 (q97 c4) ∷
   rw 5 (q71 c4) ∷
   re 0 6 (ℓ "体") ∷ []) Eq.refl

private
  q99 : WsL → Eqn
  q99 c4 = sE 2465 (lem-comm-push-TOFF024-sw0-R c4)
  q100 : WsL → Eqn
  q100 c4 = sE 2457 (lem-comm-push-BOX⟨2·031⟩-sw0-R c4)

-- comm push BOX(0;2431) sw0 R: 8 steps
lem-comm-push-BOX⟨0·2431⟩-sw0-R : WsL → ⟪ (ℓ "丫仞") ⟫ʷ ≈ ⟪ (ℓ "优丫") ⟫ʷ
lem-comm-push-BOX⟨0·2431⟩-sw0-R c4 = derive (ℓ "丫仞") (ℓ "优丫")
  (re 1 1 (ℓ "亜亝仝亝亜仝") ∷
   rw 0 (q97 c4) ∷
   rw 1 (q99 c4) ∷
   rw 2 (q100 c4) ∷
   rw 3 (q99 c4) ∷
   rw 4 (q97 c4) ∷
   rw 5 (q100 c4) ∷
   re 0 6 (ℓ "优") ∷ []) Eq.refl

private
  q101 : WsL → Eqn
  q101 c4 = wlE 122 c4
  q102 : WsL → Eqn
  q102 c4 = wlE 123 c4
  q103 : WsL → Eqn
  q103 c4 = sE 2458 (lem-comm-push-BOX⟨2·130⟩-sw1-R c4)

-- comm push BOX(1;2430) sw1 R: 8 steps
lem-comm-push-BOX⟨1·2430⟩-sw1-R : WsL → ⟪ (ℓ "乊优") ⟫ʷ ≈ ⟪ (ℓ "伶乊") ⟫ʷ
lem-comm-push-BOX⟨1·2430⟩-sw1-R c4 = derive (ℓ "乊优") (ℓ "伶乊")
  (re 1 1 (ℓ "亨亩众亩亨众") ∷
   rw⁻ 0 (q101 c4) ∷
   rw 1 (q102 c4) ∷
   rw 2 (q103 c4) ∷
   rw 3 (q102 c4) ∷
   rw⁻ 4 (q101 c4) ∷
   rw 5 (q103 c4) ∷
   re 0 6 (ℓ "伶") ∷ []) Eq.refl

private
  q104 : WsL → Eqn
  q104 c4 = sE 2459 (lem-comm-push-BOX⟨2·1430⟩-sw2-R c4)
  q105 : WsL → Eqn
  q105 c4 = eqn (ℓ "俅乥") (ℓ "乥俅") (c₂ (CS) (Swap))
  q106 : WsL → Eqn
  q106 c4 = eqn (ℓ "俆乥") (ℓ "乥俆") (c₂ (CS • CS • CS) (Swap))

-- comm push SBOX(2;1;43;0) sw2 R: 9 steps
lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R : WsL → ⟪ (ℓ "乥俇") ⟫ʷ ≈ ⟪ (ℓ "俜乥") ⟫ʷ
lem-comm-push-SBOX⟨2·1·43·0⟩-sw2-R c4 = derive (ℓ "乥俇") (ℓ "俜乥")
  (re 1 1 (ℓ "伶亡俅亡俆") ∷
   rw 0 (q104 c4) ∷
   re 2 1 (ℓ "乥亝乥") ∷
   rw 1 (q9 c4) ∷
   rw⁻ 2 (q105 c4) ∷
   re 4 1 (ℓ "乥亝乥") ∷
   rw 3 (q9 c4) ∷
   rw⁻ 4 (q106 c4) ∷
   re 0 5 (ℓ "俜") ∷ []) Eq.refl

private
  q107 : WsL → Eqn
  q107 c4 = sE 2461 (lem-comm-push-BOX⟨3·1420⟩-sw3-R c4)
  q108 : WsL → Eqn
  q108 c4 = sE 2466 (lem-comm-push-TOFF024-sw3-R c4)
  q109 : WsL → Eqn
  q109 c4 = eqn (ℓ "俗乼") (ℓ "乼俗") (c₂ (CS) (Swap ↑))
  q110 : WsL → Eqn
  q110 c4 = eqn (ℓ "俛乼") (ℓ "乼俛") (c₂ (CS • CS • CS) (Swap ↑))

-- comm push SBOX(3;1;42;0) sw3 R: 7 steps
lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R : WsL → ⟪ (ℓ "乼俜") ⟫ʷ ≈ ⟪ (ℓ "俱乼") ⟫ʷ
lem-comm-push-SBOX⟨3·1·42·0⟩-sw3-R c4 = derive (ℓ "乼俜") (ℓ "俱乼")
  (re 1 1 (ℓ "佯亝俗亝俛") ∷
   rw 0 (q107 c4) ∷
   rw 1 (q108 c4) ∷
   rw⁻ 2 (q109 c4) ∷
   rw 3 (q108 c4) ∷
   rw⁻ 4 (q110 c4) ∷
   re 0 5 (ℓ "俱") ∷ []) Eq.refl

private
  q111 : WsL → Eqn
  q111 c4 = sE 2462 (lem-comm-push-BOX⟨4·1320⟩-sw2-R c4)
  q112 : WsL → Eqn
  q112 c4 = wlE 143 c4
  q113 : WsL → Eqn
  q113 c4 = eqn (ℓ "俩乥") (ℓ "乥俩") (c₂ (CS) (Swap))
  q114 : WsL → Eqn
  q114 c4 = eqn (ℓ "俰乥") (ℓ "乥俰") (c₂ (CS • CS • CS) (Swap))

-- comm push SBOX(4;1;32;0) sw2 R: 7 steps
lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R : WsL → ⟪ (ℓ "乥俱") ⟫ʷ ≈ ⟪ (ℓ "俯乥") ⟫ʷ
lem-comm-push-SBOX⟨4·1·32·0⟩-sw2-R c4 = derive (ℓ "乥俱") (ℓ "俯乥")
  (re 1 1 (ℓ "侖亙俩亙俰") ∷
   rw 0 (q111 c4) ∷
   rw 1 (q112 c4) ∷
   rw⁻ 2 (q113 c4) ∷
   rw 3 (q112 c4) ∷
   rw⁻ 4 (q114 c4) ∷
   re 0 5 (ℓ "俯") ∷ []) Eq.refl

private
  q115 : WsL → Eqn
  q115 c4 = wlE 144 c4
  q116 : WsL → Eqn
  q116 c4 = sE 2456 (lem-comm-push-BOX⟨1·430⟩-sw1-R c4)

-- comm push BOX(4;1230) sw1 R: 8 steps
lem-comm-push-BOX⟨4·1230⟩-sw1-R : WsL → ⟪ (ℓ "乊侔") ⟫ʷ ≈ ⟪ (ℓ "侙乊") ⟫ʷ
lem-comm-push-BOX⟨4·1230⟩-sw1-R c4 = derive (ℓ "乊侔") (ℓ "侙乊")
  (re 1 1 (ℓ "亨享伬享亨伬") ∷
   rw⁻ 0 (q101 c4) ∷
   rw 1 (q115 c4) ∷
   rw 2 (q116 c4) ∷
   rw 3 (q115 c4) ∷
   rw⁻ 4 (q101 c4) ∷
   rw 5 (q116 c4) ∷
   re 0 6 (ℓ "侙") ∷ []) Eq.refl

private
  q117 : WsL → Eqn
  q117 c4 = sE 2464 (lem-comm-push-CCZ124-sw0-R c4)
  q118 : WsL → Eqn
  q118 c4 = sE 2471 (lem-comm-push-TOFF412-sw0-R c4)
  q119 : WsL → Eqn
  q119 c4 = sE 2460 (lem-comm-push-BOX⟨2·430⟩-sw0-R c4)

-- comm push BOX(4;2130) sw0 R: 8 steps
lem-comm-push-BOX⟨4·2130⟩-sw0-R : WsL → ⟪ (ℓ "丫侙") ⟫ʷ ≈ ⟪ (ℓ "侗丫") ⟫ʷ
lem-comm-push-BOX⟨4·2130⟩-sw0-R c4 = derive (ℓ "丫侙") (ℓ "侗丫")
  (re 1 1 (ℓ "亨享你享亨你") ∷
   rw 0 (q117 c4) ∷
   rw 1 (q118 c4) ∷
   rw 2 (q119 c4) ∷
   rw 3 (q118 c4) ∷
   rw 4 (q117 c4) ∷
   rw 5 (q119 c4) ∷
   re 0 6 (ℓ "侗") ∷ []) Eq.refl

private
  q120 : WsL → Eqn
  q120 c4 = sE 2453 (lem-comm-push-BOX⟨0·213⟩-sw2-R c4)

-- comm push BOX(2;0413) sw2 R: 12 steps
lem-comm-push-BOX⟨2·0413⟩-sw2-R : WsL → ⟪ (ℓ "乥伱") ⟫ʷ ≈ ⟪ (ℓ "佨乥") ⟫ʷ
lem-comm-push-BOX⟨2·0413⟩-sw2-R c4 = derive (ℓ "乥伱") (ℓ "佨乥")
  (re 1 1 (ℓ "亜亞仉亞亜仉") ∷
   rw⁻ 2 (q9 c4) ∷
   re 0 3 (ℓ "亠") ∷
   rw⁻ 3 (q9 c4) ∷
   re 1 3 (ℓ "亢") ∷
   rw 2 (q120 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   re 3 3 (ℓ "亢") ∷
   rw⁻ 6 (q9 c4) ∷
   re 4 3 (ℓ "亠") ∷
   rw 5 (q120 c4) ∷
   re 0 6 (ℓ "佨") ∷ []) Eq.refl

private
  q121 : WsL → Eqn
  q121 c4 = sE 2446 (lem-comm-push-CCZ034-sw3-R c4)
  q122 : WsL → Eqn
  q122 c4 = sE 2467 (lem-comm-push-TOFF304-sw3-R c4)
  q123 : WsL → Eqn
  q123 c4 = sE 2395 (lem-comm-push-BOX⟨0·312⟩-sw3-R c4)

-- comm push BOX(3;0412) sw3 R: 8 steps
lem-comm-push-BOX⟨3·0412⟩-sw3-R : WsL → ⟪ (ℓ "乼佨") ⟫ʷ ≈ ⟪ (ℓ "侐乼") ⟫ʷ
lem-comm-push-BOX⟨3·0412⟩-sw3-R c4 = derive (ℓ "乼佨") (ℓ "侐乼")
  (re 1 1 (ℓ "亠亢仡亢亠仡") ∷
   rw 0 (q121 c4) ∷
   rw 1 (q122 c4) ∷
   rw 2 (q123 c4) ∷
   rw 3 (q122 c4) ∷
   rw 4 (q121 c4) ∷
   rw 5 (q123 c4) ∷
   re 0 6 (ℓ "侐") ∷ []) Eq.refl

private
  q124 : WsL → Eqn
  q124 c4 = sE 2400 (lem-comm-push-BOX⟨4·02⟩-sw2-R c4)

-- comm push BOX(0;412) sw2 R: 8 steps
lem-comm-push-BOX⟨0·412⟩-sw2-R : WsL → ⟪ (ℓ "乥仹") ⟫ʷ ≈ ⟪ (ℓ "仾乥") ⟫ʷ
lem-comm-push-BOX⟨0·412⟩-sw2-R c4 = derive (ℓ "乥仹") (ℓ "仾乥")
  (re 1 1 (ℓ "五井仸井五仸") ∷
   rw 0 (q64 c4) ∷
   rw 1 (q65 c4) ∷
   rw 2 (q124 c4) ∷
   rw 3 (q65 c4) ∷
   rw 4 (q64 c4) ∷
   rw 5 (q124 c4) ∷
   re 0 6 (ℓ "仾") ∷ []) Eq.refl

private
  q125 : WsL → Eqn
  q125 c4 = sE 2454 (lem-comm-push-BOX⟨0·413⟩-sw1-R c4)

-- comm push BOX(4;0213) sw1 R: 12 steps
lem-comm-push-BOX⟨4·0213⟩-sw1-R : WsL → ⟪ (ℓ "乊侎") ⟫ʷ ≈ ⟪ (ℓ "侍乊") ⟫ʷ
lem-comm-push-BOX⟨4·0213⟩-sw1-R c4 = derive (ℓ "乊侎") (ℓ "侍乊")
  (re 1 1 (ℓ "亜亟仾亟亜仾") ∷
   re 1 1 (ℓ "乊五乊") ∷
   rw 0 (q1 c4) ∷
   re 2 1 (ℓ "乊亗乊") ∷
   rw 1 (q1 c4) ∷
   rw 2 (q125 c4) ∷
   re 4 1 (ℓ "乊亗乊") ∷
   rw 3 (q1 c4) ∷
   re 5 1 (ℓ "乊五乊") ∷
   rw 4 (q1 c4) ∷
   rw 5 (q125 c4) ∷
   re 0 6 (ℓ "侍") ∷ []) Eq.refl

private
  q126 : WsL → Eqn
  q126 c4 = sE 2401 (lem-comm-push-BOX⟨4·03⟩-sw0-R c4)

-- comm push BOX(0;423) sw0 R: 8 steps
lem-comm-push-BOX⟨0·423⟩-sw0-R : WsL → ⟪ (ℓ "丫伆") ⟫ʷ ≈ ⟪ (ℓ "伫丫") ⟫ʷ
lem-comm-push-BOX⟨0·423⟩-sw0-R c4 = derive (ℓ "丫伆") (ℓ "伫丫")
  (re 1 1 (ℓ "亜亝份亝亜份") ∷
   rw 0 (q97 c4) ∷
   rw 1 (q99 c4) ∷
   rw 2 (q126 c4) ∷
   rw 3 (q99 c4) ∷
   rw 4 (q97 c4) ∷
   rw 5 (q126 c4) ∷
   re 0 6 (ℓ "伫") ∷ []) Eq.refl
