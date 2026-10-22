{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD048 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D048 (Sᴰ : SD048) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

-- The lemmas of other derivation modules (DSig).
private
  lem-F4-I-K2 : Ws → St 1207
  lem-F4-I-K2 = pickᴰ 0 Sᴰ
  lem-F4-I-K3 : Ws → St 1208
  lem-F4-I-K3 = pickᴰ 1 Sᴰ
  lem-F4-I-S2 : Ws → St 1382
  lem-F4-I-S2 = pickᴰ 2 Sᴰ
  lem-F4-I-S3 : Ws → St 1351
  lem-F4-I-S3 = pickᴰ 3 Sᴰ
  lem-F4-K2-K2 : Ws → St 1352
  lem-F4-K2-K2 = pickᴰ 4 Sᴰ
  lem-F4-K3-K3 : Ws → St 1383
  lem-F4-K3-K3 = pickᴰ 5 Sᴰ
  lem-F4-S2-I : Ws → St 1384
  lem-F4-S2-I = pickᴰ 6 Sᴰ
  lem-F4-S2-K3 : Ws → St 1385
  lem-F4-S2-K3 = pickᴰ 7 Sᴰ
  lem-F4-S2-S2 : Ws → St 1386
  lem-F4-S2-S2 = pickᴰ 8 Sᴰ
  lem-F4-S3-I : Ws → St 1353
  lem-F4-S3-I = pickᴰ 9 Sᴰ
  lem-F4-S3-K2 : Ws → St 1354
  lem-F4-S3-K2 = pickᴰ 10 Sᴰ
  lem-F4-S3-S3 : Ws → St 1355
  lem-F4-S3-S3 = pickᴰ 11 Sᴰ
  lem-F4-I-K2-at132132 : Ws → St 1387
  lem-F4-I-K2-at132132 = pickᴰ 12 Sᴰ
  lem-F4-I-S3-at132132 : Ws → St 1388
  lem-F4-I-S3-at132132 = pickᴰ 13 Sᴰ
  lem-F4-K2-K2-at132132 : Ws → St 1389
  lem-F4-K2-K2-at132132 = pickᴰ 14 Sᴰ
  lem-F4-S3-I-at132132 : Ws → St 1390
  lem-F4-S3-I-at132132 = pickᴰ 15 Sᴰ
  lem-F4-S3-K2-at132132 : Ws → St 1391
  lem-F4-S3-K2-at132132 = pickᴰ 16 Sᴰ
  lem-F4-S3-S3-at132132 : Ws → St 1392
  lem-F4-S3-S3-at132132 = pickᴰ 17 Sᴰ
  lem-F4-CS2-I : Ws → St 1363
  lem-F4-CS2-I = pickᴰ 18 Sᴰ
  lem-F4-CS2-S2 : Ws → St 1393
  lem-F4-CS2-S2 = pickᴰ 19 Sᴰ
  lem-F4-I-CS2 : Ws → St 1230
  lem-F4-I-CS2 = pickᴰ 20 Sᴰ
  lem-F4-K2-CS2 : Ws → St 1365
  lem-F4-K2-CS2 = pickᴰ 21 Sᴰ
  lem-F4-S2-CS2 : Ws → St 1394
  lem-F4-S2-CS2 = pickᴰ 22 Sᴰ
  lem-F4-S3-CS2 : Ws → St 1366
  lem-F4-S3-CS2 = pickᴰ 23 Sᴰ
  lem-F4-CS2-K2 : Ws → St 1367
  lem-F4-CS2-K2 = pickᴰ 24 Sᴰ
  lem-F4-CS2-CS2 : Ws → St 1368
  lem-F4-CS2-CS2 = pickᴰ 25 Sᴰ
  lem-F4-CS2-CS2-at132132 : Ws → St 1395
  lem-F4-CS2-CS2-at132132 = pickᴰ 26 Sᴰ
  lem-F4-CS2-K2-at132132 : Ws → St 1397
  lem-F4-CS2-K2-at132132 = pickᴰ 27 Sᴰ
  lem-F4-I-CS2-at132132 : Ws → St 1399
  lem-F4-I-CS2-at132132 = pickᴰ 28 Sᴰ
  lem-F4-K2-CS2-at132132 : Ws → St 1400
  lem-F4-K2-CS2-at132132 = pickᴰ 29 Sᴰ
  lem-F4-S3-CS2-at132132 : Ws → St 1401
  lem-F4-S3-CS2-at132132 = pickᴰ 30 Sᴰ
  lem-F4-CS2-K3 : Ws → St 1402
  lem-F4-CS2-K3 = pickᴰ 31 Sᴰ
  lem-F4-K3-CS2 : Ws → St 1403
  lem-F4-K3-CS2 = pickᴰ 32 Sᴰ
  lem-F5-23 : Ws → St 1377
  lem-F5-23 = pickᴰ 33 Sᴰ
  lem-F5-23-at132132 : Ws → St 1404
  lem-F5-23-at132132 = pickᴰ 34 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1377 (lem-F5-23 c4)
  q2 : Ws → Eqn
  q2 c4 = wlE 1419 (lit c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1403 (lem-F4-K3-CS2 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1402 (lem-F4-CS2-K3 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1368 (lem-F4-CS2-CS2 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1383 (lem-F4-K3-K3 c4)
  q7 : Ws → Eqn
  q7 c4 = wlE 1418 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1394 (lem-F4-S2-CS2 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1385 (lem-F4-S2-K3 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1386 (lem-F4-S2-S2 c4)
  q11 : Ws → Eqn
  q11 c4 = wlE 1411 (lit c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1382 (lem-F4-I-S2 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1230 (lem-F4-I-CS2 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1208 (lem-F4-I-K3 c4)

-- deb-Q-lo-split-b: 45 steps
lem-deb-Q-lo-split-b : Ws → ⟪ (CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ []) ⟫ʷ
lem-deb-Q-lo-split-b c4 = derive (CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 4 (q2 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 12 (q2 c4) ∷
   rw⁻ 11 (q3 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 15 (q4 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   rw⁻ 13 (q4 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   rw 20 (q7 c4) ∷
   rw⁻ 19 (q8 c4) ∷
   rw⁻ 18 (q9 c4) ∷
   rw⁻ 17 (q8 c4) ∷
   rw⁻ 16 (q9 c4) ∷
   rw⁻ 15 (q8 c4) ∷
   rw 24 (q7 c4) ∷
   rw⁻ 23 (q10 c4) ∷
   rw⁻ 22 (q8 c4) ∷
   rw⁻ 21 (q9 c4) ∷
   rw⁻ 20 (q8 c4) ∷
   rw⁻ 19 (q9 c4) ∷
   rw⁻ 18 (q8 c4) ∷
   rw 28 (q7 c4) ∷
   rw⁻ 27 (q10 c4) ∷
   rw⁻ 26 (q10 c4) ∷
   rw⁻ 25 (q8 c4) ∷
   rw⁻ 24 (q9 c4) ∷
   rw⁻ 23 (q8 c4) ∷
   rw⁻ 22 (q9 c4) ∷
   rw⁻ 21 (q8 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw⁻ 31 (q12 c4) ∷
   rw⁻ 30 (q12 c4) ∷
   rw⁻ 29 (q12 c4) ∷
   rw⁻ 28 (q13 c4) ∷
   rw⁻ 27 (q14 c4) ∷
   rw⁻ 26 (q13 c4) ∷
   rw⁻ 25 (q14 c4) ∷
   rw⁻ 24 (q13 c4) ∷ []) Eq.refl

private
  q15 : Ws → Eqn
  q15 c4 = wlE 1409 (lit c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1365 (lem-F4-K2-CS2 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1367 (lem-F4-CS2-K2 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1352 (lem-F4-K2-K2 c4)
  q19 : Ws → Eqn
  q19 c4 = wlE 1410 (lit c4)
  q20 : Ws → Eqn
  q20 c4 = sE 1366 (lem-F4-S3-CS2 c4)
  q21 : Ws → Eqn
  q21 c4 = sE 1354 (lem-F4-S3-K2 c4)
  q22 : Ws → Eqn
  q22 c4 = sE 1355 (lem-F4-S3-S3 c4)
  q23 : Ws → Eqn
  q23 c4 = sE 1351 (lem-F4-I-S3 c4)
  q24 : Ws → Eqn
  q24 c4 = sE 1207 (lem-F4-I-K2 c4)
  q25 : Ws → Eqn
  q25 c4 = sE 1353 (lem-F4-S3-I c4)

-- deb-Q-hi-split-a: 55 steps
lem-deb-Q-hi-split-a : Ws → ⟪ (CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ []) ⟫ʷ
lem-deb-Q-hi-split-a c4 = derive (CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ S3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ CS34 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 4 (q15 c4) ∷
   rw⁻ 3 (q16 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 12 (q15 c4) ∷
   rw⁻ 11 (q16 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   rw⁻ 9 (q16 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 15 (q17 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   rw⁻ 13 (q17 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   rw 20 (q19 c4) ∷
   rw⁻ 19 (q20 c4) ∷
   rw⁻ 18 (q21 c4) ∷
   rw⁻ 17 (q20 c4) ∷
   rw⁻ 16 (q21 c4) ∷
   rw⁻ 15 (q20 c4) ∷
   rw 24 (q19 c4) ∷
   rw⁻ 23 (q22 c4) ∷
   rw⁻ 22 (q20 c4) ∷
   rw⁻ 21 (q21 c4) ∷
   rw⁻ 20 (q20 c4) ∷
   rw⁻ 19 (q21 c4) ∷
   rw⁻ 18 (q20 c4) ∷
   rw 28 (q19 c4) ∷
   rw⁻ 27 (q22 c4) ∷
   rw⁻ 26 (q22 c4) ∷
   rw⁻ 25 (q20 c4) ∷
   rw⁻ 24 (q21 c4) ∷
   rw⁻ 23 (q20 c4) ∷
   rw⁻ 22 (q21 c4) ∷
   rw⁻ 21 (q20 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw⁻ 31 (q23 c4) ∷
   rw⁻ 30 (q23 c4) ∷
   rw⁻ 29 (q23 c4) ∷
   rw⁻ 28 (q13 c4) ∷
   rw⁻ 27 (q24 c4) ∷
   rw⁻ 26 (q13 c4) ∷
   rw⁻ 25 (q24 c4) ∷
   rw⁻ 24 (q13 c4) ∷
   rw 36 (q19 c4) ∷
   rw⁻ 35 (q25 c4) ∷
   rw⁻ 34 (q22 c4) ∷
   rw⁻ 33 (q22 c4) ∷
   rw⁻ 32 (q22 c4) ∷
   rw⁻ 31 (q20 c4) ∷
   rw⁻ 30 (q21 c4) ∷
   rw⁻ 29 (q20 c4) ∷
   rw⁻ 28 (q21 c4) ∷
   rw⁻ 27 (q20 c4) ∷ []) Eq.refl

-- deb-Q-hi-split-b: 45 steps
lem-deb-Q-hi-split-b : Ws → ⟪ (CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ []) ⟫ʷ
lem-deb-Q-hi-split-b c4 = derive (CS23 ∷ K2 ∷ CS23 ∷ K2 ∷ CS23 ∷ S3 ∷ S3 ∷ S3 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ CS34 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ S4 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 4 (q15 c4) ∷
   rw⁻ 3 (q16 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 12 (q15 c4) ∷
   rw⁻ 11 (q16 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   rw⁻ 9 (q16 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 15 (q17 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   rw⁻ 13 (q17 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   rw 20 (q19 c4) ∷
   rw⁻ 19 (q20 c4) ∷
   rw⁻ 18 (q21 c4) ∷
   rw⁻ 17 (q20 c4) ∷
   rw⁻ 16 (q21 c4) ∷
   rw⁻ 15 (q20 c4) ∷
   rw 24 (q19 c4) ∷
   rw⁻ 23 (q22 c4) ∷
   rw⁻ 22 (q20 c4) ∷
   rw⁻ 21 (q21 c4) ∷
   rw⁻ 20 (q20 c4) ∷
   rw⁻ 19 (q21 c4) ∷
   rw⁻ 18 (q20 c4) ∷
   rw 28 (q19 c4) ∷
   rw⁻ 27 (q22 c4) ∷
   rw⁻ 26 (q22 c4) ∷
   rw⁻ 25 (q20 c4) ∷
   rw⁻ 24 (q21 c4) ∷
   rw⁻ 23 (q20 c4) ∷
   rw⁻ 22 (q21 c4) ∷
   rw⁻ 21 (q20 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw⁻ 31 (q23 c4) ∷
   rw⁻ 30 (q23 c4) ∷
   rw⁻ 29 (q23 c4) ∷
   rw⁻ 28 (q13 c4) ∷
   rw⁻ 27 (q24 c4) ∷
   rw⁻ 26 (q13 c4) ∷
   rw⁻ 25 (q24 c4) ∷
   rw⁻ 24 (q13 c4) ∷ []) Eq.refl

private
  q26 : Ws → Eqn
  q26 c4 = sE 1404 (lem-F5-23-at132132 c4)
  q27 : Ws → Eqn
  q27 c4 = wlE 1417 (lit c4)
  q28 : Ws → Eqn
  q28 c4 = sE 1400 (lem-F4-K2-CS2-at132132 c4)
  q29 : Ws → Eqn
  q29 c4 = sE 1397 (lem-F4-CS2-K2-at132132 c4)
  q30 : Ws → Eqn
  q30 c4 = sE 1395 (lem-F4-CS2-CS2-at132132 c4)
  q31 : Ws → Eqn
  q31 c4 = sE 1389 (lem-F4-K2-K2-at132132 c4)
  q32 : Ws → Eqn
  q32 c4 = sE 1401 (lem-F4-S3-CS2-at132132 c4)
  q33 : Ws → Eqn
  q33 c4 = sE 1391 (lem-F4-S3-K2-at132132 c4)
  q34 : Ws → Eqn
  q34 c4 = sE 1392 (lem-F4-S3-S3-at132132 c4)
  q35 : Ws → Eqn
  q35 c4 = sE 1388 (lem-F4-I-S3-at132132 c4)
  q36 : Ws → Eqn
  q36 c4 = sE 1399 (lem-F4-I-CS2-at132132 c4)
  q37 : Ws → Eqn
  q37 c4 = sE 1387 (lem-F4-I-K2-at132132 c4)
  q38 : Ws → Eqn
  q38 c4 = sE 1390 (lem-F4-S3-I-at132132 c4)

-- deb-Q-hi-split-a @132132: 55 steps
lem-deb-Q-hi-split-a-at132132 : Ws → ⟪ (CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ
lem-deb-Q-hi-split-a-at132132 c4 = derive (CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 4 (q27 c4) ∷
   rw⁻ 3 (q28 c4) ∷
   rw⁻ 8 (q26 c4) ∷
   rw⁻ 7 (q29 c4) ∷
   rw⁻ 6 (q30 c4) ∷
   rw 12 (q27 c4) ∷
   rw⁻ 11 (q28 c4) ∷
   rw⁻ 10 (q31 c4) ∷
   rw⁻ 9 (q28 c4) ∷
   rw⁻ 16 (q26 c4) ∷
   rw⁻ 15 (q29 c4) ∷
   rw⁻ 14 (q30 c4) ∷
   rw⁻ 13 (q29 c4) ∷
   rw⁻ 12 (q30 c4) ∷
   rw 20 (q7 c4) ∷
   rw⁻ 19 (q32 c4) ∷
   rw⁻ 18 (q33 c4) ∷
   rw⁻ 17 (q32 c4) ∷
   rw⁻ 16 (q33 c4) ∷
   rw⁻ 15 (q32 c4) ∷
   rw 24 (q7 c4) ∷
   rw⁻ 23 (q34 c4) ∷
   rw⁻ 22 (q32 c4) ∷
   rw⁻ 21 (q33 c4) ∷
   rw⁻ 20 (q32 c4) ∷
   rw⁻ 19 (q33 c4) ∷
   rw⁻ 18 (q32 c4) ∷
   rw 28 (q7 c4) ∷
   rw⁻ 27 (q34 c4) ∷
   rw⁻ 26 (q34 c4) ∷
   rw⁻ 25 (q32 c4) ∷
   rw⁻ 24 (q33 c4) ∷
   rw⁻ 23 (q32 c4) ∷
   rw⁻ 22 (q33 c4) ∷
   rw⁻ 21 (q32 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw⁻ 31 (q35 c4) ∷
   rw⁻ 30 (q35 c4) ∷
   rw⁻ 29 (q35 c4) ∷
   rw⁻ 28 (q36 c4) ∷
   rw⁻ 27 (q37 c4) ∷
   rw⁻ 26 (q36 c4) ∷
   rw⁻ 25 (q37 c4) ∷
   rw⁻ 24 (q36 c4) ∷
   rw 36 (q7 c4) ∷
   rw⁻ 35 (q38 c4) ∷
   rw⁻ 34 (q34 c4) ∷
   rw⁻ 33 (q34 c4) ∷
   rw⁻ 32 (q34 c4) ∷
   rw⁻ 31 (q32 c4) ∷
   rw⁻ 30 (q33 c4) ∷
   rw⁻ 29 (q32 c4) ∷
   rw⁻ 28 (q33 c4) ∷
   rw⁻ 27 (q32 c4) ∷ []) Eq.refl

-- deb-Q-hi-split-b @132132: 45 steps
lem-deb-Q-hi-split-b-at132132 : Ws → ⟪ (CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ []) ⟫ʷ
lem-deb-Q-hi-split-b-at132132 c4 = derive (CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ [])
  (rw⁻ 0 (q26 c4) ∷
   rw 4 (q27 c4) ∷
   rw⁻ 3 (q28 c4) ∷
   rw⁻ 8 (q26 c4) ∷
   rw⁻ 7 (q29 c4) ∷
   rw⁻ 6 (q30 c4) ∷
   rw 12 (q27 c4) ∷
   rw⁻ 11 (q28 c4) ∷
   rw⁻ 10 (q31 c4) ∷
   rw⁻ 9 (q28 c4) ∷
   rw⁻ 16 (q26 c4) ∷
   rw⁻ 15 (q29 c4) ∷
   rw⁻ 14 (q30 c4) ∷
   rw⁻ 13 (q29 c4) ∷
   rw⁻ 12 (q30 c4) ∷
   rw 20 (q7 c4) ∷
   rw⁻ 19 (q32 c4) ∷
   rw⁻ 18 (q33 c4) ∷
   rw⁻ 17 (q32 c4) ∷
   rw⁻ 16 (q33 c4) ∷
   rw⁻ 15 (q32 c4) ∷
   rw 24 (q7 c4) ∷
   rw⁻ 23 (q34 c4) ∷
   rw⁻ 22 (q32 c4) ∷
   rw⁻ 21 (q33 c4) ∷
   rw⁻ 20 (q32 c4) ∷
   rw⁻ 19 (q33 c4) ∷
   rw⁻ 18 (q32 c4) ∷
   rw 28 (q7 c4) ∷
   rw⁻ 27 (q34 c4) ∷
   rw⁻ 26 (q34 c4) ∷
   rw⁻ 25 (q32 c4) ∷
   rw⁻ 24 (q33 c4) ∷
   rw⁻ 23 (q32 c4) ∷
   rw⁻ 22 (q33 c4) ∷
   rw⁻ 21 (q32 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw⁻ 31 (q35 c4) ∷
   rw⁻ 30 (q35 c4) ∷
   rw⁻ 29 (q35 c4) ∷
   rw⁻ 28 (q36 c4) ∷
   rw⁻ 27 (q37 c4) ∷
   rw⁻ 26 (q36 c4) ∷
   rw⁻ 25 (q37 c4) ∷
   rw⁻ 24 (q36 c4) ∷ []) Eq.refl

private
  q39 : Ws → Eqn
  q39 c4 = sE 1384 (lem-F4-S2-I c4)

-- deb-AD-split-a: 136 steps
lem-deb-AD-split-a : Ws → ⟪ (CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ
lem-deb-AD-split-a c4 = derive (CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw⁻ 11 (q5 c4) ∷
   rw⁻ 10 (q5 c4) ∷
   rw⁻ 9 (q5 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 15 (q5 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   rw⁻ 13 (q5 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   rw⁻ 20 (q1 c4) ∷
   rw⁻ 19 (q5 c4) ∷
   rw⁻ 18 (q5 c4) ∷
   rw⁻ 17 (q5 c4) ∷
   rw⁻ 16 (q5 c4) ∷
   rw⁻ 15 (q5 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 23 (q5 c4) ∷
   rw⁻ 22 (q5 c4) ∷
   rw⁻ 21 (q5 c4) ∷
   rw⁻ 20 (q5 c4) ∷
   rw⁻ 19 (q5 c4) ∷
   rw⁻ 18 (q5 c4) ∷
   rw 28 (q2 c4) ∷
   rw⁻ 27 (q3 c4) ∷
   rw⁻ 26 (q3 c4) ∷
   rw⁻ 25 (q3 c4) ∷
   rw⁻ 24 (q3 c4) ∷
   rw⁻ 23 (q3 c4) ∷
   rw⁻ 22 (q3 c4) ∷
   rw⁻ 21 (q3 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   rw⁻ 31 (q4 c4) ∷
   rw⁻ 30 (q5 c4) ∷
   rw⁻ 29 (q5 c4) ∷
   rw⁻ 28 (q5 c4) ∷
   rw⁻ 27 (q5 c4) ∷
   rw⁻ 26 (q5 c4) ∷
   rw⁻ 25 (q5 c4) ∷
   rw⁻ 24 (q5 c4) ∷
   rw 36 (q2 c4) ∷
   rw⁻ 35 (q3 c4) ∷
   rw⁻ 34 (q6 c4) ∷
   rw⁻ 33 (q3 c4) ∷
   rw⁻ 32 (q3 c4) ∷
   rw⁻ 31 (q3 c4) ∷
   rw⁻ 30 (q3 c4) ∷
   rw⁻ 29 (q3 c4) ∷
   rw⁻ 28 (q3 c4) ∷
   rw⁻ 27 (q3 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   rw⁻ 39 (q4 c4) ∷
   rw⁻ 38 (q5 c4) ∷
   rw⁻ 37 (q4 c4) ∷
   rw⁻ 36 (q5 c4) ∷
   rw⁻ 35 (q5 c4) ∷
   rw⁻ 34 (q5 c4) ∷
   rw⁻ 33 (q5 c4) ∷
   rw⁻ 32 (q5 c4) ∷
   rw⁻ 31 (q5 c4) ∷
   rw⁻ 30 (q5 c4) ∷
   rw 44 (q7 c4) ∷
   rw⁻ 43 (q8 c4) ∷
   rw⁻ 42 (q9 c4) ∷
   rw⁻ 41 (q8 c4) ∷
   rw⁻ 40 (q9 c4) ∷
   rw⁻ 39 (q8 c4) ∷
   rw⁻ 38 (q8 c4) ∷
   rw⁻ 37 (q8 c4) ∷
   rw⁻ 36 (q8 c4) ∷
   rw⁻ 35 (q8 c4) ∷
   rw⁻ 34 (q8 c4) ∷
   rw⁻ 33 (q8 c4) ∷
   rw 48 (q7 c4) ∷
   rw⁻ 47 (q10 c4) ∷
   rw⁻ 46 (q8 c4) ∷
   rw⁻ 45 (q9 c4) ∷
   rw⁻ 44 (q8 c4) ∷
   rw⁻ 43 (q9 c4) ∷
   rw⁻ 42 (q8 c4) ∷
   rw⁻ 41 (q8 c4) ∷
   rw⁻ 40 (q8 c4) ∷
   rw⁻ 39 (q8 c4) ∷
   rw⁻ 38 (q8 c4) ∷
   rw⁻ 37 (q8 c4) ∷
   rw⁻ 36 (q8 c4) ∷
   rw 52 (q7 c4) ∷
   rw⁻ 51 (q10 c4) ∷
   rw⁻ 50 (q10 c4) ∷
   rw⁻ 49 (q8 c4) ∷
   rw⁻ 48 (q9 c4) ∷
   rw⁻ 47 (q8 c4) ∷
   rw⁻ 46 (q9 c4) ∷
   rw⁻ 45 (q8 c4) ∷
   rw⁻ 44 (q8 c4) ∷
   rw⁻ 43 (q8 c4) ∷
   rw⁻ 42 (q8 c4) ∷
   rw⁻ 41 (q8 c4) ∷
   rw⁻ 40 (q8 c4) ∷
   rw⁻ 39 (q8 c4) ∷
   rw⁻ 56 (q11 c4) ∷
   rw⁻ 55 (q12 c4) ∷
   rw⁻ 54 (q12 c4) ∷
   rw⁻ 53 (q12 c4) ∷
   rw⁻ 52 (q13 c4) ∷
   rw⁻ 51 (q14 c4) ∷
   rw⁻ 50 (q13 c4) ∷
   rw⁻ 49 (q14 c4) ∷
   rw⁻ 48 (q13 c4) ∷
   rw⁻ 47 (q13 c4) ∷
   rw⁻ 46 (q13 c4) ∷
   rw⁻ 45 (q13 c4) ∷
   rw⁻ 44 (q13 c4) ∷
   rw⁻ 43 (q13 c4) ∷
   rw⁻ 42 (q13 c4) ∷
   rw 60 (q7 c4) ∷
   rw⁻ 59 (q39 c4) ∷
   rw⁻ 58 (q10 c4) ∷
   rw⁻ 57 (q10 c4) ∷
   rw⁻ 56 (q10 c4) ∷
   rw⁻ 55 (q8 c4) ∷
   rw⁻ 54 (q9 c4) ∷
   rw⁻ 53 (q8 c4) ∷
   rw⁻ 52 (q9 c4) ∷
   rw⁻ 51 (q8 c4) ∷
   rw⁻ 50 (q8 c4) ∷
   rw⁻ 49 (q8 c4) ∷
   rw⁻ 48 (q8 c4) ∷
   rw⁻ 47 (q8 c4) ∷
   rw⁻ 46 (q8 c4) ∷
   rw⁻ 45 (q8 c4) ∷ []) Eq.refl

private
  q40 : Ws → Eqn
  q40 c4 = sE 1363 (lem-F4-CS2-I c4)
  q41 : Ws → Eqn
  q41 c4 = sE 1393 (lem-F4-CS2-S2 c4)

-- deb-AD-split-b: 66 steps
lem-deb-AD-split-b : Ws → ⟪ (CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-deb-AD-split-b c4 = derive (CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 4 (q2 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 12 (q2 c4) ∷
   rw⁻ 11 (q3 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 15 (q4 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   rw⁻ 13 (q4 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   rw 20 (q7 c4) ∷
   rw⁻ 19 (q8 c4) ∷
   rw⁻ 18 (q9 c4) ∷
   rw⁻ 17 (q8 c4) ∷
   rw⁻ 16 (q9 c4) ∷
   rw⁻ 15 (q8 c4) ∷
   rw 24 (q7 c4) ∷
   rw⁻ 23 (q10 c4) ∷
   rw⁻ 22 (q8 c4) ∷
   rw⁻ 21 (q9 c4) ∷
   rw⁻ 20 (q8 c4) ∷
   rw⁻ 19 (q9 c4) ∷
   rw⁻ 18 (q8 c4) ∷
   rw 28 (q7 c4) ∷
   rw⁻ 27 (q10 c4) ∷
   rw⁻ 26 (q10 c4) ∷
   rw⁻ 25 (q8 c4) ∷
   rw⁻ 24 (q9 c4) ∷
   rw⁻ 23 (q8 c4) ∷
   rw⁻ 22 (q9 c4) ∷
   rw⁻ 21 (q8 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw⁻ 31 (q12 c4) ∷
   rw⁻ 30 (q12 c4) ∷
   rw⁻ 29 (q12 c4) ∷
   rw⁻ 28 (q13 c4) ∷
   rw⁻ 27 (q14 c4) ∷
   rw⁻ 26 (q13 c4) ∷
   rw⁻ 25 (q14 c4) ∷
   rw⁻ 24 (q13 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 35 (q40 c4) ∷
   rw⁻ 34 (q41 c4) ∷
   rw⁻ 33 (q41 c4) ∷
   rw⁻ 32 (q41 c4) ∷
   rw⁻ 31 (q5 c4) ∷
   rw⁻ 30 (q4 c4) ∷
   rw⁻ 29 (q5 c4) ∷
   rw⁻ 28 (q4 c4) ∷
   rw⁻ 27 (q5 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   rw⁻ 39 (q5 c4) ∷
   rw⁻ 38 (q40 c4) ∷
   rw⁻ 37 (q41 c4) ∷
   rw⁻ 36 (q41 c4) ∷
   rw⁻ 35 (q41 c4) ∷
   rw⁻ 34 (q5 c4) ∷
   rw⁻ 33 (q4 c4) ∷
   rw⁻ 32 (q5 c4) ∷
   rw⁻ 31 (q4 c4) ∷
   rw⁻ 30 (q5 c4) ∷ []) Eq.refl
