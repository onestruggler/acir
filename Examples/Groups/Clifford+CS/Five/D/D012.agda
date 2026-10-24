{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD012 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D012 (Sᴰ : SD012) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

-- The lemmas of other derivation modules (DSig).
private
  lem-comm-CS03-TOFF412 : Ws → St 190
  lem-comm-CS03-TOFF412 = pickᴰ 0 Sᴰ
  lem-comm-CSd03-TOFF412 : Ws → St 197
  lem-comm-CSd03-TOFF412 = pickᴰ 1 Sᴰ
  lem-comm-CSd04-TOFF213 : Ws → St 198
  lem-comm-CSd04-TOFF213 = pickᴰ 2 Sᴰ
  lem-comm-CSd12-TOFF403 : Ws → St 200
  lem-comm-CSd12-TOFF403 = pickᴰ 3 Sᴰ
  lem-comm-CSd14-TOFF023 : Ws → St 202
  lem-comm-CSd14-TOFF023 = pickᴰ 4 Sᴰ
  lem-comm-CSd23-TOFF014 : Ws → St 203
  lem-comm-CSd23-TOFF014 = pickᴰ 5 Sᴰ
  lem-comm-CX02-CCZ134 : Ws → St 0
  lem-comm-CX02-CCZ134 = pickᴰ 6 Sᴰ
  lem-comm-CX12-CCZ034 : Ws → St 2
  lem-comm-CX12-CCZ034 = pickᴰ 7 Sᴰ
  lem-comm-CX13-CCZ024 : Ws → St 3
  lem-comm-CX13-CCZ024 = pickᴰ 8 Sᴰ
  lem-comm-CX21-CCZ034 : Ws → St 5
  lem-comm-CX21-CCZ034 = pickᴰ 9 Sᴰ
  lem-comm-CX23-CCZ014 : Ws → St 6
  lem-comm-CX23-CCZ014 = pickᴰ 10 Sᴰ
  lem-comm-CX31-CCZ024 : Ws → St 8
  lem-comm-CX31-CCZ024 = pickᴰ 11 Sᴰ
  lem-comm-CZ03-TOFF412 : Ws → St 373
  lem-comm-CZ03-TOFF412 = pickᴰ 12 Sᴰ
  lem-comm-CZ04-TOFF213 : Ws → St 206
  lem-comm-CZ04-TOFF213 = pickᴰ 13 Sᴰ
  lem-comm-CZ04-TOFF312 : Ws → St 207
  lem-comm-CZ04-TOFF312 = pickᴰ 14 Sᴰ
  lem-comm-CZ14-TOFF023 : Ws → St 208
  lem-comm-CZ14-TOFF023 = pickᴰ 15 Sᴰ
  lem-comm-TOFF014-CSd23 : Ws → St 211
  lem-comm-TOFF014-CSd23 = pickᴰ 16 Sᴰ
  lem-comm-TOFF204-CSd13 : Ws → St 213
  lem-comm-TOFF204-CSd13 = pickᴰ 17 Sᴰ
  lem-comm-TOFF312-CSd04 : Ws → St 214
  lem-comm-TOFF312-CSd04 = pickᴰ 18 Sᴰ
  lem-comm-TOFF412-CSd03 : Ws → St 215
  lem-comm-TOFF412-CSd03 = pickᴰ 19 Sᴰ
  lem-comm-CS04-TOFF213 : Ws → St 284
  lem-comm-CS04-TOFF213 = pickᴰ 20 Sᴰ
  lem-comm-CS04-TOFF312 : Ws → St 217
  lem-comm-CS04-TOFF312 = pickᴰ 21 Sᴰ
  lem-comm-CS12-TOFF304 : Ws → St 285
  lem-comm-CS12-TOFF304 = pickᴰ 22 Sᴰ
  lem-comm-CS13-TOFF204 : Ws → St 218
  lem-comm-CS13-TOFF204 = pickᴰ 23 Sᴰ
  lem-comm-CS14-TOFF203 : Ws → St 336
  lem-comm-CS14-TOFF203 = pickᴰ 24 Sᴰ
  lem-comm-CS23-TOFF014 : Ws → St 286
  lem-comm-CS23-TOFF014 = pickᴰ 25 Sᴰ
  lem-comm-CSd02-TOFF314 : Ws → St 287
  lem-comm-CSd02-TOFF314 = pickᴰ 26 Sᴰ
  lem-comm-CSd03-TOFF214 : Ws → St 288
  lem-comm-CSd03-TOFF214 = pickᴰ 27 Sᴰ
  lem-comm-CSd04-TOFF312 : Ws → St 221
  lem-comm-CSd04-TOFF312 = pickᴰ 28 Sᴰ
  lem-comm-CSd12-TOFF304 : Ws → St 222
  lem-comm-CSd12-TOFF304 = pickᴰ 29 Sᴰ
  lem-comm-CSd13-TOFF204 : Ws → St 223
  lem-comm-CSd13-TOFF204 = pickᴰ 30 Sᴰ
  lem-comm-CSd14-TOFF203 : Ws → St 289
  lem-comm-CSd14-TOFF203 = pickᴰ 31 Sᴰ
  lem-comm-CSd14-TOFF302 : Ws → St 290
  lem-comm-CSd14-TOFF302 = pickᴰ 32 Sᴰ
  lem-comm-CSd23-TOFF401 : Ws → St 76
  lem-comm-CSd23-TOFF401 = pickᴰ 33 Sᴰ
  lem-comm-CSd24-TOFF301 : Ws → St 77
  lem-comm-CSd24-TOFF301 = pickᴰ 34 Sᴰ
  lem-comm-CX03-CCZ124 : Ws → St 18
  lem-comm-CX03-CCZ124 = pickᴰ 35 Sᴰ
  lem-comm-CX30-CCZ124 : Ws → St 19
  lem-comm-CX30-CCZ124 = pickᴰ 36 Sᴰ
  lem-comm-CX40-CCZ123 : Ws → St 20
  lem-comm-CX40-CCZ123 = pickᴰ 37 Sᴰ
  lem-comm-CX41-CCZ023 : Ws → St 21
  lem-comm-CX41-CCZ023 = pickᴰ 38 Sᴰ
  lem-comm-CZ02-TOFF314 : Ws → St 337
  lem-comm-CZ02-TOFF314 = pickᴰ 39 Sᴰ
  lem-comm-CZ12-TOFF304 : Ws → St 226
  lem-comm-CZ12-TOFF304 = pickᴰ 40 Sᴰ
  lem-comm-CZ12-TOFF403 : Ws → St 227
  lem-comm-CZ12-TOFF403 = pickᴰ 41 Sᴰ
  lem-comm-CZ13-TOFF204 : Ws → St 292
  lem-comm-CZ13-TOFF204 = pickᴰ 42 Sᴰ
  lem-comm-CZ14-TOFF302 : Ws → St 294
  lem-comm-CZ14-TOFF302 = pickᴰ 43 Sᴰ
  lem-comm-CZ23-TOFF014 : Ws → St 295
  lem-comm-CZ23-TOFF014 = pickᴰ 44 Sᴰ
  lem-comm-TOFF213-CSd04 : Ws → St 296
  lem-comm-TOFF213-CSd04 = pickᴰ 45 Sᴰ
  lem-comm-TOFF214-CSd03 : Ws → St 297
  lem-comm-TOFF214-CSd03 = pickᴰ 46 Sᴰ
  lem-comm-TOFF304-CSd12 : Ws → St 228
  lem-comm-TOFF304-CSd12 = pickᴰ 47 Sᴰ
  lem-comm-TOFF314-CSd02 : Ws → St 298
  lem-comm-TOFF314-CSd02 = pickᴰ 48 Sᴰ
  lem-comm-CK40-TOFF312 : Ws → St 374
  lem-comm-CK40-TOFF312 = pickᴰ 49 Sᴰ
  lem-comm-CS13-TOFF402 : Ws → St 375
  lem-comm-CS13-TOFF402 = pickᴰ 50 Sᴰ
  lem-comm-CS14-TOFF302 : Ws → St 338
  lem-comm-CS14-TOFF302 = pickᴰ 51 Sᴰ
  lem-comm-CSd02-TOFF413 : Ws → St 376
  lem-comm-CSd02-TOFF413 = pickᴰ 52 Sᴰ
  lem-comm-CSd13-TOFF402 : Ws → St 377
  lem-comm-CSd13-TOFF402 = pickᴰ 53 Sᴰ
  lem-comm-CX20-CCZ134 : Ws → St 44
  lem-comm-CX20-CCZ134 = pickᴰ 54 Sᴰ
  lem-comm-CZ13-TOFF402 : Ws → St 378
  lem-comm-CZ13-TOFF402 = pickᴰ 55 Sᴰ
  lem-comm-TOFF402-CSd13 : Ws → St 379
  lem-comm-TOFF402-CSd13 = pickᴰ 56 Sᴰ
  lem-comm-TOFF413-CSd02 : Ws → St 380
  lem-comm-TOFF413-CSd02 = pickᴰ 57 Sᴰ
  lem-comm-CS02-TOFF413 : Ws → St 381
  lem-comm-CS02-TOFF413 = pickᴰ 58 Sᴰ
  lem-comm-CS12-TOFF403 : Ws → St 382
  lem-comm-CS12-TOFF403 = pickᴰ 59 Sᴰ
  lem-comm-TOFF403-CSd12 : Ws → St 383
  lem-comm-TOFF403-CSd12 = pickᴰ 60 Sᴰ
  lem-comm-TOFF203-CSd14 : Ws → St 299
  lem-comm-TOFF203-CSd14 = pickᴰ 61 Sᴰ
  lem-comm-TOFF302-CSd14 : Ws → St 339
  lem-comm-TOFF302-CSd14 = pickᴰ 62 Sᴰ
  lem-box-tQ-at033440 : Ws → St 340
  lem-box-tQ-at033440 = pickᴰ 63 Sᴰ
  lem-box-tQ-at2442 : Ws → St 343
  lem-box-tQ-at2442 = pickᴰ 64 Sᴰ
  lem-CXbc-box-at021021 : Ws → St 384
  lem-CXbc-box-at021021 = pickᴰ 65 Sᴰ
  lem-CXbc-box-at0210213443 : Ws → St 385
  lem-CXbc-box-at0210213443 = pickᴰ 66 Sᴰ
  lem-CXbc-box-at0214233041 : Ws → St 386
  lem-CXbc-box-at0214233041 = pickᴰ 67 Sᴰ
  lem-CXbc-box-at0410213243 : Ws → St 387
  lem-CXbc-box-at0410213243 = pickᴰ 68 Sᴰ
  lem-CXcb-box-at021021 : Ws → St 388
  lem-CXcb-box-at021021 = pickᴰ 69 Sᴰ
  lem-CXcb-box-at0210213443 : Ws → St 389
  lem-CXcb-box-at0210213443 = pickᴰ 70 Sᴰ
  lem-CXcb-box-at0214233041 : Ws → St 390
  lem-CXcb-box-at0214233041 = pickᴰ 71 Sᴰ
  lem-CXcb-box-at0410213243 : Ws → St 391
  lem-CXcb-box-at0410213243 = pickᴰ 72 Sᴰ
  lem-VPQ-at0213243041 : Ws → St 392
  lem-VPQ-at0213243041 = pickᴰ 73 Sᴰ
  lem-VPQ-at0214233041 : Ws → St 393
  lem-VPQ-at0214233041 = pickᴰ 74 Sᴰ
  lem-VPQ-at0310213442 : Ws → St 394
  lem-VPQ-at0310213442 = pickᴰ 75 Sᴰ
  lem-box-tQ-at02102331 : Ws → St 395
  lem-box-tQ-at02102331 = pickᴰ 76 Sᴰ
  lem-box-tQ-at02102441 : Ws → St 348
  lem-box-tQ-at02102441 = pickᴰ 77 Sᴰ
  lem-box-tQ-at02132031 : Ws → St 396
  lem-box-tQ-at02132031 = pickᴰ 78 Sᴰ
  lem-box-tQ-at02132130 : Ws → St 397
  lem-box-tQ-at02132130 = pickᴰ 79 Sᴰ
  lem-box-tQ-at02142041 : Ws → St 349
  lem-box-tQ-at02142041 = pickᴰ 80 Sᴰ
  lem-box-tQ-at0310243241 : Ws → St 350
  lem-box-tQ-at0310243241 = pickᴰ 81 Sᴰ
  lem-box-tQ-at031031 : Ws → St 351
  lem-box-tQ-at031031 = pickᴰ 82 Sᴰ
  lem-box-tQ-at03122031 : Ws → St 398
  lem-box-tQ-at03122031 = pickᴰ 83 Sᴰ
  lem-box-tQ-at03122130 : Ws → St 399
  lem-box-tQ-at03122130 = pickᴰ 84 Sᴰ
  lem-box-tQ-at0312243041 : Ws → St 354
  lem-box-tQ-at0312243041 = pickᴰ 85 Sᴰ
  lem-box-tQ-at0314203241 : Ws → St 400
  lem-box-tQ-at0314203241 = pickᴰ 86 Sᴰ
  lem-box-tQ-at03143041 : Ws → St 356
  lem-box-tQ-at03143041 = pickᴰ 87 Sᴰ
  lem-box-tQ-at03243042 : Ws → St 401
  lem-box-tQ-at03243042 = pickᴰ 88 Sᴰ
  lem-box-tQ-at04103143 : Ws → St 402
  lem-box-tQ-at04103143 = pickᴰ 89 Sᴰ
  lem-box-tQ-at04122041 : Ws → St 403
  lem-box-tQ-at04122041 = pickᴰ 90 Sᴰ
  lem-box-tQ-at142142 : Ws → St 404
  lem-box-tQ-at142142 = pickᴰ 91 Sᴰ
  lem-tP-at02102331 : Ws → St 405
  lem-tP-at02102331 = pickᴰ 92 Sᴰ
  lem-tP-at02102441 : Ws → St 359
  lem-tP-at02102441 = pickᴰ 93 Sᴰ
  lem-tP-at02132031 : Ws → St 406
  lem-tP-at02132031 = pickᴰ 94 Sᴰ
  lem-tP-at02132130 : Ws → St 407
  lem-tP-at02132130 = pickᴰ 95 Sᴰ
  lem-tP-at0214203143 : Ws → St 332
  lem-tP-at0214203143 = pickᴰ 96 Sᴰ
  lem-tP-at02142041 : Ws → St 408
  lem-tP-at02142041 = pickᴰ 97 Sᴰ
  lem-tP-at0310243241 : Ws → St 361
  lem-tP-at0310243241 = pickᴰ 98 Sᴰ
  lem-tP-at031031 : Ws → St 362
  lem-tP-at031031 = pickᴰ 99 Sᴰ
  lem-tP-at03122031 : Ws → St 409
  lem-tP-at03122031 = pickᴰ 100 Sᴰ
  lem-tP-at03122130 : Ws → St 410
  lem-tP-at03122130 = pickᴰ 101 Sᴰ
  lem-tP-at0312243041 : Ws → St 365
  lem-tP-at0312243041 = pickᴰ 102 Sᴰ
  lem-tP-at0314203241 : Ws → St 411
  lem-tP-at0314203241 = pickᴰ 103 Sᴰ
  lem-tP-at03143041 : Ws → St 412
  lem-tP-at03143041 = pickᴰ 104 Sᴰ
  lem-tP-at03243042 : Ws → St 413
  lem-tP-at03243042 = pickᴰ 105 Sᴰ
  lem-tP-at033440 : Ws → St 369
  lem-tP-at033440 = pickᴰ 106 Sᴰ
  lem-tP-at04103143 : Ws → St 414
  lem-tP-at04103143 = pickᴰ 107 Sᴰ
  lem-tP-at04122041 : Ws → St 415
  lem-tP-at04122041 = pickᴰ 108 Sᴰ
  lem-tP-at0412233041 : Ws → St 416
  lem-tP-at0412233041 = pickᴰ 109 Sᴰ
  lem-tP-at04233042 : Ws → St 417
  lem-tP-at04233042 = pickᴰ 110 Sᴰ
  lem-tP-at142142 : Ws → St 418
  lem-tP-at142142 = pickᴰ 111 Sᴰ
  lem-tP-at2442 : Ws → St 372
  lem-tP-at2442 = pickᴰ 112 Sᴰ
  lem-box-tQ-at0410233241 : Ws → St 419
  lem-box-tQ-at0410233241 = pickᴰ 113 Sᴰ
  lem-box-tQ-at041041 : Ws → St 420
  lem-box-tQ-at041041 = pickᴰ 114 Sᴰ
  lem-box-tQ-at0412233041 : Ws → St 421
  lem-box-tQ-at0412233041 = pickᴰ 115 Sᴰ
  lem-box-tQ-at0413203142 : Ws → St 422
  lem-box-tQ-at0413203142 = pickᴰ 116 Sᴰ
  lem-box-tQ-at0413213042 : Ws → St 423
  lem-box-tQ-at0413213042 = pickᴰ 117 Sᴰ
  lem-box-tQ-at04233240 : Ws → St 424
  lem-box-tQ-at04233240 = pickᴰ 118 Sᴰ
  lem-box-tQ-at0440 : Ws → St 425
  lem-box-tQ-at0440 = pickᴰ 119 Sᴰ
  lem-tP-at02142140 : Ws → St 426
  lem-tP-at02142140 = pickᴰ 120 Sᴰ
  lem-tP-at0410233241 : Ws → St 427
  lem-tP-at0410233241 = pickᴰ 121 Sᴰ
  lem-tP-at0412213043 : Ws → St 428
  lem-tP-at0412213043 = pickᴰ 122 Sᴰ
  lem-tP-at0413203142 : Ws → St 429
  lem-tP-at0413203142 = pickᴰ 123 Sᴰ
  lem-tP-at0440 : Ws → St 430
  lem-tP-at0440 = pickᴰ 124 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 349 (lem-box-tQ-at02142041 c4)
  q2 : Ws → Eqn
  q2 c4 = wpE 1151 c4
  q3 : Ws → Eqn
  q3 c4 = wlE 1323 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = wlE 1324 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = wlE 707 (lit c4)
  q6 : Ws → Eqn
  q6 c4 = wpE 1152 c4
  q7 : Ws → Eqn
  q7 c4 = wpE 945 c4
  q8 : Ws → Eqn
  q8 c4 = sE 223 (lem-comm-CSd13-TOFF204 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 218 (lem-comm-CS13-TOFF204 c4)
  q10 : Ws → Eqn
  q10 c4 = wpE 1153 c4
  q11 : Ws → Eqn
  q11 c4 = wpE 1154 c4
  q12 : Ws → Eqn
  q12 c4 = wlE 618 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = wpE 759 c4

-- CXcb-box @02142041: 18 steps
lem-CXcb-box-at02142041 : Ws → ⟪ (ℓ "买余买") ⟫ʷ ≈ ⟪ (ℓ "余京") ⟫ʷ
lem-CXcb-box-at02142041 c4 = derive (ℓ "买余买") (ℓ "余京")
  (rw 1 (q1 c4) ∷
   rw 0 (q2 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 1 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   rw 8 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw 6 (q8 c4) ∷
   rw 5 (q7 c4) ∷
   rw 4 (q9 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   rw 2 (q2 c4) ∷
   rw 3 (q11 c4) ∷
   rw⁻ 4 (q12 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q13 c4) ∷ []) Eq.refl

private
  q14 : Ws → Eqn
  q14 c4 = wlE 421 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = sE 393 (lem-VPQ-at0214233041 c4)
  q16 : Ws → Eqn
  q16 c4 = wlE 341 (lit c4)

-- QVQ @0214233041: 3 steps
lem-QVQ-at0214233041 : Ws → ⟪ (ℓ "二亱亰二") ⟫ʷ ≈ ⟪ (ℓ "亏亱亰亏") ⟫ʷ
lem-QVQ-at0214233041 c4 = derive (ℓ "二亱亰二") (ℓ "亏亱亰亏")
  (rw⁻ 0 (q14 c4) ∷
   rw⁻ 1 (q15 c4) ∷
   rw 4 (q16 c4) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = sE 400 (lem-box-tQ-at0314203241 c4)
  q18 : Ws → Eqn
  q18 c4 = wpE 1059 c4
  q19 : Ws → Eqn
  q19 c4 = wlE 1325 (lit c4)
  q20 : Ws → Eqn
  q20 c4 = wpE 1159 c4
  q21 : Ws → Eqn
  q21 c4 = wpE 1143 c4
  q22 : Ws → Eqn
  q22 c4 = wlE 765 (lit c4)
  q23 : Ws → Eqn
  q23 c4 = sE 20 (lem-comm-CX40-CCZ123 c4)
  q24 : Ws → Eqn
  q24 c4 = wlE 1321 (lit c4)
  q25 : Ws → Eqn
  q25 c4 = wlE 763 (lit c4)
  q26 : Ws → Eqn
  q26 c4 = wlE 327 (lit c4)
  q27 : Ws → Eqn
  q27 c4 = wlE 1326 (lit c4)
  q28 : Ws → Eqn
  q28 c4 = wpE 378 c4

-- CXbc-box @0314203241: 17 steps
lem-CXbc-box-at0314203241 : Ws → ⟪ (ℓ "丳佾丳") ⟫ʷ ≈ ⟪ (ℓ "佾五") ⟫ʷ
lem-CXbc-box-at0314203241 c4 = derive (ℓ "丳佾丳") (ℓ "佾五")
  (rw 1 (q17 c4) ∷
   rw 0 (q18 c4) ∷
   rw⁻ 1 (q19 c4) ∷
   rw 3 (q20 c4) ∷
   rw 2 (q18 c4) ∷
   rw 5 (q21 c4) ∷
   rw⁻ 9 (q22 c4) ∷
   rw 8 (q23 c4) ∷
   rw⁻ 7 (q24 c4) ∷
   rw 6 (q23 c4) ∷
   rw⁻ 5 (q25 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   rw 4 (q26 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw 4 (q27 c4) ∷
   rw⁻ 0 (q17 c4) ∷
   rw⁻ 1 (q28 c4) ∷ []) Eq.refl

private
  q29 : Ws → Eqn
  q29 c4 = wpE 1160 c4
  q30 : Ws → Eqn
  q30 c4 = wlE 1327 (lit c4)
  q31 : Ws → Eqn
  q31 c4 = wlE 482 (lit c4)
  q32 : Ws → Eqn
  q32 c4 = wlE 702 (lit c4)
  q33 : Ws → Eqn
  q33 c4 = wpE 1037 c4
  q34 : Ws → Eqn
  q34 c4 = wpE 1055 c4
  q35 : Ws → Eqn
  q35 c4 = sE 222 (lem-comm-CSd12-TOFF304 c4)
  q36 : Ws → Eqn
  q36 c4 = sE 285 (lem-comm-CS12-TOFF304 c4)
  q37 : Ws → Eqn
  q37 c4 = wpE 1144 c4
  q38 : Ws → Eqn
  q38 c4 = wpE 1161 c4
  q39 : Ws → Eqn
  q39 c4 = wlE 770 (lit c4)
  q40 : Ws → Eqn
  q40 c4 = wpE 380 c4

-- CXcb-box @0314203241: 18 steps
lem-CXcb-box-at0314203241 : Ws → ⟪ (ℓ "乜佾乜") ⟫ʷ ≈ ⟪ (ℓ "佾亨") ⟫ʷ
lem-CXcb-box-at0314203241 c4 = derive (ℓ "乜佾乜") (ℓ "佾亨")
  (rw 1 (q17 c4) ∷
   rw 0 (q29 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw⁻ 1 (q31 c4) ∷
   rw 4 (q32 c4) ∷
   rw 8 (q33 c4) ∷
   rw 7 (q34 c4) ∷
   rw 6 (q35 c4) ∷
   rw 5 (q34 c4) ∷
   rw 4 (q36 c4) ∷
   rw⁻ 5 (q32 c4) ∷
   rw⁻ 3 (q37 c4) ∷
   rw 2 (q29 c4) ∷
   rw 3 (q38 c4) ∷
   rw⁻ 4 (q39 c4) ∷
   rw⁻ 3 (q31 c4) ∷
   rw⁻ 0 (q17 c4) ∷
   rw⁻ 1 (q40 c4) ∷ []) Eq.refl

private
  q41 : Ws → Eqn
  q41 c4 = wlE 423 (lit c4)
  q42 : Ws → Eqn
  q42 c4 = sE 385 (lem-CXbc-box-at0210213443 c4)
  q43 : Ws → Eqn
  q43 c4 = wpE 567 c4
  q44 : Ws → Eqn
  q44 c4 = sE 389 (lem-CXcb-box-at0210213443 c4)
  q45 : Ws → Eqn
  q45 c4 = wpE 189 c4
  q46 : Ws → Eqn
  q46 c4 = wpE 566 c4
  q47 : Ws → Eqn
  q47 c4 = wpE 769 c4
  q48 : Ws → Eqn
  q48 c4 = wlE 230 (lit c4)

-- SWbc-box @0210213443: 11 steps
lem-SWbc-box-at0210213443 : Ws → ⟪ (ℓ "乘伮乘") ⟫ʷ ≈ ⟪ (ℓ "伮") ⟫ʷ
lem-SWbc-box-at0210213443 c4 = derive (ℓ "乘伮乘") (ℓ "伮")
  (rw⁻ 0 (q41 c4) ∷
   rw⁻ 4 (q41 c4) ∷
   rw 2 (q42 c4) ∷
   rw 3 (q43 c4) ∷
   rw 1 (q44 c4) ∷
   rw 4 (q45 c4) ∷
   rw 3 (q46 c4) ∷
   rw 2 (q46 c4) ∷
   rw 3 (q47 c4) ∷
   rw 0 (q42 c4) ∷
   rw 1 (q48 c4) ∷ []) Eq.refl

private
  q49 : Ws → Eqn
  q49 c4 = wlE 923 (lit c4)
  q50 : Ws → Eqn
  q50 c4 = sE 386 (lem-CXbc-box-at0214233041 c4)
  q51 : Ws → Eqn
  q51 c4 = wpE 762 c4
  q52 : Ws → Eqn
  q52 c4 = sE 390 (lem-CXcb-box-at0214233041 c4)
  q53 : Ws → Eqn
  q53 c4 = wpE 705 c4
  q54 : Ws → Eqn
  q54 c4 = wpE 763 c4
  q55 : Ws → Eqn
  q55 c4 = wpE 764 c4
  q56 : Ws → Eqn
  q56 c4 = wlE 321 (lit c4)

-- SWbc-box @0214233041: 11 steps
lem-SWbc-box-at0214233041 : Ws → ⟪ (ℓ "丹佢丹") ⟫ʷ ≈ ⟪ (ℓ "佢") ⟫ʷ
lem-SWbc-box-at0214233041 c4 = derive (ℓ "丹佢丹") (ℓ "佢")
  (rw⁻ 0 (q49 c4) ∷
   rw⁻ 4 (q49 c4) ∷
   rw 2 (q50 c4) ∷
   rw 3 (q51 c4) ∷
   rw 1 (q52 c4) ∷
   rw 4 (q53 c4) ∷
   rw 3 (q54 c4) ∷
   rw 2 (q54 c4) ∷
   rw 3 (q55 c4) ∷
   rw 0 (q50 c4) ∷
   rw 1 (q56 c4) ∷ []) Eq.refl

private
  q57 : Ws → Eqn
  q57 c4 = sE 354 (lem-box-tQ-at0312243041 c4)
  q58 : Ws → Eqn
  q58 c4 = sE 365 (lem-tP-at0312243041 c4)
  q59 : Ws → Eqn
  q59 c4 = wlE 866 (lit c4)
  q60 : Ws → Eqn
  q60 c4 = wlE 867 (lit c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (ℓ "个亲") (ℓ "亲个") (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI))
  q62 : Ws → Eqn
  q62 c4 = wlE 868 (lit c4)

-- P-box @0312243041: 8 steps
lem-P-box-at0312243041 : Ws → ⟪ (ℓ "亓佴亓") ⟫ʷ ≈ ⟪ (ℓ "佴") ⟫ʷ
lem-P-box-at0312243041 c4 = derive (ℓ "亓佴亓") (ℓ "佴")
  (rw 1 (q57 c4) ∷
   rw⁻ 0 (q58 c4) ∷
   rw⁻ 1 (q59 c4) ∷
   rw⁻ 3 (q58 c4) ∷
   rw⁻ 4 (q60 c4) ∷
   rw 2 (q61 c4) ∷
   rw⁻ 3 (q62 c4) ∷
   rw⁻ 0 (q57 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = sE 348 (lem-box-tQ-at02102441 c4)
  q64 : Ws → Eqn
  q64 c4 = sE 359 (lem-tP-at02102441 c4)
  q65 : Ws → Eqn
  q65 c4 = wlE 912 (lit c4)
  q66 : Ws → Eqn
  q66 c4 = wlE 913 (lit c4)
  q67 : Ws → Eqn
  q67 c4 = sE 292 (lem-comm-CZ13-TOFF204 c4)
  q68 : Ws → Eqn
  q68 c4 = wlE 914 (lit c4)

-- P-box @02102441: 8 steps
lem-P-box-at02102441 : Ws → ⟪ (ℓ "亦伲亦") ⟫ʷ ≈ ⟪ (ℓ "伲") ⟫ʷ
lem-P-box-at02102441 c4 = derive (ℓ "亦伲亦") (ℓ "伲")
  (rw 1 (q63 c4) ∷
   rw⁻ 0 (q64 c4) ∷
   rw⁻ 1 (q65 c4) ∷
   rw⁻ 3 (q64 c4) ∷
   rw⁻ 4 (q66 c4) ∷
   rw 2 (q67 c4) ∷
   rw⁻ 3 (q68 c4) ∷
   rw⁻ 0 (q63 c4) ∷ []) Eq.refl

private
  q69 : Ws → Eqn
  q69 c4 = sE 397 (lem-box-tQ-at02132130 c4)
  q70 : Ws → Eqn
  q70 c4 = wlE 920 (lit c4)
  q71 : Ws → Eqn
  q71 c4 = wpE 1190 c4
  q72 : Ws → Eqn
  q72 c4 = wlE 1336 (lit c4)
  q73 : Ws → Eqn
  q73 c4 = wlE 831 (lit c4)
  q74 : Ws → Eqn
  q74 c4 = wpE 36 c4
  q75 : Ws → Eqn
  q75 c4 = sE 8 (lem-comm-CX31-CCZ024 c4)
  q76 : Ws → Eqn
  q76 c4 = wpE 746 c4
  q77 : Ws → Eqn
  q77 c4 = wpE 34 c4
  q78 : Ws → Eqn
  q78 c4 = wpE 827 c4
  q79 : Ws → Eqn
  q79 c4 = wpE 1191 c4
  q80 : Ws → Eqn
  q80 c4 = wpE 505 c4

-- CXbc-box @02132130: 17 steps
lem-CXbc-box-at02132130 : Ws → ⟪ (ℓ "乄佅乄") ⟫ʷ ≈ ⟪ (ℓ "佅京") ⟫ʷ
lem-CXbc-box-at02132130 c4 = derive (ℓ "乄佅乄") (ℓ "佅京")
  (rw 1 (q69 c4) ∷
   rw 0 (q70 c4) ∷
   rw⁻ 1 (q71 c4) ∷
   rw 3 (q72 c4) ∷
   rw 2 (q70 c4) ∷
   rw 5 (q73 c4) ∷
   rw⁻ 9 (q74 c4) ∷
   rw 8 (q75 c4) ∷
   rw⁻ 7 (q76 c4) ∷
   rw 6 (q75 c4) ∷
   rw⁻ 5 (q77 c4) ∷
   rw⁻ 6 (q73 c4) ∷
   rw⁻ 4 (q78 c4) ∷
   rw⁻ 3 (q71 c4) ∷
   rw 4 (q79 c4) ∷
   rw⁻ 0 (q69 c4) ∷
   rw⁻ 1 (q80 c4) ∷ []) Eq.refl

private
  q81 : Ws → Eqn
  q81 c4 = wlE 1337 (lit c4)
  q82 : Ws → Eqn
  q82 c4 = wpE 1192 c4
  q83 : Ws → Eqn
  q83 c4 = wpE 22 c4
  q84 : Ws → Eqn
  q84 c4 = wpE 1193 c4
  q85 : Ws → Eqn
  q85 c4 = wlE 808 (lit c4)
  q86 : Ws → Eqn
  q86 c4 = wlE 917 (lit c4)
  q87 : Ws → Eqn
  q87 c4 = sE 198 (lem-comm-CSd04-TOFF213 c4)
  q88 : Ws → Eqn
  q88 c4 = sE 284 (lem-comm-CS04-TOFF213 c4)
  q89 : Ws → Eqn
  q89 c4 = wlE 1338 (lit c4)
  q90 : Ws → Eqn
  q90 c4 = wlE 1339 (lit c4)
  q91 : Ws → Eqn
  q91 c4 = wpE 109 c4
  q92 : Ws → Eqn
  q92 c4 = wpE 499 c4

-- CXcb-box @02132130: 18 steps
lem-CXcb-box-at02132130 : Ws → ⟪ (ℓ "丬佅丬") ⟫ʷ ≈ ⟪ (ℓ "佅亠") ⟫ʷ
lem-CXcb-box-at02132130 c4 = derive (ℓ "丬佅丬") (ℓ "佅亠")
  (rw 1 (q69 c4) ∷
   rw 0 (q81 c4) ∷
   rw⁻ 2 (q82 c4) ∷
   rw⁻ 1 (q83 c4) ∷
   rw 4 (q84 c4) ∷
   rw 8 (q85 c4) ∷
   rw 7 (q86 c4) ∷
   rw 6 (q87 c4) ∷
   rw 5 (q86 c4) ∷
   rw 4 (q88 c4) ∷
   rw⁻ 5 (q84 c4) ∷
   rw 3 (q89 c4) ∷
   rw 2 (q81 c4) ∷
   rw 3 (q90 c4) ∷
   rw⁻ 4 (q91 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   rw⁻ 0 (q69 c4) ∷
   rw⁻ 1 (q92 c4) ∷ []) Eq.refl

private
  q93 : Ws → Eqn
  q93 c4 = sE 356 (lem-box-tQ-at03143041 c4)
  q94 : Ws → Eqn
  q94 c4 = sE 412 (lem-tP-at03143041 c4)

-- P-box @03143041: 8 steps
lem-P-box-at03143041 : Ws → ⟪ (ℓ "亓侈亓") ⟫ʷ ≈ ⟪ (ℓ "侈") ⟫ʷ
lem-P-box-at03143041 c4 = derive (ℓ "亓侈亓") (ℓ "侈")
  (rw 1 (q93 c4) ∷
   rw⁻ 0 (q94 c4) ∷
   rw⁻ 1 (q59 c4) ∷
   rw⁻ 3 (q94 c4) ∷
   rw⁻ 4 (q60 c4) ∷
   rw 2 (q61 c4) ∷
   rw⁻ 3 (q62 c4) ∷
   rw⁻ 0 (q93 c4) ∷ []) Eq.refl

private
  q95 : Ws → Eqn
  q95 c4 = wlE 438 (lit c4)
  q96 : Ws → Eqn
  q96 c4 = wlE 437 (lit c4)
  q97 : Ws → Eqn
  q97 c4 = eqn (ℓ "丩丝") (ℓ "丝丩") (c₂ (CS • CS • CS) ((S • S • S) ↑))
  q98 : Ws → Eqn
  q98 c4 = eqn (ℓ "丩亲") (ℓ "亲丩") (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI))
  q99 : Ws → Eqn
  q99 c4 = eqn (ℓ "丩东") (ℓ "东丩") (c₂ (CS • CS • CS) (S ↑))
  q100 : Ws → Eqn
  q100 c4 = eqn (ℓ "丩乪") (ℓ "乪丩") (c₂ (CS • CS • CS) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q101 : Ws → Eqn
  q101 c4 = wlE 441 (lit c4)
  q102 : Ws → Eqn
  q102 c4 = wlE 440 (lit c4)
  q103 : Ws → Eqn
  q103 c4 = sE 77 (lem-comm-CSd24-TOFF301 c4)
  q104 : Ws → Eqn
  q104 c4 = wlE 439 (lit c4)

-- VPQ @03143041: 14 steps
lem-VPQ-at03143041 : Ws → ⟪ (ℓ "亲亰亓亐") ⟫ʷ ≈ ⟪ (ℓ "亓亐亲亰") ⟫ʷ
lem-VPQ-at03143041 c4 = derive (ℓ "亲亰亓亐") (ℓ "亓亐亲亰")
  (rw⁻ 0 (q95 c4) ∷
   rw⁻ 4 (q96 c4) ∷
   rw⁻ 3 (q97 c4) ∷
   rw⁻ 2 (q98 c4) ∷
   rw⁻ 1 (q99 c4) ∷
   rw⁻ 0 (q100 c4) ∷
   rw 4 (q101 c4) ∷
   rw 3 (q94 c4) ∷
   rw⁻ 4 (q101 c4) ∷
   rw 1 (q102 c4) ∷
   rw 2 (q103 c4) ∷
   rw 3 (q104 c4) ∷
   rw 0 (q96 c4) ∷
   rw 2 (q95 c4) ∷ []) Eq.refl

private
  q105 : Ws → Eqn
  q105 c4 = wlE 630 (lit c4)
  q106 : Ws → Eqn
  q106 c4 = wlE 629 (lit c4)
  q107 : Ws → Eqn
  q107 c4 = wlE 634 (lit c4)
  q108 : Ws → Eqn
  q108 c4 = sE 299 (lem-comm-TOFF203-CSd14 c4)
  q109 : Ws → Eqn
  q109 c4 = wlE 633 (lit c4)
  q110 : Ws → Eqn
  q110 c4 = wpE 514 c4
  q111 : Ws → Eqn
  q111 c4 = wlE 179 (lit c4)
  q112 : Ws → Eqn
  q112 c4 = sE 406 (lem-tP-at02132031 c4)
  q113 : Ws → Eqn
  q113 c4 = wlE 632 (lit c4)
  q114 : Ws → Eqn
  q114 c4 = sE 288 (lem-comm-CSd03-TOFF214 c4)
  q115 : Ws → Eqn
  q115 c4 = wlE 631 (lit c4)

-- VPQ @02132031: 14 steps
lem-VPQ-at02132031 : Ws → ⟪ (ℓ "亚亘亪亨") ⟫ʷ ≈ ⟪ (ℓ "亪亨亚亘") ⟫ʷ
lem-VPQ-at02132031 c4 = derive (ℓ "亚亘亪亨") (ℓ "亪亨亚亘")
  (rw⁻ 0 (q105 c4) ∷
   rw⁻ 4 (q106 c4) ∷
   rw⁻ 3 (q107 c4) ∷
   rw 2 (q108 c4) ∷
   rw⁻ 1 (q109 c4) ∷
   rw 0 (q110 c4) ∷
   rw 4 (q111 c4) ∷
   rw 3 (q112 c4) ∷
   rw⁻ 4 (q111 c4) ∷
   rw 1 (q113 c4) ∷
   rw 2 (q114 c4) ∷
   rw 3 (q115 c4) ∷
   rw 0 (q106 c4) ∷
   rw 2 (q105 c4) ∷ []) Eq.refl

private
  q116 : Ws → Eqn
  q116 c4 = wlE 442 (lit c4)
  q117 : Ws → Eqn
  q117 c4 = sE 394 (lem-VPQ-at0310213442 c4)
  q118 : Ws → Eqn
  q118 c4 = wlE 305 (lit c4)

-- QVQ @0310213442: 3 steps
lem-QVQ-at0310213442 : Ws → ⟪ (ℓ "亰亓亐亰") ⟫ʷ ≈ ⟪ (ℓ "亲亓亐亲") ⟫ʷ
lem-QVQ-at0310213442 c4 = derive (ℓ "亰亓亐亰") (ℓ "亲亓亐亲")
  (rw⁻ 0 (q116 c4) ∷
   rw⁻ 1 (q117 c4) ∷
   rw 4 (q118 c4) ∷ []) Eq.refl

private
  q119 : Ws → Eqn
  q119 c4 = sE 396 (lem-box-tQ-at02132031 c4)
  q120 : Ws → Eqn
  q120 c4 = wlE 1348 (lit c4)
  q121 : Ws → Eqn
  q121 c4 = wpE 1196 c4
  q122 : Ws → Eqn
  q122 c4 = wpE 1197 c4
  q123 : Ws → Eqn
  q123 c4 = wlE 471 (lit c4)
  q124 : Ws → Eqn
  q124 c4 = sE 19 (lem-comm-CX30-CCZ124 c4)
  q125 : Ws → Eqn
  q125 c4 = wpE 318 c4
  q126 : Ws → Eqn
  q126 c4 = wpE 384 c4
  q127 : Ws → Eqn
  q127 c4 = wpE 1198 c4

-- CXbc-box @02132031: 17 steps
lem-CXbc-box-at02132031 : Ws → ⟪ (ℓ "丬似丬") ⟫ʷ ≈ ⟪ (ℓ "似亠") ⟫ʷ
lem-CXbc-box-at02132031 c4 = derive (ℓ "丬似丬") (ℓ "似亠")
  (rw 1 (q119 c4) ∷
   rw 0 (q120 c4) ∷
   rw⁻ 1 (q121 c4) ∷
   rw 3 (q122 c4) ∷
   rw 2 (q120 c4) ∷
   rw 5 (q84 c4) ∷
   rw⁻ 9 (q123 c4) ∷
   rw 8 (q124 c4) ∷
   rw⁻ 7 (q125 c4) ∷
   rw 6 (q124 c4) ∷
   rw⁻ 5 (q126 c4) ∷
   rw⁻ 6 (q84 c4) ∷
   rw 4 (q78 c4) ∷
   rw⁻ 3 (q121 c4) ∷
   rw 4 (q127 c4) ∷
   rw⁻ 0 (q119 c4) ∷
   rw⁻ 1 (q92 c4) ∷ []) Eq.refl

private
  q128 : Ws → Eqn
  q128 c4 = wlE 1349 (lit c4)
  q129 : Ws → Eqn
  q129 c4 = wlE 1350 (lit c4)
  q130 : Ws → Eqn
  q130 c4 = wpE 672 c4
  q131 : Ws → Eqn
  q131 c4 = wpE 1199 c4
  q132 : Ws → Eqn
  q132 c4 = wlE 1351 (lit c4)
  q133 : Ws → Eqn
  q133 c4 = sE 289 (lem-comm-CSd14-TOFF203 c4)
  q134 : Ws → Eqn
  q134 c4 = sE 336 (lem-comm-CS14-TOFF203 c4)
  q135 : Ws → Eqn
  q135 c4 = wlE 1352 (lit c4)
  q136 : Ws → Eqn
  q136 c4 = wlE 1222 (lit c4)

-- CXcb-box @02132031: 18 steps
lem-CXcb-box-at02132031 : Ws → ⟪ (ℓ "乄似乄") ⟫ʷ ≈ ⟪ (ℓ "似京") ⟫ʷ
lem-CXcb-box-at02132031 c4 = derive (ℓ "乄似乄") (ℓ "似京")
  (rw 1 (q119 c4) ∷
   rw 0 (q128 c4) ∷
   rw⁻ 2 (q129 c4) ∷
   rw⁻ 1 (q130 c4) ∷
   rw 4 (q73 c4) ∷
   rw 8 (q131 c4) ∷
   rw 7 (q132 c4) ∷
   rw 6 (q133 c4) ∷
   rw 5 (q132 c4) ∷
   rw 4 (q134 c4) ∷
   rw⁻ 5 (q73 c4) ∷
   rw⁻ 3 (q89 c4) ∷
   rw 2 (q128 c4) ∷
   rw 3 (q135 c4) ∷
   rw⁻ 4 (q136 c4) ∷
   rw⁻ 3 (q130 c4) ∷
   rw⁻ 0 (q119 c4) ∷
   rw⁻ 1 (q80 c4) ∷ []) Eq.refl

private
  q137 : Ws → Eqn
  q137 c4 = sE 407 (lem-tP-at02132130 c4)
  q138 : Ws → Eqn
  q138 c4 = wpE 780 c4
  q139 : Ws → Eqn
  q139 c4 = wpE 781 c4
  q140 : Ws → Eqn
  q140 c4 = sE 206 (lem-comm-CZ04-TOFF213 c4)
  q141 : Ws → Eqn
  q141 c4 = wpE 782 c4

-- P-box @02132130: 8 steps
lem-P-box-at02132130 : Ws → ⟪ (ℓ "亞佅亞") ⟫ʷ ≈ ⟪ (ℓ "佅") ⟫ʷ
lem-P-box-at02132130 c4 = derive (ℓ "亞佅亞") (ℓ "佅")
  (rw 1 (q69 c4) ∷
   rw⁻ 0 (q137 c4) ∷
   rw⁻ 1 (q138 c4) ∷
   rw⁻ 3 (q137 c4) ∷
   rw⁻ 4 (q139 c4) ∷
   rw 2 (q140 c4) ∷
   rw⁻ 3 (q141 c4) ∷
   rw⁻ 0 (q69 c4) ∷ []) Eq.refl

private
  q142 : Ws → Eqn
  q142 c4 = wlE 176 (lit c4)
  q143 : Ws → Eqn
  q143 c4 = wpE 15 c4
  q144 : Ws → Eqn
  q144 c4 = wpE 18 c4
  q145 : Ws → Eqn
  q145 c4 = sE 296 (lem-comm-TOFF213-CSd04 c4)
  q146 : Ws → Eqn
  q146 c4 = wpE 17 c4
  q147 : Ws → Eqn
  q147 c4 = wpE 16 c4
  q148 : Ws → Eqn
  q148 c4 = wlE 178 (lit c4)
  q149 : Ws → Eqn
  q149 c4 = wlE 177 (lit c4)

-- VPQ @02132130: 14 steps
lem-VPQ-at02132130 : Ws → ⟪ (ℓ "亦交亞亜") ⟫ʷ ≈ ⟪ (ℓ "亞亜亦交") ⟫ʷ
lem-VPQ-at02132130 c4 = derive (ℓ "亦交亞亜") (ℓ "亞亜亦交")
  (rw⁻ 0 (q142 c4) ∷
   rw⁻ 4 (q143 c4) ∷
   rw⁻ 3 (q144 c4) ∷
   rw 2 (q145 c4) ∷
   rw⁻ 1 (q146 c4) ∷
   rw⁻ 0 (q147 c4) ∷
   rw 4 (q111 c4) ∷
   rw 3 (q137 c4) ∷
   rw⁻ 4 (q111 c4) ∷
   rw 1 (q148 c4) ∷
   rw 2 (q8 c4) ∷
   rw 3 (q149 c4) ∷
   rw 0 (q143 c4) ∷
   rw 2 (q142 c4) ∷ []) Eq.refl

private
  q150 : Ws → Eqn
  q150 c4 = sE 392 (lem-VPQ-at0213243041 c4)

-- QVQ @0213243041: 3 steps
lem-QVQ-at0213243041 : Ws → ⟪ (ℓ "二亱亰二") ⟫ʷ ≈ ⟪ (ℓ "亏亱亰亏") ⟫ʷ
lem-QVQ-at0213243041 c4 = derive (ℓ "二亱亰二") (ℓ "亏亱亰亏")
  (rw⁻ 0 (q14 c4) ∷
   rw⁻ 1 (q150 c4) ∷
   rw 4 (q16 c4) ∷ []) Eq.refl

private
  q151 : Ws → Eqn
  q151 c4 = sE 350 (lem-box-tQ-at0310243241 c4)
  q152 : Ws → Eqn
  q152 c4 = sE 361 (lem-tP-at0310243241 c4)
  q153 : Ws → Eqn
  q153 c4 = wlE 504 (lit c4)
  q154 : Ws → Eqn
  q154 c4 = wlE 505 (lit c4)
  q155 : Ws → Eqn
  q155 c4 = sE 226 (lem-comm-CZ12-TOFF304 c4)
  q156 : Ws → Eqn
  q156 c4 = wlE 506 (lit c4)

-- P-box @0310243241: 8 steps
lem-P-box-at0310243241 : Ws → ⟪ (ℓ "产佩产") ⟫ʷ ≈ ⟪ (ℓ "佩") ⟫ʷ
lem-P-box-at0310243241 c4 = derive (ℓ "产佩产") (ℓ "佩")
  (rw 1 (q151 c4) ∷
   rw⁻ 0 (q152 c4) ∷
   rw⁻ 1 (q153 c4) ∷
   rw⁻ 3 (q152 c4) ∷
   rw⁻ 4 (q154 c4) ∷
   rw 2 (q155 c4) ∷
   rw⁻ 3 (q156 c4) ∷
   rw⁻ 0 (q151 c4) ∷ []) Eq.refl

private
  q157 : Ws → Eqn
  q157 c4 = sE 399 (lem-box-tQ-at03122130 c4)
  q158 : Ws → Eqn
  q158 c4 = wlE 537 (lit c4)
  q159 : Ws → Eqn
  q159 c4 = wpE 225 c4
  q160 : Ws → Eqn
  q160 c4 = wlE 1356 (lit c4)
  q161 : Ws → Eqn
  q161 c4 = wlE 271 (lit c4)
  q162 : Ws → Eqn
  q162 c4 = wpE 108 c4
  q163 : Ws → Eqn
  q163 c4 = sE 5 (lem-comm-CX21-CCZ034 c4)
  q164 : Ws → Eqn
  q164 c4 = wpE 123 c4
  q165 : Ws → Eqn
  q165 c4 = wpE 106 c4
  q166 : Ws → Eqn
  q166 c4 = wpE 103 c4
  q167 : Ws → Eqn
  q167 c4 = wpE 226 c4
  q168 : Ws → Eqn
  q168 c4 = wpE 663 c4

-- CXbc-box @03122130: 17 steps
lem-CXbc-box-at03122130 : Ws → ⟪ (ℓ "乄佲乄") ⟫ʷ ≈ ⟪ (ℓ "佲亨") ⟫ʷ
lem-CXbc-box-at03122130 c4 = derive (ℓ "乄佲乄") (ℓ "佲亨")
  (rw 1 (q157 c4) ∷
   rw 0 (q158 c4) ∷
   rw⁻ 1 (q159 c4) ∷
   rw 3 (q160 c4) ∷
   rw 2 (q158 c4) ∷
   rw 5 (q161 c4) ∷
   rw⁻ 9 (q162 c4) ∷
   rw 8 (q163 c4) ∷
   rw⁻ 7 (q164 c4) ∷
   rw 6 (q163 c4) ∷
   rw⁻ 5 (q165 c4) ∷
   rw⁻ 6 (q161 c4) ∷
   rw⁻ 4 (q166 c4) ∷
   rw⁻ 3 (q159 c4) ∷
   rw 4 (q167 c4) ∷
   rw⁻ 0 (q157 c4) ∷
   rw⁻ 1 (q168 c4) ∷ []) Eq.refl

private
  q169 : Ws → Eqn
  q169 c4 = wlE 1357 (lit c4)
  q170 : Ws → Eqn
  q170 c4 = wpE 1202 c4
  q171 : Ws → Eqn
  q171 c4 = wpE 221 c4
  q172 : Ws → Eqn
  q172 c4 = wpE 450 c4
  q173 : Ws → Eqn
  q173 c4 = wlE 879 (lit c4)
  q174 : Ws → Eqn
  q174 c4 = wlE 534 (lit c4)
  q175 : Ws → Eqn
  q175 c4 = sE 221 (lem-comm-CSd04-TOFF312 c4)
  q176 : Ws → Eqn
  q176 c4 = sE 217 (lem-comm-CS04-TOFF312 c4)
  q177 : Ws → Eqn
  q177 c4 = wlE 1358 (lit c4)
  q178 : Ws → Eqn
  q178 c4 = wlE 1359 (lit c4)
  q179 : Ws → Eqn
  q179 c4 = wpE 670 c4

-- CXcb-box @03122130: 18 steps
lem-CXcb-box-at03122130 : Ws → ⟪ (ℓ "丬佲丬") ⟫ʷ ≈ ⟪ (ℓ "佲亜") ⟫ʷ
lem-CXcb-box-at03122130 c4 = derive (ℓ "丬佲丬") (ℓ "佲亜")
  (rw 1 (q157 c4) ∷
   rw 0 (q169 c4) ∷
   rw⁻ 2 (q170 c4) ∷
   rw⁻ 1 (q171 c4) ∷
   rw 4 (q172 c4) ∷
   rw 8 (q173 c4) ∷
   rw 7 (q174 c4) ∷
   rw 6 (q175 c4) ∷
   rw 5 (q174 c4) ∷
   rw 4 (q176 c4) ∷
   rw⁻ 5 (q172 c4) ∷
   rw 3 (q177 c4) ∷
   rw 2 (q169 c4) ∷
   rw 3 (q178 c4) ∷
   rw 4 (q91 c4) ∷
   rw⁻ 3 (q171 c4) ∷
   rw⁻ 0 (q157 c4) ∷
   rw⁻ 1 (q179 c4) ∷ []) Eq.refl

private
  q180 : Ws → Eqn
  q180 c4 = wlE 784 (lit c4)
  q181 : Ws → Eqn
  q181 c4 = wlE 783 (lit c4)
  q182 : Ws → Eqn
  q182 c4 = wlE 786 (lit c4)
  q183 : Ws → Eqn
  q183 c4 = sE 339 (lem-comm-TOFF302-CSd14 c4)
  q184 : Ws → Eqn
  q184 c4 = wlE 785 (lit c4)
  q185 : Ws → Eqn
  q185 c4 = wpE 703 c4
  q186 : Ws → Eqn
  q186 c4 = sE 409 (lem-tP-at03122031 c4)
  q187 : Ws → Eqn
  q187 c4 = eqn (ℓ "丰东") (ℓ "东丰") (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S))
  q188 : Ws → Eqn
  q188 c4 = sE 287 (lem-comm-CSd02-TOFF314 c4)
  q189 : Ws → Eqn
  q189 c4 = eqn (ℓ "丰丝") (ℓ "丝丰") (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S • S • S))

-- VPQ @03122031: 14 steps
lem-VPQ-at03122031 : Ws → ⟪ (ℓ "些亘亮京") ⟫ʷ ≈ ⟪ (ℓ "亮京些亘") ⟫ʷ
lem-VPQ-at03122031 c4 = derive (ℓ "些亘亮京") (ℓ "亮京些亘")
  (rw⁻ 0 (q180 c4) ∷
   rw⁻ 4 (q181 c4) ∷
   rw⁻ 3 (q182 c4) ∷
   rw 2 (q183 c4) ∷
   rw⁻ 1 (q184 c4) ∷
   rw 0 (q185 c4) ∷
   rw 4 (q101 c4) ∷
   rw 3 (q186 c4) ∷
   rw⁻ 4 (q101 c4) ∷
   rw 1 (q187 c4) ∷
   rw 2 (q188 c4) ∷
   rw 3 (q189 c4) ∷
   rw 0 (q181 c4) ∷
   rw 2 (q180 c4) ∷ []) Eq.refl

private
  q190 : Ws → Eqn
  q190 c4 = sE 398 (lem-box-tQ-at03122031 c4)
  q191 : Ws → Eqn
  q191 c4 = wlE 1233 (lit c4)
  q192 : Ws → Eqn
  q192 c4 = wpE 1204 c4
  q193 : Ws → Eqn
  q193 c4 = wpE 1205 c4
  q194 : Ws → Eqn
  q194 c4 = wlE 1220 (lit c4)
  q195 : Ws → Eqn
  q195 c4 = sE 44 (lem-comm-CX20-CCZ134 c4)
  q196 : Ws → Eqn
  q196 c4 = wpE 1206 c4
  q197 : Ws → Eqn
  q197 c4 = wpE 1003 c4
  q198 : Ws → Eqn
  q198 c4 = wpE 1207 c4

-- CXbc-box @03122031: 17 steps
lem-CXbc-box-at03122031 : Ws → ⟪ (ℓ "丬佰丬") ⟫ʷ ≈ ⟪ (ℓ "佰亜") ⟫ʷ
lem-CXbc-box-at03122031 c4 = derive (ℓ "丬佰丬") (ℓ "佰亜")
  (rw 1 (q190 c4) ∷
   rw 0 (q191 c4) ∷
   rw⁻ 1 (q192 c4) ∷
   rw 3 (q193 c4) ∷
   rw 2 (q191 c4) ∷
   rw 5 (q172 c4) ∷
   rw⁻ 9 (q194 c4) ∷
   rw 8 (q195 c4) ∷
   rw⁻ 7 (q196 c4) ∷
   rw 6 (q195 c4) ∷
   rw⁻ 5 (q197 c4) ∷
   rw⁻ 6 (q172 c4) ∷
   rw 4 (q166 c4) ∷
   rw⁻ 3 (q192 c4) ∷
   rw 4 (q198 c4) ∷
   rw⁻ 0 (q190 c4) ∷
   rw⁻ 1 (q179 c4) ∷ []) Eq.refl

private
  q199 : Ws → Eqn
  q199 c4 = wlE 1367 (lit c4)
  q200 : Ws → Eqn
  q200 c4 = wlE 1368 (lit c4)
  q201 : Ws → Eqn
  q201 c4 = wpE 712 c4
  q202 : Ws → Eqn
  q202 c4 = wpE 1006 c4
  q203 : Ws → Eqn
  q203 c4 = wlE 1304 (lit c4)
  q204 : Ws → Eqn
  q204 c4 = sE 290 (lem-comm-CSd14-TOFF302 c4)
  q205 : Ws → Eqn
  q205 c4 = sE 338 (lem-comm-CS14-TOFF302 c4)
  q206 : Ws → Eqn
  q206 c4 = wlE 1369 (lit c4)

-- CXcb-box @03122031: 18 steps
lem-CXcb-box-at03122031 : Ws → ⟪ (ℓ "乄佰乄") ⟫ʷ ≈ ⟪ (ℓ "佰亨") ⟫ʷ
lem-CXcb-box-at03122031 c4 = derive (ℓ "乄佰乄") (ℓ "佰亨")
  (rw 1 (q190 c4) ∷
   rw 0 (q199 c4) ∷
   rw⁻ 2 (q200 c4) ∷
   rw⁻ 1 (q201 c4) ∷
   rw 4 (q161 c4) ∷
   rw 8 (q202 c4) ∷
   rw 7 (q203 c4) ∷
   rw 6 (q204 c4) ∷
   rw 5 (q203 c4) ∷
   rw 4 (q205 c4) ∷
   rw⁻ 5 (q161 c4) ∷
   rw⁻ 3 (q177 c4) ∷
   rw 2 (q199 c4) ∷
   rw 3 (q206 c4) ∷
   rw 4 (q136 c4) ∷
   rw⁻ 3 (q201 c4) ∷
   rw⁻ 0 (q190 c4) ∷
   rw⁻ 1 (q168 c4) ∷ []) Eq.refl

private
  q207 : Ws → Eqn
  q207 c4 = sE 410 (lem-tP-at03122130 c4)
  q208 : Ws → Eqn
  q208 c4 = wpE 344 c4
  q209 : Ws → Eqn
  q209 c4 = wpE 345 c4
  q210 : Ws → Eqn
  q210 c4 = sE 207 (lem-comm-CZ04-TOFF312 c4)
  q211 : Ws → Eqn
  q211 c4 = wpE 346 c4

-- P-box @03122130: 8 steps
lem-P-box-at03122130 : Ws → ⟪ (ℓ "亢佲亢") ⟫ʷ ≈ ⟪ (ℓ "佲") ⟫ʷ
lem-P-box-at03122130 c4 = derive (ℓ "亢佲亢") (ℓ "佲")
  (rw 1 (q157 c4) ∷
   rw⁻ 0 (q207 c4) ∷
   rw⁻ 1 (q208 c4) ∷
   rw⁻ 3 (q207 c4) ∷
   rw⁻ 4 (q209 c4) ∷
   rw 2 (q210 c4) ∷
   rw⁻ 3 (q211 c4) ∷
   rw⁻ 0 (q157 c4) ∷ []) Eq.refl

private
  q212 : Ws → Eqn
  q212 c4 = wlE 488 (lit c4)
  q213 : Ws → Eqn
  q213 c4 = wpE 347 c4
  q214 : Ws → Eqn
  q214 c4 = wpE 348 c4
  q215 : Ws → Eqn
  q215 c4 = sE 214 (lem-comm-TOFF312-CSd04 c4)
  q216 : Ws → Eqn
  q216 c4 = wpE 349 c4
  q217 : Ws → Eqn
  q217 c4 = wpE 350 c4
  q218 : Ws → Eqn
  q218 c4 = eqn (ℓ "么东") (ℓ "东么") (c₃ ((CS • CS • CS) ↑) (S))
  q219 : Ws → Eqn
  q219 c4 = eqn (ℓ "么丝") (ℓ "丝么") (c₃ ((CS • CS • CS) ↑) (S • S • S))

-- VPQ @03122130: 14 steps
lem-VPQ-at03122130 : Ws → ⟪ (ℓ "产交亢亠") ⟫ʷ ≈ ⟪ (ℓ "亢亠产交") ⟫ʷ
lem-VPQ-at03122130 c4 = derive (ℓ "产交亢亠") (ℓ "亢亠产交")
  (rw⁻ 0 (q212 c4) ∷
   rw⁻ 4 (q213 c4) ∷
   rw⁻ 3 (q214 c4) ∷
   rw 2 (q215 c4) ∷
   rw⁻ 1 (q216 c4) ∷
   rw⁻ 0 (q217 c4) ∷
   rw 4 (q101 c4) ∷
   rw 3 (q207 c4) ∷
   rw⁻ 4 (q101 c4) ∷
   rw 1 (q218 c4) ∷
   rw 2 (q35 c4) ∷
   rw 3 (q219 c4) ∷
   rw 0 (q213 c4) ∷
   rw 2 (q212 c4) ∷ []) Eq.refl

private
  q220 : Ws → Eqn
  q220 c4 = sE 213 (lem-comm-TOFF204-CSd13 c4)
  q221 : Ws → Eqn
  q221 c4 = sE 408 (lem-tP-at02142041 c4)

-- VPQ @02142041: 14 steps
lem-VPQ-at02142041 : Ws → ⟪ (ℓ "亞亜亦交") ⟫ʷ ≈ ⟪ (ℓ "亦交亞亜") ⟫ʷ
lem-VPQ-at02142041 c4 = derive (ℓ "亞亜亦交") (ℓ "亦交亞亜")
  (rw⁻ 0 (q143 c4) ∷
   rw⁻ 4 (q142 c4) ∷
   rw⁻ 3 (q149 c4) ∷
   rw 2 (q220 c4) ∷
   rw⁻ 1 (q148 c4) ∷
   rw 0 (q147 c4) ∷
   rw 4 (q111 c4) ∷
   rw 3 (q221 c4) ∷
   rw⁻ 4 (q111 c4) ∷
   rw 1 (q146 c4) ∷
   rw 2 (q87 c4) ∷
   rw 3 (q144 c4) ∷
   rw 0 (q142 c4) ∷
   rw 2 (q143 c4) ∷ []) Eq.refl

private
  q222 : Ws → Eqn
  q222 c4 = wpE 27 c4
  q223 : Ws → Eqn
  q223 c4 = wpE 28 c4

-- t-cP @02142041: 5 steps
lem-t-cP-at02142041 : Ws → ⟪ (ℓ "亞亜亦亜亦") ⟫ʷ ≈ ⟪ (ℓ "亜亦亜亦亞") ⟫ʷ
lem-t-cP-at02142041 c4 = derive (ℓ "亞亜亦亜亦") (ℓ "亜亦亜亦亞")
  (rw⁻ 0 (q222 c4) ∷
   rw 2 (q140 c4) ∷
   rw 1 (q221 c4) ∷
   rw⁻ 2 (q223 c4) ∷
   rw 3 (q221 c4) ∷ []) Eq.refl

private
  q224 : Ws → Eqn
  q224 c4 = sE 228 (lem-comm-TOFF304-CSd12 c4)
  q225 : Ws → Eqn
  q225 c4 = sE 411 (lem-tP-at0314203241 c4)

-- VPQ @0314203241: 14 steps
lem-VPQ-at0314203241 : Ws → ⟪ (ℓ "亢亠产交") ⟫ʷ ≈ ⟪ (ℓ "产交亢亠") ⟫ʷ
lem-VPQ-at0314203241 c4 = derive (ℓ "亢亠产交") (ℓ "产交亢亠")
  (rw⁻ 0 (q213 c4) ∷
   rw⁻ 4 (q212 c4) ∷
   rw⁻ 3 (q219 c4) ∷
   rw 2 (q224 c4) ∷
   rw⁻ 1 (q218 c4) ∷
   rw 0 (q217 c4) ∷
   rw 4 (q101 c4) ∷
   rw 3 (q225 c4) ∷
   rw⁻ 4 (q101 c4) ∷
   rw 1 (q216 c4) ∷
   rw 2 (q175 c4) ∷
   rw 3 (q214 c4) ∷
   rw 0 (q212 c4) ∷
   rw 2 (q213 c4) ∷ []) Eq.refl

private
  q226 : Ws → Eqn
  q226 c4 = wpE 1033 c4
  q227 : Ws → Eqn
  q227 c4 = wpE 1034 c4

-- t-cP @0314203241: 5 steps
lem-t-cP-at0314203241 : Ws → ⟪ (ℓ "亢亠产亠产") ⟫ʷ ≈ ⟪ (ℓ "亠产亠产亢") ⟫ʷ
lem-t-cP-at0314203241 c4 = derive (ℓ "亢亠产亠产") (ℓ "亠产亠产亢")
  (rw⁻ 0 (q226 c4) ∷
   rw 2 (q210 c4) ∷
   rw 1 (q225 c4) ∷
   rw⁻ 2 (q227 c4) ∷
   rw 3 (q225 c4) ∷ []) Eq.refl

private
  q228 : Ws → Eqn
  q228 c4 = sE 340 (lem-box-tQ-at033440 c4)
  q229 : Ws → Eqn
  q229 c4 = sE 374 (lem-comm-CK40-TOFF312 c4)
  q230 : Ws → Eqn
  q230 c4 = wpE 1216 c4
  q231 : Ws → Eqn
  q231 c4 = wpE 1217 c4

-- CK-box @033440: 6 steps
lem-CK-box-at033440 : Ws → ⟪ (ℓ "亁佭亂") ⟫ʷ ≈ ⟪ (ℓ "产亡产亡") ⟫ʷ
lem-CK-box-at033440 c4 = derive (ℓ "亁佭亂") (ℓ "产亡产亡")
  (rw 1 (q228 c4) ∷
   rw 0 (q229 c4) ∷
   rw 1 (q230 c4) ∷
   rw 2 (q229 c4) ∷
   rw 3 (q230 c4) ∷
   rw 4 (q231 c4) ∷ []) Eq.refl

private
  q232 : Ws → Eqn
  q232 c4 = wlE 278 (lit c4)
  q233 : Ws → Eqn
  q233 c4 = sE 384 (lem-CXbc-box-at021021 c4)
  q234 : Ws → Eqn
  q234 c4 = wpE 1229 c4
  q235 : Ws → Eqn
  q235 c4 = sE 388 (lem-CXcb-box-at021021 c4)
  q236 : Ws → Eqn
  q236 c4 = wpE 795 c4
  q237 : Ws → Eqn
  q237 c4 = wpE 1230 c4
  q238 : Ws → Eqn
  q238 c4 = wpE 1231 c4
  q239 : Ws → Eqn
  q239 c4 = wpE 161 c4

-- SWbc-box @021021: 11 steps
lem-SWbc-box-at021021 : Ws → ⟪ (ℓ "乑伭乑") ⟫ʷ ≈ ⟪ (ℓ "伭") ⟫ʷ
lem-SWbc-box-at021021 c4 = derive (ℓ "乑伭乑") (ℓ "伭")
  (rw⁻ 0 (q232 c4) ∷
   rw⁻ 4 (q232 c4) ∷
   rw 2 (q233 c4) ∷
   rw 3 (q234 c4) ∷
   rw 1 (q235 c4) ∷
   rw 4 (q236 c4) ∷
   rw 3 (q237 c4) ∷
   rw 2 (q237 c4) ∷
   rw 3 (q238 c4) ∷
   rw 0 (q233 c4) ∷
   rw 1 (q239 c4) ∷ []) Eq.refl

private
  q240 : Ws → Eqn
  q240 c4 = sE 405 (lem-tP-at02102331 c4)

-- VPQ @02102331: 14 steps
lem-VPQ-at02102331 : Ws → ⟪ (ℓ "亚亘亪亨") ⟫ʷ ≈ ⟪ (ℓ "亪亨亚亘") ⟫ʷ
lem-VPQ-at02102331 c4 = derive (ℓ "亚亘亪亨") (ℓ "亪亨亚亘")
  (rw⁻ 0 (q105 c4) ∷
   rw⁻ 4 (q106 c4) ∷
   rw⁻ 3 (q107 c4) ∷
   rw 2 (q108 c4) ∷
   rw⁻ 1 (q109 c4) ∷
   rw 0 (q110 c4) ∷
   rw 4 (q111 c4) ∷
   rw 3 (q240 c4) ∷
   rw⁻ 4 (q111 c4) ∷
   rw 1 (q113 c4) ∷
   rw 2 (q114 c4) ∷
   rw 3 (q115 c4) ∷
   rw 0 (q106 c4) ∷
   rw 2 (q105 c4) ∷ []) Eq.refl

private
  q241 : Ws → Eqn
  q241 c4 = sE 351 (lem-box-tQ-at031031 c4)
  q242 : Ws → Eqn
  q242 c4 = sE 362 (lem-tP-at031031 c4)
  q243 : Ws → Eqn
  q243 c4 = wlE 1253 (lit c4)
  q244 : Ws → Eqn
  q244 c4 = wlE 1254 (lit c4)
  q245 : Ws → Eqn
  q245 c4 = sE 294 (lem-comm-CZ14-TOFF302 c4)
  q246 : Ws → Eqn
  q246 c4 = wlE 1255 (lit c4)

-- P-box @031031: 8 steps
lem-P-box-at031031 : Ws → ⟪ (ℓ "亮佦亮") ⟫ʷ ≈ ⟪ (ℓ "佦") ⟫ʷ
lem-P-box-at031031 c4 = derive (ℓ "亮佦亮") (ℓ "佦")
  (rw 1 (q241 c4) ∷
   rw⁻ 0 (q242 c4) ∷
   rw⁻ 1 (q243 c4) ∷
   rw⁻ 3 (q242 c4) ∷
   rw⁻ 4 (q244 c4) ∷
   rw 2 (q245 c4) ∷
   rw⁻ 3 (q246 c4) ∷
   rw⁻ 0 (q241 c4) ∷ []) Eq.refl

private
  q247 : Ws → Eqn
  q247 c4 = sE 404 (lem-box-tQ-at142142 c4)
  q248 : Ws → Eqn
  q248 c4 = wpE 963 c4
  q249 : Ws → Eqn
  q249 c4 = wlE 1393 (lit c4)
  q250 : Ws → Eqn
  q250 c4 = wpE 1233 c4
  q251 : Ws → Eqn
  q251 c4 = wlE 334 (lit c4)
  q252 : Ws → Eqn
  q252 c4 = wpE 513 c4
  q253 : Ws → Eqn
  q253 c4 = sE 21 (lem-comm-CX41-CCZ023 c4)
  q254 : Ws → Eqn
  q254 c4 = wlE 620 (lit c4)
  q255 : Ws → Eqn
  q255 c4 = wlE 621 (lit c4)
  q256 : Ws → Eqn
  q256 c4 = wlE 332 (lit c4)
  q257 : Ws → Eqn
  q257 c4 = wlE 1394 (lit c4)
  q258 : Ws → Eqn
  q258 c4 = wlE 272 (lit c4)

-- CXbc-box @142142: 17 steps
lem-CXbc-box-at142142 : Ws → ⟪ (ℓ "乒企乒") ⟫ʷ ≈ ⟪ (ℓ "企亨") ⟫ʷ
lem-CXbc-box-at142142 c4 = derive (ℓ "乒企乒") (ℓ "企亨")
  (rw 1 (q247 c4) ∷
   rw 0 (q248 c4) ∷
   rw⁻ 1 (q249 c4) ∷
   rw 3 (q250 c4) ∷
   rw 2 (q248 c4) ∷
   rw 5 (q251 c4) ∷
   rw⁻ 9 (q252 c4) ∷
   rw 8 (q253 c4) ∷
   rw⁻ 7 (q254 c4) ∷
   rw 6 (q253 c4) ∷
   rw⁻ 5 (q255 c4) ∷
   rw⁻ 6 (q251 c4) ∷
   rw 4 (q256 c4) ∷
   rw⁻ 3 (q249 c4) ∷
   rw 4 (q257 c4) ∷
   rw⁻ 0 (q247 c4) ∷
   rw⁻ 1 (q258 c4) ∷ []) Eq.refl

private
  q259 : Ws → Eqn
  q259 c4 = wpE 1234 c4
  q260 : Ws → Eqn
  q260 c4 = wpE 1235 c4
  q261 : Ws → Eqn
  q261 c4 = wlE 1343 (lit c4)
  q262 : Ws → Eqn
  q262 c4 = wlE 330 (lit c4)
  q263 : Ws → Eqn
  q263 c4 = wpE 817 c4
  q264 : Ws → Eqn
  q264 c4 = wpE 960 c4
  q265 : Ws → Eqn
  q265 c4 = sE 203 (lem-comm-CSd23-TOFF014 c4)
  q266 : Ws → Eqn
  q266 c4 = sE 286 (lem-comm-CS23-TOFF014 c4)
  q267 : Ws → Eqn
  q267 c4 = wpE 203 c4
  q268 : Ws → Eqn
  q268 c4 = wpE 1236 c4
  q269 : Ws → Eqn
  q269 c4 = wpE 550 c4
  q270 : Ws → Eqn
  q270 c4 = wlE 277 (lit c4)

-- CXcb-box @142142: 18 steps
lem-CXcb-box-at142142 : Ws → ⟪ (ℓ "乳企乳") ⟫ʷ ≈ ⟪ (ℓ "企亰") ⟫ʷ
lem-CXcb-box-at142142 c4 = derive (ℓ "乳企乳") (ℓ "企亰")
  (rw 1 (q247 c4) ∷
   rw 0 (q259 c4) ∷
   rw⁻ 2 (q260 c4) ∷
   rw⁻ 1 (q261 c4) ∷
   rw 4 (q262 c4) ∷
   rw 8 (q263 c4) ∷
   rw 7 (q264 c4) ∷
   rw 6 (q265 c4) ∷
   rw 5 (q264 c4) ∷
   rw 4 (q266 c4) ∷
   rw⁻ 5 (q262 c4) ∷
   rw⁻ 3 (q267 c4) ∷
   rw 2 (q259 c4) ∷
   rw 3 (q268 c4) ∷
   rw⁻ 4 (q269 c4) ∷
   rw⁻ 3 (q261 c4) ∷
   rw⁻ 0 (q247 c4) ∷
   rw⁻ 1 (q270 c4) ∷ []) Eq.refl

private
  q271 : Ws → Eqn
  q271 c4 = sE 401 (lem-box-tQ-at03243042 c4)
  q272 : Ws → Eqn
  q272 c4 = sE 413 (lem-tP-at03243042 c4)
  q273 : Ws → Eqn
  q273 c4 = wlE 1235 (lit c4)
  q274 : Ws → Eqn
  q274 c4 = wlE 1236 (lit c4)
  q275 : Ws → Eqn
  q275 c4 = sE 337 (lem-comm-CZ02-TOFF314 c4)
  q276 : Ws → Eqn
  q276 c4 = wlE 774 (lit c4)

-- P-box @03243042: 8 steps
lem-P-box-at03243042 : Ws → ⟪ (ℓ "些佮些") ⟫ʷ ≈ ⟪ (ℓ "佮") ⟫ʷ
lem-P-box-at03243042 c4 = derive (ℓ "些佮些") (ℓ "佮")
  (rw 1 (q271 c4) ∷
   rw⁻ 0 (q272 c4) ∷
   rw⁻ 1 (q273 c4) ∷
   rw⁻ 3 (q272 c4) ∷
   rw⁻ 4 (q274 c4) ∷
   rw 2 (q275 c4) ∷
   rw⁻ 3 (q276 c4) ∷
   rw⁻ 0 (q271 c4) ∷ []) Eq.refl

private
  q277 : Ws → Eqn
  q277 c4 = sE 298 (lem-comm-TOFF314-CSd02 c4)

-- VPQ @03243042: 14 steps
lem-VPQ-at03243042 : Ws → ⟪ (ℓ "亮京些亘") ⟫ʷ ≈ ⟪ (ℓ "些亘亮京") ⟫ʷ
lem-VPQ-at03243042 c4 = derive (ℓ "亮京些亘") (ℓ "些亘亮京")
  (rw⁻ 0 (q181 c4) ∷
   rw⁻ 4 (q180 c4) ∷
   rw⁻ 3 (q189 c4) ∷
   rw 2 (q277 c4) ∷
   rw⁻ 1 (q187 c4) ∷
   rw⁻ 0 (q185 c4) ∷
   rw 4 (q101 c4) ∷
   rw 3 (q272 c4) ∷
   rw⁻ 4 (q101 c4) ∷
   rw 1 (q184 c4) ∷
   rw 2 (q204 c4) ∷
   rw 3 (q182 c4) ∷
   rw 0 (q180 c4) ∷
   rw 2 (q181 c4) ∷ []) Eq.refl

private
  q278 : Ws → Eqn
  q278 c4 = sE 343 (lem-box-tQ-at2442 c4)
  q279 : Ws → Eqn
  q279 c4 = sE 372 (lem-tP-at2442 c4)
  q280 : Ws → Eqn
  q280 c4 = wlE 825 (lit c4)
  q281 : Ws → Eqn
  q281 c4 = wlE 826 (lit c4)
  q282 : Ws → Eqn
  q282 c4 = sE 295 (lem-comm-CZ23-TOFF014 c4)
  q283 : Ws → Eqn
  q283 c4 = wlE 827 (lit c4)

-- P-box @2442: 8 steps
lem-P-box-at2442 : Ws → ⟪ (ℓ "亙仆亙") ⟫ʷ ≈ ⟪ (ℓ "仆") ⟫ʷ
lem-P-box-at2442 c4 = derive (ℓ "亙仆亙") (ℓ "仆")
  (rw 1 (q278 c4) ∷
   rw⁻ 0 (q279 c4) ∷
   rw⁻ 1 (q280 c4) ∷
   rw⁻ 3 (q279 c4) ∷
   rw⁻ 4 (q281 c4) ∷
   rw 2 (q282 c4) ∷
   rw⁻ 3 (q283 c4) ∷
   rw⁻ 0 (q278 c4) ∷ []) Eq.refl

private
  q284 : Ws → Eqn
  q284 c4 = sE 395 (lem-box-tQ-at02102331 c4)
  q285 : Ws → Eqn
  q285 c4 = wlE 1398 (lit c4)
  q286 : Ws → Eqn
  q286 c4 = wpE 1249 c4
  q287 : Ws → Eqn
  q287 c4 = wpE 231 c4
  q288 : Ws → Eqn
  q288 c4 = sE 18 (lem-comm-CX03-CCZ124 c4)
  q289 : Ws → Eqn
  q289 c4 = wlE 1399 (lit c4)
  q290 : Ws → Eqn
  q290 c4 = wlE 527 (lit c4)
  q291 : Ws → Eqn
  q291 c4 = wlE 1400 (lit c4)
  q292 : Ws → Eqn
  q292 c4 = wpE 1228 c4

-- CXbc-box @02102331: 17 steps
lem-CXbc-box-at02102331 : Ws → ⟪ (ℓ "乳伯乳") ⟫ʷ ≈ ⟪ (ℓ "伯亠") ⟫ʷ
lem-CXbc-box-at02102331 c4 = derive (ℓ "乳伯乳") (ℓ "伯亠")
  (rw 1 (q284 c4) ∷
   rw 0 (q132 c4) ∷
   rw⁻ 1 (q285 c4) ∷
   rw 3 (q286 c4) ∷
   rw 2 (q132 c4) ∷
   rw 5 (q287 c4) ∷
   rw⁻ 9 (q126 c4) ∷
   rw 8 (q288 c4) ∷
   rw⁻ 7 (q289 c4) ∷
   rw 6 (q288 c4) ∷
   rw⁻ 5 (q123 c4) ∷
   rw⁻ 6 (q287 c4) ∷
   rw⁻ 4 (q290 c4) ∷
   rw⁻ 3 (q285 c4) ∷
   rw 4 (q291 c4) ∷
   rw⁻ 0 (q284 c4) ∷
   rw⁻ 1 (q292 c4) ∷ []) Eq.refl

private
  q293 : Ws → Eqn
  q293 c4 = wlE 1401 (lit c4)
  q294 : Ws → Eqn
  q294 c4 = wpE 1250 c4
  q295 : Ws → Eqn
  q295 c4 = wlE 280 (lit c4)
  q296 : Ws → Eqn
  q296 c4 = wpE 301 c4
  q297 : Ws → Eqn
  q297 c4 = wpE 1251 c4
  q298 : Ws → Eqn
  q298 c4 = wlE 1391 (lit c4)
  q299 : Ws → Eqn
  q299 c4 = wlE 1402 (lit c4)
  q300 : Ws → Eqn
  q300 c4 = wpE 66 c4
  q301 : Ws → Eqn
  q301 c4 = wpE 1226 c4

-- CXcb-box @02102331: 18 steps
lem-CXcb-box-at02102331 : Ws → ⟪ (ℓ "乒伯乒") ⟫ʷ ≈ ⟪ (ℓ "伯五") ⟫ʷ
lem-CXcb-box-at02102331 c4 = derive (ℓ "乒伯乒") (ℓ "伯五")
  (rw 1 (q284 c4) ∷
   rw 0 (q293 c4) ∷
   rw⁻ 2 (q294 c4) ∷
   rw⁻ 1 (q295 c4) ∷
   rw 4 (q296 c4) ∷
   rw 8 (q297 c4) ∷
   rw 7 (q120 c4) ∷
   rw 6 (q133 c4) ∷
   rw 5 (q120 c4) ∷
   rw 4 (q134 c4) ∷
   rw⁻ 5 (q296 c4) ∷
   rw 3 (q298 c4) ∷
   rw 2 (q293 c4) ∷
   rw 3 (q299 c4) ∷
   rw 4 (q300 c4) ∷
   rw⁻ 3 (q295 c4) ∷
   rw⁻ 0 (q284 c4) ∷
   rw⁻ 1 (q301 c4) ∷ []) Eq.refl

private
  q302 : Ws → Eqn
  q302 c4 = wpE 50 c4
  q303 : Ws → Eqn
  q303 c4 = wlE 201 (lit c4)
  q304 : Ws → Eqn
  q304 c4 = eqn (ℓ "下乣") (ℓ "乣下") (c₁ (S • S • S) ((CS • CS • CS) ↑))
  q305 : Ws → Eqn
  q305 c4 = sE 211 (lem-comm-TOFF014-CSd23 c4)
  q306 : Ws → Eqn
  q306 c4 = eqn (ℓ "上乣") (ℓ "乣上") (c₁ (S) ((CS • CS • CS) ↑))
  q307 : Ws → Eqn
  q307 c4 = wlE 202 (lit c4)
  q308 : Ws → Eqn
  q308 c4 = wlE 159 (lit c4)
  q309 : Ws → Eqn
  q309 c4 = sE 418 (lem-tP-at142142 c4)
  q310 : Ws → Eqn
  q310 c4 = eqn (ℓ "上乖") (ℓ "乖上") (c₁ (S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))
  q311 : Ws → Eqn
  q311 c4 = sE 202 (lem-comm-CSd14-TOFF023 c4)
  q312 : Ws → Eqn
  q312 c4 = eqn (ℓ "下乖") (ℓ "乖下") (c₁ (S • S • S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))

-- VPQ @142142: 14 steps
lem-VPQ-at142142 : Ws → ⟪ (ℓ "井五亙亘") ⟫ʷ ≈ ⟪ (ℓ "亙亘井五") ⟫ʷ
lem-VPQ-at142142 c4 = derive (ℓ "井五亙亘") (ℓ "亙亘井五")
  (rw⁻ 0 (q302 c4) ∷
   rw⁻ 4 (q303 c4) ∷
   rw 3 (q304 c4) ∷
   rw 2 (q305 c4) ∷
   rw 1 (q306 c4) ∷
   rw 0 (q307 c4) ∷
   rw 4 (q308 c4) ∷
   rw 3 (q309 c4) ∷
   rw⁻ 4 (q308 c4) ∷
   rw⁻ 1 (q310 c4) ∷
   rw 2 (q311 c4) ∷
   rw⁻ 3 (q312 c4) ∷
   rw 0 (q303 c4) ∷
   rw 2 (q302 c4) ∷ []) Eq.refl

private
  q313 : Ws → Eqn
  q313 c4 = wpE 58 c4
  q314 : Ws → Eqn
  q314 c4 = sE 208 (lem-comm-CZ14-TOFF023 c4)
  q315 : Ws → Eqn
  q315 c4 = wpE 59 c4

-- t-cP @142142: 5 steps
lem-t-cP-at142142 : Ws → ⟪ (ℓ "井五亙五亙") ⟫ʷ ≈ ⟪ (ℓ "五亙五亙井") ⟫ʷ
lem-t-cP-at142142 c4 = derive (ℓ "井五亙五亙") (ℓ "五亙五亙井")
  (rw⁻ 0 (q313 c4) ∷
   rw 2 (q314 c4) ∷
   rw 1 (q309 c4) ∷
   rw⁻ 2 (q315 c4) ∷
   rw 3 (q309 c4) ∷ []) Eq.refl

private
  q316 : Ws → Eqn
  q316 c4 = wlE 1403 (lit c4)
  q317 : Ws → Eqn
  q317 c4 = sE 369 (lem-tP-at033440 c4)
  q318 : Ws → Eqn
  q318 c4 = wlE 882 (lit c4)

-- t-cP @033440: 5 steps
lem-t-cP-at033440 : Ws → ⟪ (ℓ "产交亢交亢") ⟫ʷ ≈ ⟪ (ℓ "交亢交亢产") ⟫ʷ
lem-t-cP-at033440 c4 = derive (ℓ "产交亢交亢") (ℓ "交亢交亢产")
  (rw⁻ 0 (q316 c4) ∷
   rw 2 (q155 c4) ∷
   rw 1 (q317 c4) ∷
   rw⁻ 2 (q318 c4) ∷
   rw 3 (q317 c4) ∷ []) Eq.refl

private
  q319 : Ws → Eqn
  q319 c4 = sE 332 (lem-tP-at0214203143 c4)

-- t-cP @0214203143: 5 steps
lem-t-cP-at0214203143 : Ws → ⟪ (ℓ "亞亜亦亜亦") ⟫ʷ ≈ ⟪ (ℓ "亜亦亜亦亞") ⟫ʷ
lem-t-cP-at0214203143 c4 = derive (ℓ "亞亜亦亜亦") (ℓ "亜亦亜亦亞")
  (rw⁻ 0 (q222 c4) ∷
   rw 2 (q140 c4) ∷
   rw 1 (q319 c4) ∷
   rw⁻ 2 (q223 c4) ∷
   rw 3 (q319 c4) ∷ []) Eq.refl

private
  q320 : Ws → Eqn
  q320 c4 = sE 403 (lem-box-tQ-at04122041 c4)
  q321 : Ws → Eqn
  q321 c4 = wpE 1311 c4
  q322 : Ws → Eqn
  q322 c4 = wpE 1312 c4
  q323 : Ws → Eqn
  q323 c4 = wpE 1313 c4
  q324 : Ws → Eqn
  q324 c4 = wlE 1273 (lit c4)
  q325 : Ws → Eqn
  q325 c4 = wlE 393 (lit c4)
  q326 : Ws → Eqn
  q326 c4 = wpE 1027 c4
  q327 : Ws → Eqn
  q327 c4 = wpE 261 c4
  q328 : Ws → Eqn
  q328 c4 = wpE 272 c4
  q329 : Ws → Eqn
  q329 c4 = wpE 1314 c4
  q330 : Ws → Eqn
  q330 c4 = wlE 1465 (lit c4)

-- CXbc-box @04122041: 17 steps
lem-CXbc-box-at04122041 : Ws → ⟪ (ℓ "为侗为") ⟫ʷ ≈ ⟪ (ℓ "侗二") ⟫ʷ
lem-CXbc-box-at04122041 c4 = derive (ℓ "为侗为") (ℓ "侗二")
  (rw 1 (q320 c4) ∷
   rw 0 (q321 c4) ∷
   rw⁻ 1 (q322 c4) ∷
   rw 3 (q323 c4) ∷
   rw 2 (q321 c4) ∷
   rw 5 (q324 c4) ∷
   rw⁻ 9 (q325 c4) ∷
   rw 8 (q195 c4) ∷
   rw⁻ 7 (q326 c4) ∷
   rw 6 (q195 c4) ∷
   rw⁻ 5 (q327 c4) ∷
   rw⁻ 6 (q324 c4) ∷
   rw 4 (q328 c4) ∷
   rw⁻ 3 (q322 c4) ∷
   rw 4 (q329 c4) ∷
   rw⁻ 0 (q320 c4) ∷
   rw⁻ 1 (q330 c4) ∷ []) Eq.refl

private
  q331 : Ws → Eqn
  q331 c4 = wpE 1315 c4
  q332 : Ws → Eqn
  q332 c4 = wlE 1466 (lit c4)
  q333 : Ws → Eqn
  q333 c4 = wlE 233 (lit c4)
  q334 : Ws → Eqn
  q334 c4 = wpE 1316 c4
  q335 : Ws → Eqn
  q335 c4 = wpE 1317 c4
  q336 : Ws → Eqn
  q336 c4 = sE 377 (lem-comm-CSd13-TOFF402 c4)
  q337 : Ws → Eqn
  q337 c4 = sE 375 (lem-comm-CS13-TOFF402 c4)
  q338 : Ws → Eqn
  q338 c4 = wpE 1318 c4
  q339 : Ws → Eqn
  q339 c4 = wpE 1319 c4
  q340 : Ws → Eqn
  q340 c4 = wlE 1467 (lit c4)

-- CXcb-box @04122041: 18 steps
lem-CXcb-box-at04122041 : Ws → ⟪ (ℓ "买侗买") ⟫ʷ ≈ ⟪ (ℓ "侗交") ⟫ʷ
lem-CXcb-box-at04122041 c4 = derive (ℓ "买侗买") (ℓ "侗交")
  (rw 1 (q320 c4) ∷
   rw 0 (q331 c4) ∷
   rw⁻ 2 (q332 c4) ∷
   rw⁻ 1 (q53 c4) ∷
   rw 4 (q333 c4) ∷
   rw 8 (q334 c4) ∷
   rw 7 (q335 c4) ∷
   rw 6 (q336 c4) ∷
   rw 5 (q335 c4) ∷
   rw 4 (q337 c4) ∷
   rw⁻ 5 (q333 c4) ∷
   rw⁻ 3 (q338 c4) ∷
   rw 2 (q331 c4) ∷
   rw 3 (q339 c4) ∷
   rw 4 (q12 c4) ∷
   rw⁻ 3 (q53 c4) ∷
   rw⁻ 0 (q320 c4) ∷
   rw⁻ 1 (q340 c4) ∷ []) Eq.refl

private
  q341 : Ws → Eqn
  q341 c4 = wlE 455 (lit c4)
  q342 : Ws → Eqn
  q342 c4 = wpE 304 c4
  q343 : Ws → Eqn
  q343 c4 = eqn (ℓ "丩丣") (ℓ "丣丩") (c₂ (CS • CS • CS) ((S • S • S) ↑ ↑))
  q344 : Ws → Eqn
  q344 c4 = eqn (ℓ "丩亳") (ℓ "亳丩") (c₂ (CS • CS • CS) (Toffᵗ))
  q345 : Ws → Eqn
  q345 c4 = eqn (ℓ "丩丢") (ℓ "丢丩") (c₂ (CS • CS • CS) (S ↑ ↑))
  q346 : Ws → Eqn
  q346 c4 = eqn (ℓ "丩乣") (ℓ "乣丩") (c₂ (CS • CS • CS) (CS • CS • CS))
  q347 : Ws → Eqn
  q347 c4 = wlE 456 (lit c4)
  q348 : Ws → Eqn
  q348 c4 = sE 416 (lem-tP-at0412233041 c4)
  q349 : Ws → Eqn
  q349 c4 = eqn (ℓ "乣丢") (ℓ "丢乣") (c₄ ((CS • CS • CS) ↑ ↑) (S))
  q350 : Ws → Eqn
  q350 c4 = sE 76 (lem-comm-CSd23-TOFF401 c4)
  q351 : Ws → Eqn
  q351 c4 = eqn (ℓ "乣丣") (ℓ "丣乣") (c₄ ((CS • CS • CS) ↑ ↑) (S • S • S))

-- VPQ @0412233041: 14 steps
lem-VPQ-at0412233041 : Ws → ⟪ (ℓ "亳亰亗五") ⟫ʷ ≈ ⟪ (ℓ "亗五亳亰") ⟫ʷ
lem-VPQ-at0412233041 c4 = derive (ℓ "亳亰亗五") (ℓ "亗五亳亰")
  (rw⁻ 0 (q341 c4) ∷
   rw⁻ 4 (q342 c4) ∷
   rw⁻ 3 (q343 c4) ∷
   rw⁻ 2 (q344 c4) ∷
   rw⁻ 1 (q345 c4) ∷
   rw⁻ 0 (q346 c4) ∷
   rw 4 (q347 c4) ∷
   rw 3 (q348 c4) ∷
   rw⁻ 4 (q347 c4) ∷
   rw 1 (q349 c4) ∷
   rw 2 (q350 c4) ∷
   rw 3 (q351 c4) ∷
   rw 0 (q342 c4) ∷
   rw 2 (q341 c4) ∷ []) Eq.refl

private
  q352 : Ws → Eqn
  q352 c4 = wpE 1322 c4
  q353 : Ws → Eqn
  q353 c4 = wlE 1473 (lit c4)
  q354 : Ws → Eqn
  q354 c4 = eqn (ℓ "乏丣") (ℓ "丣乏") (c₄ (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) (S • S • S))
  q355 : Ws → Eqn
  q355 c4 = sE 379 (lem-comm-TOFF402-CSd13 c4)
  q356 : Ws → Eqn
  q356 c4 = eqn (ℓ "乏丢") (ℓ "丢乏") (c₄ (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) (S))
  q357 : Ws → Eqn
  q357 c4 = wlE 901 (lit c4)
  q358 : Ws → Eqn
  q358 c4 = sE 415 (lem-tP-at04122041 c4)
  q359 : Ws → Eqn
  q359 c4 = eqn (ℓ "丰丢") (ℓ "丢丰") (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S ↑))
  q360 : Ws → Eqn
  q360 c4 = sE 376 (lem-comm-CSd02-TOFF413 c4)
  q361 : Ws → Eqn
  q361 c4 = eqn (ℓ "丰丣") (ℓ "丣丰") (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) ((S • S • S) ↑))

-- VPQ @04122041: 14 steps
lem-VPQ-at04122041 : Ws → ⟪ (ℓ "亟亜亯京") ⟫ʷ ≈ ⟪ (ℓ "亯京亟亜") ⟫ʷ
lem-VPQ-at04122041 c4 = derive (ℓ "亟亜亯京") (ℓ "亯京亟亜")
  (rw⁻ 0 (q352 c4) ∷
   rw⁻ 4 (q353 c4) ∷
   rw⁻ 3 (q354 c4) ∷
   rw 2 (q355 c4) ∷
   rw⁻ 1 (q356 c4) ∷
   rw 0 (q357 c4) ∷
   rw 4 (q347 c4) ∷
   rw 3 (q358 c4) ∷
   rw⁻ 4 (q347 c4) ∷
   rw 1 (q359 c4) ∷
   rw 2 (q360 c4) ∷
   rw 3 (q361 c4) ∷
   rw 0 (q353 c4) ∷
   rw 2 (q352 c4) ∷ []) Eq.refl

private
  q362 : Ws → Eqn
  q362 c4 = wlE 677 (lit c4)
  q363 : Ws → Eqn
  q363 c4 = sE 387 (lem-CXbc-box-at0410213243 c4)
  q364 : Ws → Eqn
  q364 c4 = wlE 1479 (lit c4)
  q365 : Ws → Eqn
  q365 c4 = sE 391 (lem-CXcb-box-at0410213243 c4)
  q366 : Ws → Eqn
  q366 c4 = wlE 448 (lit c4)
  q367 : Ws → Eqn
  q367 c4 = wlE 1480 (lit c4)
  q368 : Ws → Eqn
  q368 c4 = wlE 1481 (lit c4)

-- SWbc-box @0410213243: 11 steps
lem-SWbc-box-at0410213243 : Ws → ⟪ (ℓ "乊侍乊") ⟫ʷ ≈ ⟪ (ℓ "侍") ⟫ʷ
lem-SWbc-box-at0410213243 c4 = derive (ℓ "乊侍乊") (ℓ "侍")
  (rw⁻ 0 (q362 c4) ∷
   rw⁻ 4 (q362 c4) ∷
   rw 2 (q363 c4) ∷
   rw 3 (q364 c4) ∷
   rw 1 (q365 c4) ∷
   rw 4 (q366 c4) ∷
   rw 3 (q367 c4) ∷
   rw 2 (q367 c4) ∷
   rw 3 (q368 c4) ∷
   rw 0 (q363 c4) ∷
   rw 1 (q48 c4) ∷ []) Eq.refl

private
  q369 : Ws → Eqn
  q369 c4 = sE 402 (lem-box-tQ-at04103143 c4)
  q370 : Ws → Eqn
  q370 c4 = sE 414 (lem-tP-at04103143 c4)
  q371 : Ws → Eqn
  q371 c4 = wlE 1482 (lit c4)
  q372 : Ws → Eqn
  q372 c4 = wlE 1483 (lit c4)
  q373 : Ws → Eqn
  q373 c4 = sE 378 (lem-comm-CZ13-TOFF402 c4)
  q374 : Ws → Eqn
  q374 c4 = wlE 1484 (lit c4)

-- P-box @04103143: 8 steps
lem-P-box-at04103143 : Ws → ⟪ (ℓ "亯侎亯") ⟫ʷ ≈ ⟪ (ℓ "侎") ⟫ʷ
lem-P-box-at04103143 c4 = derive (ℓ "亯侎亯") (ℓ "侎")
  (rw 1 (q369 c4) ∷
   rw⁻ 0 (q370 c4) ∷
   rw⁻ 1 (q371 c4) ∷
   rw⁻ 3 (q370 c4) ∷
   rw⁻ 4 (q372 c4) ∷
   rw 2 (q373 c4) ∷
   rw⁻ 3 (q374 c4) ∷
   rw⁻ 0 (q369 c4) ∷ []) Eq.refl

-- VPQ @04103143: 14 steps
lem-VPQ-at04103143 : Ws → ⟪ (ℓ "亟亜亯京") ⟫ʷ ≈ ⟪ (ℓ "亯京亟亜") ⟫ʷ
lem-VPQ-at04103143 c4 = derive (ℓ "亟亜亯京") (ℓ "亯京亟亜")
  (rw⁻ 0 (q352 c4) ∷
   rw⁻ 4 (q353 c4) ∷
   rw⁻ 3 (q354 c4) ∷
   rw 2 (q355 c4) ∷
   rw⁻ 1 (q356 c4) ∷
   rw 0 (q357 c4) ∷
   rw 4 (q347 c4) ∷
   rw 3 (q370 c4) ∷
   rw⁻ 4 (q347 c4) ∷
   rw 1 (q359 c4) ∷
   rw 2 (q360 c4) ∷
   rw 3 (q361 c4) ∷
   rw 0 (q353 c4) ∷
   rw 2 (q352 c4) ∷ []) Eq.refl

private
  q375 : Ws → Eqn
  q375 c4 = sE 380 (lem-comm-TOFF413-CSd02 c4)
  q376 : Ws → Eqn
  q376 c4 = sE 417 (lem-tP-at04233042 c4)

-- VPQ @04233042: 14 steps
lem-VPQ-at04233042 : Ws → ⟪ (ℓ "亯京亟亜") ⟫ʷ ≈ ⟪ (ℓ "亟亜亯京") ⟫ʷ
lem-VPQ-at04233042 c4 = derive (ℓ "亯京亟亜") (ℓ "亟亜亯京")
  (rw⁻ 0 (q353 c4) ∷
   rw⁻ 4 (q352 c4) ∷
   rw⁻ 3 (q361 c4) ∷
   rw 2 (q375 c4) ∷
   rw⁻ 1 (q359 c4) ∷
   rw⁻ 0 (q357 c4) ∷
   rw 4 (q347 c4) ∷
   rw 3 (q376 c4) ∷
   rw⁻ 4 (q347 c4) ∷
   rw 1 (q356 c4) ∷
   rw 2 (q336 c4) ∷
   rw 3 (q354 c4) ∷
   rw 0 (q352 c4) ∷
   rw 2 (q353 c4) ∷ []) Eq.refl

private
  q377 : Ws → Eqn
  q377 c4 = sE 421 (lem-box-tQ-at0412233041 c4)
  q378 : Ws → Eqn
  q378 c4 = wpE 1333 c4
  q379 : Ws → Eqn
  q379 c4 = wpE 1010 c4
  q380 : Ws → Eqn
  q380 c4 = wlE 1496 (lit c4)
  q381 : Ws → Eqn
  q381 c4 = wpE 67 c4
  q382 : Ws → Eqn
  q382 c4 = sE 6 (lem-comm-CX23-CCZ014 c4)
  q383 : Ws → Eqn
  q383 c4 = wpE 60 c4
  q384 : Ws → Eqn
  q384 c4 = wpE 53 c4
  q385 : Ws → Eqn
  q385 c4 = wpE 1011 c4

-- CXbc-box @0412233041: 17 steps
lem-CXbc-box-at0412233041 : Ws → ⟪ (ℓ "买侚买") ⟫ʷ ≈ ⟪ (ℓ "侚交") ⟫ʷ
lem-CXbc-box-at0412233041 c4 = derive (ℓ "买侚买") (ℓ "侚交")
  (rw 1 (q377 c4) ∷
   rw 0 (q378 c4) ∷
   rw⁻ 1 (q379 c4) ∷
   rw 3 (q380 c4) ∷
   rw 2 (q378 c4) ∷
   rw 5 (q333 c4) ∷
   rw⁻ 9 (q381 c4) ∷
   rw 8 (q382 c4) ∷
   rw⁻ 7 (q383 c4) ∷
   rw 6 (q382 c4) ∷
   rw⁻ 5 (q384 c4) ∷
   rw⁻ 6 (q333 c4) ∷
   rw⁻ 4 (q328 c4) ∷
   rw⁻ 3 (q379 c4) ∷
   rw 4 (q385 c4) ∷
   rw⁻ 0 (q377 c4) ∷
   rw⁻ 1 (q340 c4) ∷ []) Eq.refl

private
  q386 : Ws → Eqn
  q386 c4 = wpE 1334 c4
  q387 : Ws → Eqn
  q387 c4 = wpE 1335 c4
  q388 : Ws → Eqn
  q388 c4 = wpE 778 c4
  q389 : Ws → Eqn
  q389 c4 = wlE 461 (lit c4)
  q390 : Ws → Eqn
  q390 c4 = wpE 1336 c4
  q391 : Ws → Eqn
  q391 c4 = eqn (ℓ "丨亳") (ℓ "亳丨") (c₂ (CS) (Toffᵗ))
  q392 : Ws → Eqn
  q392 c4 = wpE 1337 c4
  q393 : Ws → Eqn
  q393 c4 = wpE 167 c4

-- CXcb-box @0412233041: 18 steps
lem-CXcb-box-at0412233041 : Ws → ⟪ (ℓ "为侚为") ⟫ʷ ≈ ⟪ (ℓ "侚二") ⟫ʷ
lem-CXcb-box-at0412233041 c4 = derive (ℓ "为侚为") (ℓ "侚二")
  (rw 1 (q377 c4) ∷
   rw 0 (q386 c4) ∷
   rw⁻ 2 (q387 c4) ∷
   rw⁻ 1 (q388 c4) ∷
   rw 4 (q324 c4) ∷
   rw 8 (q389 c4) ∷
   rw 7 (q390 c4) ∷
   rw 6 (q344 c4) ∷
   rw 5 (q390 c4) ∷
   rw 4 (q391 c4) ∷
   rw⁻ 5 (q324 c4) ∷
   rw 3 (q338 c4) ∷
   rw 2 (q386 c4) ∷
   rw 3 (q392 c4) ∷
   rw 4 (q393 c4) ∷
   rw⁻ 3 (q388 c4) ∷
   rw⁻ 0 (q377 c4) ∷
   rw⁻ 1 (q330 c4) ∷ []) Eq.refl

private
  q394 : Ws → Eqn
  q394 c4 = wpE 1338 c4
  q395 : Ws → Eqn
  q395 c4 = wpE 1339 c4
  q396 : Ws → Eqn
  q396 c4 = eqn (ℓ "个亳") (ℓ "亳个") (c₂ (CZ) (Toffᵗ))
  q397 : Ws → Eqn
  q397 c4 = wpE 1340 c4

-- P-box @0412233041: 8 steps
lem-P-box-at0412233041 : Ws → ⟪ (ℓ "亗侚亗") ⟫ʷ ≈ ⟪ (ℓ "侚") ⟫ʷ
lem-P-box-at0412233041 c4 = derive (ℓ "亗侚亗") (ℓ "侚")
  (rw 1 (q377 c4) ∷
   rw⁻ 0 (q348 c4) ∷
   rw⁻ 1 (q394 c4) ∷
   rw⁻ 3 (q348 c4) ∷
   rw⁻ 4 (q395 c4) ∷
   rw 2 (q396 c4) ∷
   rw⁻ 3 (q397 c4) ∷
   rw⁻ 0 (q377 c4) ∷ []) Eq.refl

private
  q398 : Ws → Eqn
  q398 c4 = sE 420 (lem-box-tQ-at041041 c4)
  q399 : Ws → Eqn
  q399 c4 = wlE 1562 (lit c4)
  q400 : Ws → Eqn
  q400 c4 = wpE 1385 c4
  q401 : Ws → Eqn
  q401 c4 = wlE 391 (lit c4)
  q402 : Ws → Eqn
  q402 c4 = sE 0 (lem-comm-CX02-CCZ134 c4)
  q403 : Ws → Eqn
  q403 c4 = wlE 392 (lit c4)
  q404 : Ws → Eqn
  q404 c4 = wlE 1563 (lit c4)
  q405 : Ws → Eqn
  q405 c4 = wlE 1564 (lit c4)

-- CXbc-box @041041: 17 steps
lem-CXbc-box-at041041 : Ws → ⟪ (ℓ "书侏书") ⟫ʷ ≈ ⟪ (ℓ "侏二") ⟫ʷ
lem-CXbc-box-at041041 c4 = derive (ℓ "书侏书") (ℓ "侏二")
  (rw 1 (q398 c4) ∷
   rw 0 (q335 c4) ∷
   rw⁻ 1 (q399 c4) ∷
   rw 3 (q400 c4) ∷
   rw 2 (q335 c4) ∷
   rw 5 (q401 c4) ∷
   rw⁻ 9 (q327 c4) ∷
   rw 8 (q402 c4) ∷
   rw⁻ 7 (q403 c4) ∷
   rw 6 (q402 c4) ∷
   rw⁻ 5 (q325 c4) ∷
   rw⁻ 6 (q401 c4) ∷
   rw 4 (q136 c4) ∷
   rw⁻ 3 (q399 c4) ∷
   rw 4 (q404 c4) ∷
   rw⁻ 0 (q398 c4) ∷
   rw⁻ 1 (q405 c4) ∷ []) Eq.refl

private
  q406 : Ws → Eqn
  q406 c4 = wpE 1386 c4
  q407 : Ws → Eqn
  q407 c4 = wpE 1387 c4
  q408 : Ws → Eqn
  q408 c4 = wlE 1021 (lit c4)
  q409 : Ws → Eqn
  q409 c4 = wlE 905 (lit c4)
  q410 : Ws → Eqn
  q410 c4 = wpE 1388 c4
  q411 : Ws → Eqn
  q411 c4 = wpE 1389 c4
  q412 : Ws → Eqn
  q412 c4 = wpE 1390 c4
  q413 : Ws → Eqn
  q413 c4 = wpE 593 c4
  q414 : Ws → Eqn
  q414 c4 = wlE 1565 (lit c4)

-- CXcb-box @041041: 18 steps
lem-CXcb-box-at041041 : Ws → ⟪ (ℓ "乶侏乶") ⟫ʷ ≈ ⟪ (ℓ "侏亐") ⟫ʷ
lem-CXcb-box-at041041 c4 = derive (ℓ "乶侏乶") (ℓ "侏亐")
  (rw 1 (q398 c4) ∷
   rw 0 (q406 c4) ∷
   rw⁻ 2 (q407 c4) ∷
   rw⁻ 1 (q408 c4) ∷
   rw 4 (q409 c4) ∷
   rw 8 (q410 c4) ∷
   rw 7 (q321 c4) ∷
   rw 6 (q336 c4) ∷
   rw 5 (q321 c4) ∷
   rw 4 (q337 c4) ∷
   rw⁻ 5 (q409 c4) ∷
   rw⁻ 3 (q411 c4) ∷
   rw 2 (q406 c4) ∷
   rw 3 (q412 c4) ∷
   rw 4 (q413 c4) ∷
   rw⁻ 3 (q408 c4) ∷
   rw⁻ 0 (q398 c4) ∷
   rw⁻ 1 (q414 c4) ∷ []) Eq.refl

private
  q415 : Ws → Eqn
  q415 c4 = sE 419 (lem-box-tQ-at0410233241 c4)
  q416 : Ws → Eqn
  q416 c4 = sE 427 (lem-tP-at0410233241 c4)
  q417 : Ws → Eqn
  q417 c4 = wlE 1569 (lit c4)
  q418 : Ws → Eqn
  q418 c4 = wlE 1570 (lit c4)
  q419 : Ws → Eqn
  q419 c4 = sE 227 (lem-comm-CZ12-TOFF403 c4)
  q420 : Ws → Eqn
  q420 c4 = wlE 1571 (lit c4)

-- P-box @0410233241: 8 steps
lem-P-box-at0410233241 : Ws → ⟪ (ℓ "享侑享") ⟫ʷ ≈ ⟪ (ℓ "侑") ⟫ʷ
lem-P-box-at0410233241 c4 = derive (ℓ "享侑享") (ℓ "侑")
  (rw 1 (q415 c4) ∷
   rw⁻ 0 (q416 c4) ∷
   rw⁻ 1 (q417 c4) ∷
   rw⁻ 3 (q416 c4) ∷
   rw⁻ 4 (q418 c4) ∷
   rw 2 (q419 c4) ∷
   rw⁻ 3 (q420 c4) ∷
   rw⁻ 0 (q415 c4) ∷ []) Eq.refl

private
  q421 : Ws → Eqn
  q421 c4 = wpE 316 c4
  q422 : Ws → Eqn
  q422 c4 = wlE 468 (lit c4)
  q423 : Ws → Eqn
  q423 c4 = eqn (ℓ "么丣") (ℓ "丣么") (c₃ ((CS • CS • CS) ↑) ((S • S • S) ↑))
  q424 : Ws → Eqn
  q424 c4 = sE 383 (lem-comm-TOFF403-CSd12 c4)
  q425 : Ws → Eqn
  q425 c4 = eqn (ℓ "么丢") (ℓ "丢么") (c₃ ((CS • CS • CS) ↑) (S ↑))
  q426 : Ws → Eqn
  q426 c4 = wlE 469 (lit c4)
  q427 : Ws → Eqn
  q427 c4 = eqn (ℓ "丷丢") (ℓ "丢丷") (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S))
  q428 : Ws → Eqn
  q428 c4 = sE 197 (lem-comm-CSd03-TOFF412 c4)
  q429 : Ws → Eqn
  q429 c4 = eqn (ℓ "丷丣") (ℓ "丣丷") (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S • S • S))

-- VPQ @0410233241: 14 steps
lem-VPQ-at0410233241 : Ws → ⟪ (ℓ "亣亠享亨") ⟫ʷ ≈ ⟪ (ℓ "享亨亣亠") ⟫ʷ
lem-VPQ-at0410233241 c4 = derive (ℓ "亣亠享亨") (ℓ "享亨亣亠")
  (rw⁻ 0 (q421 c4) ∷
   rw⁻ 4 (q422 c4) ∷
   rw⁻ 3 (q423 c4) ∷
   rw 2 (q424 c4) ∷
   rw⁻ 1 (q425 c4) ∷
   rw 0 (q426 c4) ∷
   rw 4 (q347 c4) ∷
   rw 3 (q416 c4) ∷
   rw⁻ 4 (q347 c4) ∷
   rw 1 (q427 c4) ∷
   rw 2 (q428 c4) ∷
   rw 3 (q429 c4) ∷
   rw 0 (q422 c4) ∷
   rw 2 (q421 c4) ∷ []) Eq.refl

private
  q430 : Ws → Eqn
  q430 c4 = sE 215 (lem-comm-TOFF412-CSd03 c4)
  q431 : Ws → Eqn
  q431 c4 = sE 428 (lem-tP-at0412213043 c4)
  q432 : Ws → Eqn
  q432 c4 = sE 200 (lem-comm-CSd12-TOFF403 c4)

-- VPQ @0412213043: 14 steps
lem-VPQ-at0412213043 : Ws → ⟪ (ℓ "享亨亣亠") ⟫ʷ ≈ ⟪ (ℓ "亣亠享亨") ⟫ʷ
lem-VPQ-at0412213043 c4 = derive (ℓ "享亨亣亠") (ℓ "亣亠享亨")
  (rw⁻ 0 (q422 c4) ∷
   rw⁻ 4 (q421 c4) ∷
   rw⁻ 3 (q429 c4) ∷
   rw 2 (q430 c4) ∷
   rw⁻ 1 (q427 c4) ∷
   rw⁻ 0 (q426 c4) ∷
   rw 4 (q347 c4) ∷
   rw 3 (q431 c4) ∷
   rw⁻ 4 (q347 c4) ∷
   rw 1 (q425 c4) ∷
   rw 2 (q432 c4) ∷
   rw 3 (q423 c4) ∷
   rw 0 (q421 c4) ∷
   rw 2 (q422 c4) ∷ []) Eq.refl

-- P-box @04122041: 8 steps
lem-P-box-at04122041 : Ws → ⟪ (ℓ "亯侗亯") ⟫ʷ ≈ ⟪ (ℓ "侗") ⟫ʷ
lem-P-box-at04122041 c4 = derive (ℓ "亯侗亯") (ℓ "侗")
  (rw 1 (q320 c4) ∷
   rw⁻ 0 (q358 c4) ∷
   rw⁻ 1 (q371 c4) ∷
   rw⁻ 3 (q358 c4) ∷
   rw⁻ 4 (q372 c4) ∷
   rw 2 (q373 c4) ∷
   rw⁻ 3 (q374 c4) ∷
   rw⁻ 0 (q320 c4) ∷ []) Eq.refl

private
  q433 : Ws → Eqn
  q433 c4 = sE 424 (lem-box-tQ-at04233240 c4)
  q434 : Ws → Eqn
  q434 c4 = wlE 1586 (lit c4)
  q435 : Ws → Eqn
  q435 c4 = wpE 717 c4
  q436 : Ws → Eqn
  q436 c4 = wpE 1396 c4
  q437 : Ws → Eqn
  q437 c4 = wlE 289 (lit c4)
  q438 : Ws → Eqn
  q438 c4 = wpE 39 c4
  q439 : Ws → Eqn
  q439 c4 = sE 3 (lem-comm-CX13-CCZ024 c4)
  q440 : Ws → Eqn
  q440 c4 = wpE 32 c4
  q441 : Ws → Eqn
  q441 c4 = wpE 21 c4
  q442 : Ws → Eqn
  q442 c4 = wpE 718 c4

-- CXbc-box @04233240: 17 steps
lem-CXbc-box-at04233240 : Ws → ⟪ (ℓ "乶侖乶") ⟫ʷ ≈ ⟪ (ℓ "侖亐") ⟫ʷ
lem-CXbc-box-at04233240 c4 = derive (ℓ "乶侖乶") (ℓ "侖亐")
  (rw 1 (q433 c4) ∷
   rw 0 (q434 c4) ∷
   rw⁻ 1 (q435 c4) ∷
   rw 3 (q436 c4) ∷
   rw 2 (q434 c4) ∷
   rw 5 (q437 c4) ∷
   rw⁻ 9 (q438 c4) ∷
   rw 8 (q439 c4) ∷
   rw⁻ 7 (q440 c4) ∷
   rw 6 (q439 c4) ∷
   rw⁻ 5 (q441 c4) ∷
   rw⁻ 6 (q437 c4) ∷
   rw⁻ 4 (q91 c4) ∷
   rw⁻ 3 (q435 c4) ∷
   rw 4 (q442 c4) ∷
   rw⁻ 0 (q433 c4) ∷
   rw⁻ 1 (q414 c4) ∷ []) Eq.refl

private
  q443 : Ws → Eqn
  q443 c4 = wlE 1587 (lit c4)
  q444 : Ws → Eqn
  q444 c4 = wpE 1397 c4
  q445 : Ws → Eqn
  q445 c4 = wpE 82 c4
  q446 : Ws → Eqn
  q446 c4 = wlE 155 (lit c4)
  q447 : Ws → Eqn
  q447 c4 = wpE 1398 c4
  q448 : Ws → Eqn
  q448 c4 = wlE 1588 (lit c4)
  q449 : Ws → Eqn
  q449 c4 = sE 381 (lem-comm-CS02-TOFF413 c4)
  q450 : Ws → Eqn
  q450 c4 = wlE 1589 (lit c4)
  q451 : Ws → Eqn
  q451 c4 = wlE 1590 (lit c4)
  q452 : Ws → Eqn
  q452 c4 = wpE 142 c4

-- CXcb-box @04233240: 18 steps
lem-CXcb-box-at04233240 : Ws → ⟪ (ℓ "书侖书") ⟫ʷ ≈ ⟪ (ℓ "侖二") ⟫ʷ
lem-CXcb-box-at04233240 c4 = derive (ℓ "书侖书") (ℓ "侖二")
  (rw 1 (q433 c4) ∷
   rw 0 (q443 c4) ∷
   rw⁻ 2 (q444 c4) ∷
   rw⁻ 1 (q445 c4) ∷
   rw 4 (q446 c4) ∷
   rw 8 (q447 c4) ∷
   rw 7 (q448 c4) ∷
   rw 6 (q360 c4) ∷
   rw 5 (q448 c4) ∷
   rw 4 (q449 c4) ∷
   rw⁻ 5 (q446 c4) ∷
   rw 3 (q450 c4) ∷
   rw 2 (q443 c4) ∷
   rw 3 (q451 c4) ∷
   rw 4 (q452 c4) ∷
   rw⁻ 3 (q445 c4) ∷
   rw⁻ 0 (q433 c4) ∷
   rw⁻ 1 (q405 c4) ∷ []) Eq.refl

private
  q453 : Ws → Eqn
  q453 c4 = sE 425 (lem-box-tQ-at0440 c4)
  q454 : Ws → Eqn
  q454 c4 = sE 430 (lem-tP-at0440 c4)
  q455 : Ws → Eqn
  q455 c4 = wpE 1399 c4
  q456 : Ws → Eqn
  q456 c4 = wpE 1400 c4
  q457 : Ws → Eqn
  q457 c4 = sE 373 (lem-comm-CZ03-TOFF412 c4)
  q458 : Ws → Eqn
  q458 c4 = wpE 375 c4

-- P-box @0440: 8 steps
lem-P-box-at0440 : Ws → ⟪ (ℓ "亣侔亣") ⟫ʷ ≈ ⟪ (ℓ "侔") ⟫ʷ
lem-P-box-at0440 c4 = derive (ℓ "亣侔亣") (ℓ "侔")
  (rw 1 (q453 c4) ∷
   rw⁻ 0 (q454 c4) ∷
   rw⁻ 1 (q455 c4) ∷
   rw⁻ 3 (q454 c4) ∷
   rw⁻ 4 (q456 c4) ∷
   rw 2 (q457 c4) ∷
   rw⁻ 3 (q458 c4) ∷
   rw⁻ 0 (q453 c4) ∷ []) Eq.refl

-- VPQ @0440: 14 steps
lem-VPQ-at0440 : Ws → ⟪ (ℓ "享亨亣亠") ⟫ʷ ≈ ⟪ (ℓ "亣亠享亨") ⟫ʷ
lem-VPQ-at0440 c4 = derive (ℓ "享亨亣亠") (ℓ "亣亠享亨")
  (rw⁻ 0 (q422 c4) ∷
   rw⁻ 4 (q421 c4) ∷
   rw⁻ 3 (q429 c4) ∷
   rw 2 (q430 c4) ∷
   rw⁻ 1 (q427 c4) ∷
   rw⁻ 0 (q426 c4) ∷
   rw 4 (q347 c4) ∷
   rw 3 (q454 c4) ∷
   rw⁻ 4 (q347 c4) ∷
   rw 1 (q425 c4) ∷
   rw 2 (q432 c4) ∷
   rw 3 (q423 c4) ∷
   rw 0 (q421 c4) ∷
   rw 2 (q422 c4) ∷ []) Eq.refl

private
  q459 : Ws → Eqn
  q459 c4 = sE 422 (lem-box-tQ-at0413203142 c4)
  q460 : Ws → Eqn
  q460 c4 = wpE 1401 c4
  q461 : Ws → Eqn
  q461 c4 = wpE 1402 c4
  q462 : Ws → Eqn
  q462 c4 = wlE 757 (lit c4)
  q463 : Ws → Eqn
  q463 c4 = wlE 639 (lit c4)
  q464 : Ws → Eqn
  q464 c4 = wpE 679 c4
  q465 : Ws → Eqn
  q465 c4 = wpE 515 c4
  q466 : Ws → Eqn
  q466 c4 = wlE 1597 (lit c4)

-- CXbc-box @0413203142: 17 steps
lem-CXbc-box-at0413203142 : Ws → ⟪ (ℓ "丬侜丬") ⟫ʷ ≈ ⟪ (ℓ "侜亘") ⟫ʷ
lem-CXbc-box-at0413203142 c4 = derive (ℓ "丬侜丬") (ℓ "侜亘")
  (rw 1 (q459 c4) ∷
   rw 0 (q460 c4) ∷
   rw⁻ 1 (q121 c4) ∷
   rw 3 (q461 c4) ∷
   rw 2 (q460 c4) ∷
   rw 5 (q462 c4) ∷
   rw⁻ 9 (q463 c4) ∷
   rw 8 (q124 c4) ∷
   rw⁻ 7 (q464 c4) ∷
   rw 6 (q124 c4) ∷
   rw⁻ 5 (q465 c4) ∷
   rw⁻ 6 (q462 c4) ∷
   rw 4 (q78 c4) ∷
   rw⁻ 3 (q121 c4) ∷
   rw 4 (q127 c4) ∷
   rw⁻ 0 (q459 c4) ∷
   rw⁻ 1 (q466 c4) ∷ []) Eq.refl

private
  q467 : Ws → Eqn
  q467 c4 = wpE 1403 c4
  q468 : Ws → Eqn
  q468 c4 = wlE 1598 (lit c4)
  q469 : Ws → Eqn
  q469 c4 = wlE 297 (lit c4)
  q470 : Ws → Eqn
  q470 c4 = wpE 1404 c4
  q471 : Ws → Eqn
  q471 c4 = wpE 1405 c4
  q472 : Ws → Eqn
  q472 c4 = sE 382 (lem-comm-CS12-TOFF403 c4)
  q473 : Ws → Eqn
  q473 c4 = wpE 1377 c4
  q474 : Ws → Eqn
  q474 c4 = wpE 1406 c4
  q475 : Ws → Eqn
  q475 c4 = wlE 1599 (lit c4)

-- CXcb-box @0413203142: 18 steps
lem-CXcb-box-at0413203142 : Ws → ⟪ (ℓ "乄侜乄") ⟫ʷ ≈ ⟪ (ℓ "侜交") ⟫ʷ
lem-CXcb-box-at0413203142 c4 = derive (ℓ "乄侜乄") (ℓ "侜交")
  (rw 1 (q459 c4) ∷
   rw 0 (q467 c4) ∷
   rw⁻ 2 (q468 c4) ∷
   rw⁻ 1 (q130 c4) ∷
   rw 4 (q469 c4) ∷
   rw 8 (q470 c4) ∷
   rw 7 (q471 c4) ∷
   rw 6 (q432 c4) ∷
   rw 5 (q471 c4) ∷
   rw 4 (q472 c4) ∷
   rw⁻ 5 (q469 c4) ∷
   rw⁻ 3 (q473 c4) ∷
   rw 2 (q467 c4) ∷
   rw 3 (q474 c4) ∷
   rw 4 (q39 c4) ∷
   rw⁻ 3 (q130 c4) ∷
   rw⁻ 0 (q459 c4) ∷
   rw⁻ 1 (q475 c4) ∷ []) Eq.refl

private
  q476 : Ws → Eqn
  q476 c4 = sE 297 (lem-comm-TOFF214-CSd03 c4)
  q477 : Ws → Eqn
  q477 c4 = sE 426 (lem-tP-at02142140 c4)

-- VPQ @02142140: 14 steps
lem-VPQ-at02142140 : Ws → ⟪ (ℓ "亪亨亚亘") ⟫ʷ ≈ ⟪ (ℓ "亚亘亪亨") ⟫ʷ
lem-VPQ-at02142140 c4 = derive (ℓ "亪亨亚亘") (ℓ "亚亘亪亨")
  (rw⁻ 0 (q106 c4) ∷
   rw⁻ 4 (q105 c4) ∷
   rw⁻ 3 (q115 c4) ∷
   rw 2 (q476 c4) ∷
   rw⁻ 1 (q113 c4) ∷
   rw⁻ 0 (q110 c4) ∷
   rw 4 (q111 c4) ∷
   rw 3 (q477 c4) ∷
   rw⁻ 4 (q111 c4) ∷
   rw 1 (q109 c4) ∷
   rw 2 (q133 c4) ∷
   rw 3 (q107 c4) ∷
   rw 0 (q105 c4) ∷
   rw 2 (q106 c4) ∷ []) Eq.refl

private
  q478 : Ws → Eqn
  q478 c4 = sE 423 (lem-box-tQ-at0413213042 c4)
  q479 : Ws → Eqn
  q479 c4 = wpE 1407 c4
  q480 : Ws → Eqn
  q480 c4 = wlE 1603 (lit c4)
  q481 : Ws → Eqn
  q481 c4 = wpE 92 c4
  q482 : Ws → Eqn
  q482 c4 = wpE 87 c4
  q483 : Ws → Eqn
  q483 c4 = wpE 81 c4

-- CXbc-box @0413213042: 17 steps
lem-CXbc-box-at0413213042 : Ws → ⟪ (ℓ "乄侞乄") ⟫ʷ ≈ ⟪ (ℓ "侞交") ⟫ʷ
lem-CXbc-box-at0413213042 c4 = derive (ℓ "乄侞乄") (ℓ "侞交")
  (rw 1 (q478 c4) ∷
   rw 0 (q479 c4) ∷
   rw⁻ 1 (q71 c4) ∷
   rw 3 (q480 c4) ∷
   rw 2 (q479 c4) ∷
   rw 5 (q469 c4) ∷
   rw⁻ 9 (q481 c4) ∷
   rw 8 (q75 c4) ∷
   rw⁻ 7 (q482 c4) ∷
   rw 6 (q75 c4) ∷
   rw⁻ 5 (q483 c4) ∷
   rw⁻ 6 (q469 c4) ∷
   rw⁻ 4 (q78 c4) ∷
   rw⁻ 3 (q71 c4) ∷
   rw 4 (q79 c4) ∷
   rw⁻ 0 (q478 c4) ∷
   rw⁻ 1 (q475 c4) ∷ []) Eq.refl

private
  q484 : Ws → Eqn
  q484 c4 = wpE 1408 c4
  q485 : Ws → Eqn
  q485 c4 = wpE 1374 c4
  q486 : Ws → Eqn
  q486 c4 = wlE 1546 (lit c4)
  q487 : Ws → Eqn
  q487 c4 = wpE 1409 c4
  q488 : Ws → Eqn
  q488 c4 = wpE 1410 c4
  q489 : Ws → Eqn
  q489 c4 = wpE 669 c4

-- CXcb-box @0413213042: 18 steps
lem-CXcb-box-at0413213042 : Ws → ⟪ (ℓ "丬侞丬") ⟫ʷ ≈ ⟪ (ℓ "侞亘") ⟫ʷ
lem-CXcb-box-at0413213042 c4 = derive (ℓ "丬侞丬") (ℓ "侞亘")
  (rw 1 (q478 c4) ∷
   rw 0 (q484 c4) ∷
   rw⁻ 2 (q485 c4) ∷
   rw⁻ 1 (q83 c4) ∷
   rw 4 (q462 c4) ∷
   rw 8 (q486 c4) ∷
   rw 7 (q487 c4) ∷
   rw 6 (q360 c4) ∷
   rw 5 (q487 c4) ∷
   rw 4 (q449 c4) ∷
   rw⁻ 5 (q462 c4) ∷
   rw 3 (q473 c4) ∷
   rw 2 (q484 c4) ∷
   rw 3 (q488 c4) ∷
   rw 4 (q489 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   rw⁻ 0 (q478 c4) ∷
   rw⁻ 1 (q466 c4) ∷ []) Eq.refl

private
  q490 : Ws → Eqn
  q490 c4 = sE 429 (lem-tP-at0413203142 c4)

-- P-box @0413203142: 8 steps
lem-P-box-at0413203142 : Ws → ⟪ (ℓ "享侜享") ⟫ʷ ≈ ⟪ (ℓ "侜") ⟫ʷ
lem-P-box-at0413203142 c4 = derive (ℓ "享侜享") (ℓ "侜")
  (rw 1 (q459 c4) ∷
   rw⁻ 0 (q490 c4) ∷
   rw⁻ 1 (q417 c4) ∷
   rw⁻ 3 (q490 c4) ∷
   rw⁻ 4 (q418 c4) ∷
   rw 2 (q419 c4) ∷
   rw⁻ 3 (q420 c4) ∷
   rw⁻ 0 (q459 c4) ∷ []) Eq.refl

-- VPQ @0413203142: 14 steps
lem-VPQ-at0413203142 : Ws → ⟪ (ℓ "亣亠享亨") ⟫ʷ ≈ ⟪ (ℓ "享亨亣亠") ⟫ʷ
lem-VPQ-at0413203142 c4 = derive (ℓ "亣亠享亨") (ℓ "享亨亣亠")
  (rw⁻ 0 (q421 c4) ∷
   rw⁻ 4 (q422 c4) ∷
   rw⁻ 3 (q423 c4) ∷
   rw 2 (q424 c4) ∷
   rw⁻ 1 (q425 c4) ∷
   rw 0 (q426 c4) ∷
   rw 4 (q347 c4) ∷
   rw 3 (q490 c4) ∷
   rw⁻ 4 (q347 c4) ∷
   rw 1 (q427 c4) ∷
   rw 2 (q428 c4) ∷
   rw 3 (q429 c4) ∷
   rw 0 (q422 c4) ∷
   rw 2 (q421 c4) ∷ []) Eq.refl

private
  q491 : Ws → Eqn
  q491 c4 = wlE 1609 (lit c4)
  q492 : Ws → Eqn
  q492 c4 = wpE 104 c4
  q493 : Ws → Eqn
  q493 c4 = wpE 1413 c4
  q494 : Ws → Eqn
  q494 c4 = wpE 1 c4
  q495 : Ws → Eqn
  q495 c4 = sE 2 (lem-comm-CX12-CCZ034 c4)
  q496 : Ws → Eqn
  q496 c4 = wpE 2 c4
  q497 : Ws → Eqn
  q497 c4 = wpE 3 c4
  q498 : Ws → Eqn
  q498 c4 = wpE 110 c4

-- CXbc-box @0440: 17 steps
lem-CXbc-box-at0440 : Ws → ⟪ (ℓ "书侔书") ⟫ʷ ≈ ⟪ (ℓ "侔二") ⟫ʷ
lem-CXbc-box-at0440 c4 = derive (ℓ "书侔书") (ℓ "侔二")
  (rw 1 (q453 c4) ∷
   rw 0 (q491 c4) ∷
   rw⁻ 1 (q492 c4) ∷
   rw 3 (q493 c4) ∷
   rw 2 (q491 c4) ∷
   rw 5 (q446 c4) ∷
   rw⁻ 9 (q494 c4) ∷
   rw 8 (q495 c4) ∷
   rw⁻ 7 (q496 c4) ∷
   rw 6 (q495 c4) ∷
   rw⁻ 5 (q497 c4) ∷
   rw⁻ 6 (q446 c4) ∷
   rw 4 (q91 c4) ∷
   rw⁻ 3 (q492 c4) ∷
   rw 4 (q498 c4) ∷
   rw⁻ 0 (q453 c4) ∷
   rw⁻ 1 (q405 c4) ∷ []) Eq.refl

private
  q499 : Ws → Eqn
  q499 c4 = wlE 1610 (lit c4)
  q500 : Ws → Eqn
  q500 c4 = wpE 1414 c4
  q501 : Ws → Eqn
  q501 c4 = wpE 101 c4
  q502 : Ws → Eqn
  q502 c4 = wpE 1415 c4
  q503 : Ws → Eqn
  q503 c4 = wlE 1611 (lit c4)
  q504 : Ws → Eqn
  q504 c4 = sE 190 (lem-comm-CS03-TOFF412 c4)
  q505 : Ws → Eqn
  q505 c4 = wlE 1612 (lit c4)
  q506 : Ws → Eqn
  q506 c4 = wpE 186 c4

-- CXcb-box @0440: 18 steps
lem-CXcb-box-at0440 : Ws → ⟪ (ℓ "乶侔乶") ⟫ʷ ≈ ⟪ (ℓ "侔亐") ⟫ʷ
lem-CXcb-box-at0440 c4 = derive (ℓ "乶侔乶") (ℓ "侔亐")
  (rw 1 (q453 c4) ∷
   rw 0 (q499 c4) ∷
   rw⁻ 2 (q500 c4) ∷
   rw⁻ 1 (q501 c4) ∷
   rw 4 (q437 c4) ∷
   rw 8 (q502 c4) ∷
   rw 7 (q503 c4) ∷
   rw 6 (q428 c4) ∷
   rw 5 (q503 c4) ∷
   rw 4 (q504 c4) ∷
   rw⁻ 5 (q437 c4) ∷
   rw⁻ 3 (q450 c4) ∷
   rw 2 (q499 c4) ∷
   rw 3 (q505 c4) ∷
   rw 4 (q506 c4) ∷
   rw⁻ 3 (q501 c4) ∷
   rw⁻ 0 (q453 c4) ∷
   rw⁻ 1 (q414 c4) ∷ []) Eq.refl
