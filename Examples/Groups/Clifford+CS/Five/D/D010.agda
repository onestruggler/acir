{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD010 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D010 (Sᴰ : SD010) where

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
  lem-comm-CS13-TOFF024 : Ws → St 192
  lem-comm-CS13-TOFF024 = pickᴰ 0 Sᴰ
  lem-comm-CS14-TOFF023 : Ws → St 193
  lem-comm-CS14-TOFF023 = pickᴰ 1 Sᴰ
  lem-comm-CS24-TOFF013 : Ws → St 195
  lem-comm-CS24-TOFF013 = pickᴰ 2 Sᴰ
  lem-comm-CSd04-TOFF213 : Ws → St 198
  lem-comm-CSd04-TOFF213 = pickᴰ 3 Sᴰ
  lem-comm-CSd12-TOFF034 : Ws → St 63
  lem-comm-CSd12-TOFF034 = pickᴰ 4 Sᴰ
  lem-comm-CSd13-TOFF024 : Ws → St 201
  lem-comm-CSd13-TOFF024 = pickᴰ 5 Sᴰ
  lem-comm-CSd14-TOFF023 : Ws → St 202
  lem-comm-CSd14-TOFF023 = pickᴰ 6 Sᴰ
  lem-comm-CSd23-TOFF014 : Ws → St 203
  lem-comm-CSd23-TOFF014 = pickᴰ 7 Sᴰ
  lem-comm-CSd24-TOFF013 : Ws → St 205
  lem-comm-CSd24-TOFF013 = pickᴰ 8 Sᴰ
  lem-comm-CX04-CCZ123 : Ws → St 1
  lem-comm-CX04-CCZ123 = pickᴰ 9 Sᴰ
  lem-comm-CX13-CCZ024 : Ws → St 3
  lem-comm-CX13-CCZ024 = pickᴰ 10 Sᴰ
  lem-comm-CX14-CCZ023 : Ws → St 4
  lem-comm-CX14-CCZ023 = pickᴰ 11 Sᴰ
  lem-comm-CX21-CCZ034 : Ws → St 5
  lem-comm-CX21-CCZ034 = pickᴰ 12 Sᴰ
  lem-comm-CX23-CCZ014 : Ws → St 6
  lem-comm-CX23-CCZ014 = pickᴰ 13 Sᴰ
  lem-comm-CX24-CCZ013 : Ws → St 7
  lem-comm-CX24-CCZ013 = pickᴰ 14 Sᴰ
  lem-comm-CX31-CCZ024 : Ws → St 8
  lem-comm-CX31-CCZ024 = pickᴰ 15 Sᴰ
  lem-comm-CX32-CCZ014 : Ws → St 9
  lem-comm-CX32-CCZ014 = pickᴰ 16 Sᴰ
  lem-comm-CX42-CCZ013 : Ws → St 10
  lem-comm-CX42-CCZ013 = pickᴰ 17 Sᴰ
  lem-comm-CZ04-TOFF213 : Ws → St 206
  lem-comm-CZ04-TOFF213 = pickᴰ 18 Sᴰ
  lem-comm-CZ14-TOFF023 : Ws → St 208
  lem-comm-CZ14-TOFF023 = pickᴰ 19 Sᴰ
  lem-comm-TOFF013-CSd24 : Ws → St 210
  lem-comm-TOFF013-CSd24 = pickᴰ 20 Sᴰ
  lem-comm-TOFF014-CSd23 : Ws → St 211
  lem-comm-TOFF014-CSd23 = pickᴰ 21 Sᴰ
  lem-comm-TOFF024-CSd13 : Ws → St 212
  lem-comm-TOFF024-CSd13 = pickᴰ 22 Sᴰ
  lem-comm-TOFF204-CSd13 : Ws → St 213
  lem-comm-TOFF204-CSd13 = pickᴰ 23 Sᴰ
  lem-comm-CS02-TOFF314 : Ws → St 282
  lem-comm-CS02-TOFF314 = pickᴰ 24 Sᴰ
  lem-comm-CS03-TOFF214 : Ws → St 283
  lem-comm-CS03-TOFF214 = pickᴰ 25 Sᴰ
  lem-comm-CS04-CCZ123 : Ws → St 216
  lem-comm-CS04-CCZ123 = pickᴰ 26 Sᴰ
  lem-comm-CS04-TOFF213 : Ws → St 284
  lem-comm-CS04-TOFF213 = pickᴰ 27 Sᴰ
  lem-comm-CS04-TOFF312 : Ws → St 217
  lem-comm-CS04-TOFF312 = pickᴰ 28 Sᴰ
  lem-comm-CS12-TOFF304 : Ws → St 285
  lem-comm-CS12-TOFF304 = pickᴰ 29 Sᴰ
  lem-comm-CS13-TOFF204 : Ws → St 218
  lem-comm-CS13-TOFF204 = pickᴰ 30 Sᴰ
  lem-comm-CS23-TOFF014 : Ws → St 286
  lem-comm-CS23-TOFF014 = pickᴰ 31 Sᴰ
  lem-comm-CSd02-TOFF314 : Ws → St 287
  lem-comm-CSd02-TOFF314 = pickᴰ 32 Sᴰ
  lem-comm-CSd03-TOFF214 : Ws → St 288
  lem-comm-CSd03-TOFF214 = pickᴰ 33 Sᴰ
  lem-comm-CSd04-CCZ123 : Ws → St 220
  lem-comm-CSd04-CCZ123 = pickᴰ 34 Sᴰ
  lem-comm-CSd04-TOFF312 : Ws → St 221
  lem-comm-CSd04-TOFF312 = pickᴰ 35 Sᴰ
  lem-comm-CSd12-TOFF304 : Ws → St 222
  lem-comm-CSd12-TOFF304 = pickᴰ 36 Sᴰ
  lem-comm-CSd13-TOFF204 : Ws → St 223
  lem-comm-CSd13-TOFF204 = pickᴰ 37 Sᴰ
  lem-comm-CSd14-TOFF203 : Ws → St 289
  lem-comm-CSd14-TOFF203 = pickᴰ 38 Sᴰ
  lem-comm-CSd14-TOFF302 : Ws → St 290
  lem-comm-CSd14-TOFF302 = pickᴰ 39 Sᴰ
  lem-comm-CSd24-TOFF301 : Ws → St 77
  lem-comm-CSd24-TOFF301 = pickᴰ 40 Sᴰ
  lem-comm-CX40-CCZ123 : Ws → St 20
  lem-comm-CX40-CCZ123 = pickᴰ 41 Sᴰ
  lem-comm-CX41-CCZ023 : Ws → St 21
  lem-comm-CX41-CCZ023 = pickᴰ 42 Sᴰ
  lem-comm-CZ13-TOFF024 : Ws → St 291
  lem-comm-CZ13-TOFF024 = pickᴰ 43 Sᴰ
  lem-comm-CZ13-TOFF204 : Ws → St 292
  lem-comm-CZ13-TOFF204 = pickᴰ 44 Sᴰ
  lem-comm-CZ14-TOFF203 : Ws → St 293
  lem-comm-CZ14-TOFF203 = pickᴰ 45 Sᴰ
  lem-comm-CZ14-TOFF302 : Ws → St 294
  lem-comm-CZ14-TOFF302 = pickᴰ 46 Sᴰ
  lem-comm-CZ23-TOFF014 : Ws → St 295
  lem-comm-CZ23-TOFF014 = pickᴰ 47 Sᴰ
  lem-comm-TOFF213-CSd04 : Ws → St 296
  lem-comm-TOFF213-CSd04 = pickᴰ 48 Sᴰ
  lem-comm-TOFF214-CSd03 : Ws → St 297
  lem-comm-TOFF214-CSd03 = pickᴰ 49 Sᴰ
  lem-comm-TOFF314-CSd02 : Ws → St 298
  lem-comm-TOFF314-CSd02 = pickᴰ 50 Sᴰ
  lem-comm-TOFF023-CSd14 : Ws → St 229
  lem-comm-TOFF023-CSd14 = pickᴰ 51 Sᴰ
  lem-comm-TOFF203-CSd14 : Ws → St 299
  lem-comm-TOFF203-CSd14 = pickᴰ 52 Sᴰ
  lem-CXbc-box-at0213243140 : Ws → St 300
  lem-CXbc-box-at0213243140 = pickᴰ 53 Sᴰ
  lem-CXcb-box-at0213243140 : Ws → St 301
  lem-CXcb-box-at0213243140 = pickᴰ 54 Sᴰ
  lem-VPQ-at0210213443 : Ws → St 302
  lem-VPQ-at0210213443 = pickᴰ 55 Sᴰ
  lem-VPQ-at0220 : Ws → St 303
  lem-VPQ-at0220 = pickᴰ 56 Sᴰ
  lem-VPQ-at032032 : Ws → St 304
  lem-VPQ-at032032 = pickᴰ 57 Sᴰ
  lem-VPQ-at14233241 : Ws → St 305
  lem-VPQ-at14233241 = pickᴰ 58 Sᴰ
  lem-box-tQ-at0210233441 : Ws → St 306
  lem-box-tQ-at0210233441 = pickᴰ 59 Sᴰ
  lem-box-tQ-at0210243143 : Ws → St 248
  lem-box-tQ-at0210243143 = pickᴰ 60 Sᴰ
  lem-box-tQ-at0214203143 : Ws → St 249
  lem-box-tQ-at0214203143 = pickᴰ 61 Sᴰ
  lem-box-tQ-at0214213043 : Ws → St 250
  lem-box-tQ-at0214213043 = pickᴰ 62 Sᴰ
  lem-box-tQ-at022330 : Ws → St 307
  lem-box-tQ-at022330 = pickᴰ 63 Sᴰ
  lem-box-tQ-at0312213440 : Ws → St 308
  lem-box-tQ-at0312213440 = pickᴰ 64 Sᴰ
  lem-box-tQ-at0312243140 : Ws → St 309
  lem-box-tQ-at0312243140 = pickᴰ 65 Sᴰ
  lem-box-tQ-at0314203142 : Ws → St 310
  lem-box-tQ-at0314203142 = pickᴰ 66 Sᴰ
  lem-box-tQ-at0314213042 : Ws → St 311
  lem-box-tQ-at0314213042 = pickᴰ 67 Sᴰ
  lem-box-tQ-at122331 : Ws → St 255
  lem-box-tQ-at122331 = pickᴰ 68 Sᴰ
  lem-box-tQ-at12233441 : Ws → St 312
  lem-box-tQ-at12233441 = pickᴰ 69 Sᴰ
  lem-box-tQ-at122441 : Ws → St 257
  lem-box-tQ-at122441 = pickᴰ 70 Sᴰ
  lem-box-tQ-at132132 : Ws → St 258
  lem-box-tQ-at132132 = pickᴰ 71 Sᴰ
  lem-box-tQ-at1331 : Ws → St 260
  lem-box-tQ-at1331 = pickᴰ 72 Sᴰ
  lem-box-tQ-at14213243 : Ws → St 313
  lem-box-tQ-at14213243 = pickᴰ 73 Sᴰ
  lem-box-tQ-at143143 : Ws → St 314
  lem-box-tQ-at143143 = pickᴰ 74 Sᴰ
  lem-box-tQ-at1441 : Ws → St 315
  lem-box-tQ-at1441 = pickᴰ 75 Sᴰ
  lem-box-tQ-at2332 : Ws → St 262
  lem-box-tQ-at2332 = pickᴰ 76 Sᴰ
  lem-box-tQ-at243243 : Ws → St 263
  lem-box-tQ-at243243 = pickᴰ 77 Sᴰ
  lem-tP-at0210233441 : Ws → St 316
  lem-tP-at0210233441 = pickᴰ 78 Sᴰ
  lem-tP-at0210243143 : Ws → St 267
  lem-tP-at0210243143 = pickᴰ 79 Sᴰ
  lem-tP-at0213203441 : Ws → St 317
  lem-tP-at0213203441 = pickᴰ 80 Sᴰ
  lem-tP-at0214213043 : Ws → St 268
  lem-tP-at0214213043 = pickᴰ 81 Sᴰ
  lem-tP-at0312243140 : Ws → St 318
  lem-tP-at0312243140 = pickᴰ 82 Sᴰ
  lem-tP-at0314213042 : Ws → St 319
  lem-tP-at0314213042 = pickᴰ 83 Sᴰ
  lem-tP-at12213443 : Ws → St 320
  lem-tP-at12213443 = pickᴰ 84 Sᴰ
  lem-tP-at12233441 : Ws → St 321
  lem-tP-at12233441 = pickᴰ 85 Sᴰ
  lem-tP-at122441 : Ws → St 275
  lem-tP-at122441 = pickᴰ 86 Sᴰ
  lem-tP-at143143 : Ws → St 322
  lem-tP-at143143 = pickᴰ 87 Sᴰ
  lem-tP-at233442 : Ws → St 323
  lem-tP-at233442 = pickᴰ 88 Sᴰ
  lem-tP-at243243 : Ws → St 280
  lem-tP-at243243 = pickᴰ 89 Sᴰ
  lem-CXbc-box-at0220 : Ws → St 324
  lem-CXbc-box-at0220 = pickᴰ 90 Sᴰ
  lem-CXbc-box-at03102132 : Ws → St 325
  lem-CXbc-box-at03102132 = pickᴰ 91 Sᴰ
  lem-CXcb-box-at0220 : Ws → St 326
  lem-CXcb-box-at0220 = pickᴰ 92 Sᴰ
  lem-CXcb-box-at03102132 : Ws → St 327
  lem-CXcb-box-at03102132 = pickᴰ 93 Sᴰ
  lem-VPQ-at0213243140 : Ws → St 328
  lem-VPQ-at0213243140 = pickᴰ 94 Sᴰ
  lem-box-tQ-at0213213440 : Ws → St 329
  lem-box-tQ-at0213213440 = pickᴰ 95 Sᴰ
  lem-box-tQ-at02233440 : Ws → St 330
  lem-box-tQ-at02233440 = pickᴰ 96 Sᴰ
  lem-box-tQ-at022440 : Ws → St 331
  lem-box-tQ-at022440 = pickᴰ 97 Sᴰ
  lem-tP-at0214203143 : Ws → St 332
  lem-tP-at0214203143 = pickᴰ 98 Sᴰ
  lem-tP-at022330 : Ws → St 333
  lem-tP-at022330 = pickᴰ 99 Sᴰ
  lem-tP-at022440 : Ws → St 334
  lem-tP-at022440 = pickᴰ 100 Sᴰ
  lem-tP-at14213243 : Ws → St 335
  lem-tP-at14213243 = pickᴰ 101 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = wlE 629 (lit c4)
  q2 : Ws → Eqn
  q2 c4 = wlE 630 (lit c4)
  q3 : Ws → Eqn
  q3 c4 = wlE 631 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = sE 297 (lem-comm-TOFF214-CSd03 c4)
  q5 : Ws → Eqn
  q5 c4 = wlE 632 (lit c4)
  q6 : Ws → Eqn
  q6 c4 = wpE 514 c4
  q7 : Ws → Eqn
  q7 c4 = wlE 179 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = sE 268 (lem-tP-at0214213043 c4)
  q9 : Ws → Eqn
  q9 c4 = wlE 633 (lit c4)
  q10 : Ws → Eqn
  q10 c4 = sE 289 (lem-comm-CSd14-TOFF203 c4)
  q11 : Ws → Eqn
  q11 c4 = wlE 634 (lit c4)

-- VPQ @0214213043: 14 steps
lem-VPQ-at0214213043 : Ws → ⟪ (ℓ "亪亨亚亘") ⟫ʷ ≈ ⟪ (ℓ "亚亘亪亨") ⟫ʷ
lem-VPQ-at0214213043 c4 = derive (ℓ "亪亨亚亘") (ℓ "亚亘亪亨")
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw 2 (q4 c4) ∷
   rw⁻ 1 (q5 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   rw 4 (q7 c4) ∷
   rw 3 (q8 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw 1 (q9 c4) ∷
   rw 2 (q10 c4) ∷
   rw 3 (q11 c4) ∷
   rw 0 (q2 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q12 : Ws → Eqn
  q12 c4 = sE 299 (lem-comm-TOFF203-CSd14 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 316 (lem-tP-at0210233441 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 288 (lem-comm-CSd03-TOFF214 c4)

-- VPQ @0210233441: 14 steps
lem-VPQ-at0210233441 : Ws → ⟪ (ℓ "亚亘亪亨") ⟫ʷ ≈ ⟪ (ℓ "亪亨亚亘") ⟫ʷ
lem-VPQ-at0210233441 c4 = derive (ℓ "亚亘亪亨") (ℓ "亪亨亚亘")
  (rw⁻ 0 (q2 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 3 (q11 c4) ∷
   rw 2 (q12 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   rw 0 (q6 c4) ∷
   rw 4 (q7 c4) ∷
   rw 3 (q13 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q14 c4) ∷
   rw 3 (q3 c4) ∷
   rw 0 (q1 c4) ∷
   rw 2 (q2 c4) ∷ []) Eq.refl

private
  q15 : Ws → Eqn
  q15 c4 = sE 257 (lem-box-tQ-at122441 c4)
  q16 : Ws → Eqn
  q16 c4 = wpE 519 c4
  q17 : Ws → Eqn
  q17 c4 = wpE 392 c4
  q18 : Ws → Eqn
  q18 c4 = wpE 520 c4
  q19 : Ws → Eqn
  q19 c4 = wlE 644 (lit c4)
  q20 : Ws → Eqn
  q20 c4 = wlE 645 (lit c4)
  q21 : Ws → Eqn
  q21 c4 = sE 7 (lem-comm-CX24-CCZ013 c4)
  q22 : Ws → Eqn
  q22 c4 = wpE 521 c4
  q23 : Ws → Eqn
  q23 c4 = wpE 299 c4
  q24 : Ws → Eqn
  q24 c4 = wpE 394 c4
  q25 : Ws → Eqn
  q25 c4 = wpE 395 c4
  q26 : Ws → Eqn
  q26 c4 = wlE 646 (lit c4)

-- CXbc-box @122441: 17 steps
lem-CXbc-box-at122441 : Ws → ⟪ (ℓ "争仞争") ⟫ʷ ≈ ⟪ (ℓ "仞亨") ⟫ʷ
lem-CXbc-box-at122441 c4 = derive (ℓ "争仞争") (ℓ "仞亨")
  (rw 1 (q15 c4) ∷
   rw 0 (q16 c4) ∷
   rw⁻ 1 (q17 c4) ∷
   rw 3 (q18 c4) ∷
   rw 2 (q16 c4) ∷
   rw 5 (q19 c4) ∷
   rw⁻ 9 (q20 c4) ∷
   rw 8 (q21 c4) ∷
   rw⁻ 7 (q22 c4) ∷
   rw 6 (q21 c4) ∷
   rw⁻ 5 (q23 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw⁻ 4 (q24 c4) ∷
   rw⁻ 3 (q17 c4) ∷
   rw 4 (q25 c4) ∷
   rw⁻ 0 (q15 c4) ∷
   rw⁻ 1 (q26 c4) ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = wpE 522 c4
  q28 : Ws → Eqn
  q28 c4 = wlE 647 (lit c4)
  q29 : Ws → Eqn
  q29 c4 = wpE 523 c4
  q30 : Ws → Eqn
  q30 c4 = wlE 233 (lit c4)
  q31 : Ws → Eqn
  q31 c4 = wpE 524 c4
  q32 : Ws → Eqn
  q32 c4 = wpE 525 c4
  q33 : Ws → Eqn
  q33 c4 = sE 201 (lem-comm-CSd13-TOFF024 c4)
  q34 : Ws → Eqn
  q34 c4 = sE 192 (lem-comm-CS13-TOFF024 c4)
  q35 : Ws → Eqn
  q35 c4 = wpE 72 c4
  q36 : Ws → Eqn
  q36 c4 = wpE 526 c4
  q37 : Ws → Eqn
  q37 c4 = wlE 327 (lit c4)
  q38 : Ws → Eqn
  q38 c4 = wlE 648 (lit c4)

-- CXcb-box @122441: 18 steps
lem-CXcb-box-at122441 : Ws → ⟪ (ℓ "乽仞乽") ⟫ʷ ≈ ⟪ (ℓ "仞交") ⟫ʷ
lem-CXcb-box-at122441 c4 = derive (ℓ "乽仞乽") (ℓ "仞交")
  (rw 1 (q15 c4) ∷
   rw 0 (q27 c4) ∷
   rw⁻ 2 (q28 c4) ∷
   rw⁻ 1 (q29 c4) ∷
   rw 4 (q30 c4) ∷
   rw 8 (q31 c4) ∷
   rw 7 (q32 c4) ∷
   rw 6 (q33 c4) ∷
   rw 5 (q32 c4) ∷
   rw 4 (q34 c4) ∷
   rw⁻ 5 (q30 c4) ∷
   rw 3 (q35 c4) ∷
   rw 2 (q27 c4) ∷
   rw 3 (q36 c4) ∷
   rw⁻ 4 (q37 c4) ∷
   rw⁻ 3 (q29 c4) ∷
   rw⁻ 0 (q15 c4) ∷
   rw⁻ 1 (q38 c4) ∷ []) Eq.refl

private
  q39 : Ws → Eqn
  q39 c4 = wlE 201 (lit c4)
  q40 : Ws → Eqn
  q40 c4 = wpE 50 c4
  q41 : Ws → Eqn
  q41 c4 = eqn (ℓ "下乖") (ℓ "乖下") (c₁ (S • S • S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))
  q42 : Ws → Eqn
  q42 c4 = sE 229 (lem-comm-TOFF023-CSd14 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (ℓ "上乖") (ℓ "乖上") (c₁ (S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))
  q44 : Ws → Eqn
  q44 c4 = wlE 202 (lit c4)
  q45 : Ws → Eqn
  q45 c4 = wlE 159 (lit c4)
  q46 : Ws → Eqn
  q46 c4 = sE 321 (lem-tP-at12233441 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (ℓ "上乣") (ℓ "乣上") (c₁ (S) ((CS • CS • CS) ↑))
  q48 : Ws → Eqn
  q48 c4 = sE 203 (lem-comm-CSd23-TOFF014 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (ℓ "下乣") (ℓ "乣下") (c₁ (S • S • S) ((CS • CS • CS) ↑))

-- VPQ @12233441: 14 steps
lem-VPQ-at12233441 : Ws → ⟪ (ℓ "亙亘井五") ⟫ʷ ≈ ⟪ (ℓ "井五亙亘") ⟫ʷ
lem-VPQ-at12233441 c4 = derive (ℓ "亙亘井五") (ℓ "井五亙亘")
  (rw⁻ 0 (q39 c4) ∷
   rw⁻ 4 (q40 c4) ∷
   rw 3 (q41 c4) ∷
   rw 2 (q42 c4) ∷
   rw 1 (q43 c4) ∷
   rw⁻ 0 (q44 c4) ∷
   rw 4 (q45 c4) ∷
   rw 3 (q46 c4) ∷
   rw⁻ 4 (q45 c4) ∷
   rw⁻ 1 (q47 c4) ∷
   rw 2 (q48 c4) ∷
   rw⁻ 3 (q49 c4) ∷
   rw 0 (q40 c4) ∷
   rw 2 (q39 c4) ∷ []) Eq.refl

private
  q50 : Ws → Eqn
  q50 c4 = sE 248 (lem-box-tQ-at0210243143 c4)
  q51 : Ws → Eqn
  q51 c4 = wpE 534 c4
  q52 : Ws → Eqn
  q52 c4 = wpE 450 c4
  q53 : Ws → Eqn
  q53 c4 = wlE 173 (lit c4)
  q54 : Ws → Eqn
  q54 c4 = wlE 482 (lit c4)
  q55 : Ws → Eqn
  q55 c4 = sE 220 (lem-comm-CSd04-CCZ123 c4)
  q56 : Ws → Eqn
  q56 c4 = sE 216 (lem-comm-CS04-CCZ123 c4)
  q57 : Ws → Eqn
  q57 c4 = wpE 28 c4
  q58 : Ws → Eqn
  q58 c4 = wpE 454 c4
  q59 : Ws → Eqn
  q59 c4 = wpE 535 c4

-- CSu-box-2 @0210243143: 17 steps
lem-CSu-box-2-at0210243143 : Ws → ⟪ (ℓ "乩伱") ⟫ʷ ≈ ⟪ (ℓ "伱乩") ⟫ʷ
lem-CSu-box-2-at0210243143 c4 = derive (ℓ "乩伱") (ℓ "伱乩")
  (rw 1 (q50 c4) ∷
   rw 0 (q51 c4) ∷
   rw 3 (q52 c4) ∷
   rw⁻ 7 (q53 c4) ∷
   rw⁻ 6 (q54 c4) ∷
   rw 5 (q55 c4) ∷
   rw⁻ 4 (q54 c4) ∷
   rw 3 (q56 c4) ∷
   rw⁻ 4 (q52 c4) ∷
   rw 2 (q56 c4) ∷
   rw⁻ 1 (q53 c4) ∷
   rw 4 (q57 c4) ∷
   rw 3 (q58 c4) ∷
   rw 2 (q51 c4) ∷
   rw 3 (q59 c4) ∷
   rw⁻ 3 (q53 c4) ∷
   rw⁻ 0 (q50 c4) ∷ []) Eq.refl

private
  q60 : Ws → Eqn
  q60 c4 = sE 313 (lem-box-tQ-at14213243 c4)
  q61 : Ws → Eqn
  q61 c4 = wpE 541 c4
  q62 : Ws → Eqn
  q62 c4 = wlE 668 (lit c4)
  q63 : Ws → Eqn
  q63 c4 = wpE 542 c4
  q64 : Ws → Eqn
  q64 c4 = wlE 617 (lit c4)
  q65 : Ws → Eqn
  q65 c4 = wpE 543 c4
  q66 : Ws → Eqn
  q66 c4 = sE 21 (lem-comm-CX41-CCZ023 c4)
  q67 : Ws → Eqn
  q67 c4 = wlE 669 (lit c4)
  q68 : Ws → Eqn
  q68 c4 = wlE 670 (lit c4)
  q69 : Ws → Eqn
  q69 c4 = wlE 671 (lit c4)
  q70 : Ws → Eqn
  q70 c4 = wlE 672 (lit c4)
  q71 : Ws → Eqn
  q71 c4 = wlE 673 (lit c4)

-- CXbc-box @14213243: 17 steps
lem-CXbc-box-at14213243 : Ws → ⟪ (ℓ "之仼之") ⟫ʷ ≈ ⟪ (ℓ "仼京") ⟫ʷ
lem-CXbc-box-at14213243 c4 = derive (ℓ "之仼之") (ℓ "仼京")
  (rw 1 (q60 c4) ∷
   rw 0 (q61 c4) ∷
   rw⁻ 1 (q62 c4) ∷
   rw 3 (q63 c4) ∷
   rw 2 (q61 c4) ∷
   rw 5 (q64 c4) ∷
   rw⁻ 9 (q65 c4) ∷
   rw 8 (q66 c4) ∷
   rw⁻ 7 (q67 c4) ∷
   rw 6 (q66 c4) ∷
   rw⁻ 5 (q68 c4) ∷
   rw⁻ 6 (q64 c4) ∷
   rw 4 (q69 c4) ∷
   rw⁻ 3 (q62 c4) ∷
   rw 4 (q70 c4) ∷
   rw⁻ 0 (q60 c4) ∷
   rw⁻ 1 (q71 c4) ∷ []) Eq.refl

private
  q72 : Ws → Eqn
  q72 c4 = wpE 544 c4
  q73 : Ws → Eqn
  q73 c4 = wpE 545 c4
  q74 : Ws → Eqn
  q74 c4 = wlE 674 (lit c4)
  q75 : Ws → Eqn
  q75 c4 = wlE 675 (lit c4)
  q76 : Ws → Eqn
  q76 c4 = wpE 546 c4
  q77 : Ws → Eqn
  q77 c4 = wpE 547 c4
  q78 : Ws → Eqn
  q78 c4 = sE 286 (lem-comm-CS23-TOFF014 c4)
  q79 : Ws → Eqn
  q79 c4 = wpE 548 c4
  q80 : Ws → Eqn
  q80 c4 = wpE 549 c4
  q81 : Ws → Eqn
  q81 c4 = wpE 550 c4
  q82 : Ws → Eqn
  q82 c4 = wlE 676 (lit c4)

-- CXcb-box @14213243: 18 steps
lem-CXcb-box-at14213243 : Ws → ⟪ (ℓ "也仼也") ⟫ʷ ≈ ⟪ (ℓ "仼亰") ⟫ʷ
lem-CXcb-box-at14213243 c4 = derive (ℓ "也仼也") (ℓ "仼亰")
  (rw 1 (q60 c4) ∷
   rw 0 (q72 c4) ∷
   rw⁻ 2 (q73 c4) ∷
   rw⁻ 1 (q74 c4) ∷
   rw 4 (q75 c4) ∷
   rw 8 (q76 c4) ∷
   rw 7 (q77 c4) ∷
   rw 6 (q48 c4) ∷
   rw 5 (q77 c4) ∷
   rw 4 (q78 c4) ∷
   rw⁻ 5 (q75 c4) ∷
   rw⁻ 3 (q79 c4) ∷
   rw 2 (q72 c4) ∷
   rw 3 (q80 c4) ∷
   rw⁻ 4 (q81 c4) ∷
   rw⁻ 3 (q74 c4) ∷
   rw⁻ 0 (q60 c4) ∷
   rw⁻ 1 (q82 c4) ∷ []) Eq.refl

private
  q83 : Ws → Eqn
  q83 c4 = sE 314 (lem-box-tQ-at143143 c4)
  q84 : Ws → Eqn
  q84 c4 = sE 322 (lem-tP-at143143 c4)
  q85 : Ws → Eqn
  q85 c4 = wlE 682 (lit c4)
  q86 : Ws → Eqn
  q86 c4 = wlE 683 (lit c4)
  q87 : Ws → Eqn
  q87 c4 = sE 291 (lem-comm-CZ13-TOFF024 c4)
  q88 : Ws → Eqn
  q88 c4 = wlE 684 (lit c4)

-- P-box @143143: 8 steps
lem-P-box-at143143 : Ws → ⟪ (ℓ "云伅云") ⟫ʷ ≈ ⟪ (ℓ "伅") ⟫ʷ
lem-P-box-at143143 c4 = derive (ℓ "云伅云") (ℓ "伅")
  (rw 1 (q83 c4) ∷
   rw⁻ 0 (q84 c4) ∷
   rw⁻ 1 (q85 c4) ∷
   rw⁻ 3 (q84 c4) ∷
   rw⁻ 4 (q86 c4) ∷
   rw 2 (q87 c4) ∷
   rw⁻ 3 (q88 c4) ∷
   rw⁻ 0 (q83 c4) ∷ []) Eq.refl

private
  q89 : Ws → Eqn
  q89 c4 = wpE 79 c4
  q90 : Ws → Eqn
  q90 c4 = wlE 227 (lit c4)
  q91 : Ws → Eqn
  q91 c4 = eqn (ℓ "下乏") (ℓ "乏下") (c₁ (S • S • S) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q92 : Ws → Eqn
  q92 c4 = sE 212 (lem-comm-TOFF024-CSd13 c4)
  q93 : Ws → Eqn
  q93 c4 = eqn (ℓ "上乏") (ℓ "乏上") (c₁ (S) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q94 : Ws → Eqn
  q94 c4 = wlE 228 (lit c4)
  q95 : Ws → Eqn
  q95 c4 = eqn (ℓ "上乪") (ℓ "乪上") (c₁ (S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑))
  q96 : Ws → Eqn
  q96 c4 = sE 205 (lem-comm-CSd24-TOFF013 c4)
  q97 : Ws → Eqn
  q97 c4 = eqn (ℓ "下乪") (ℓ "乪下") (c₁ (S • S • S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑))

-- VPQ @143143: 14 steps
lem-VPQ-at143143 : Ws → ⟪ (ℓ "亝亜云亐") ⟫ʷ ≈ ⟪ (ℓ "云亐亝亜") ⟫ʷ
lem-VPQ-at143143 c4 = derive (ℓ "亝亜云亐") (ℓ "云亐亝亜")
  (rw⁻ 0 (q89 c4) ∷
   rw⁻ 4 (q90 c4) ∷
   rw 3 (q91 c4) ∷
   rw 2 (q92 c4) ∷
   rw 1 (q93 c4) ∷
   rw⁻ 0 (q94 c4) ∷
   rw 4 (q45 c4) ∷
   rw 3 (q84 c4) ∷
   rw⁻ 4 (q45 c4) ∷
   rw⁻ 1 (q95 c4) ∷
   rw 2 (q96 c4) ∷
   rw⁻ 3 (q97 c4) ∷
   rw 0 (q90 c4) ∷
   rw 2 (q89 c4) ∷ []) Eq.refl

private
  q98 : Ws → Eqn
  q98 c4 = sE 210 (lem-comm-TOFF013-CSd24 c4)
  q99 : Ws → Eqn
  q99 c4 = sE 323 (lem-tP-at233442 c4)

-- VPQ @233442: 14 steps
lem-VPQ-at233442 : Ws → ⟪ (ℓ "云亐亝亜") ⟫ʷ ≈ ⟪ (ℓ "亝亜云亐") ⟫ʷ
lem-VPQ-at233442 c4 = derive (ℓ "云亐亝亜") (ℓ "亝亜云亐")
  (rw⁻ 0 (q90 c4) ∷
   rw⁻ 4 (q89 c4) ∷
   rw 3 (q97 c4) ∷
   rw 2 (q98 c4) ∷
   rw 1 (q95 c4) ∷
   rw 0 (q94 c4) ∷
   rw 4 (q45 c4) ∷
   rw 3 (q99 c4) ∷
   rw⁻ 4 (q45 c4) ∷
   rw⁻ 1 (q93 c4) ∷
   rw 2 (q33 c4) ∷
   rw⁻ 3 (q91 c4) ∷
   rw 0 (q89 c4) ∷
   rw 2 (q90 c4) ∷ []) Eq.refl

private
  q100 : Ws → Eqn
  q100 c4 = wpE 502 c4
  q101 : Ws → Eqn
  q101 c4 = wlE 694 (lit c4)
  q102 : Ws → Eqn
  q102 c4 = wpE 559 c4
  q103 : Ws → Eqn
  q103 c4 = wpE 352 c4
  q104 : Ws → Eqn
  q104 c4 = wlE 490 (lit c4)
  q105 : Ws → Eqn
  q105 c4 = sE 1 (lem-comm-CX04-CCZ123 c4)
  q106 : Ws → Eqn
  q106 c4 = wlE 491 (lit c4)
  q107 : Ws → Eqn
  q107 c4 = wlE 492 (lit c4)
  q108 : Ws → Eqn
  q108 c4 = wlE 508 (lit c4)
  q109 : Ws → Eqn
  q109 c4 = wlE 695 (lit c4)
  q110 : Ws → Eqn
  q110 c4 = wpE 560 c4

-- CXbc-box @0210243143: 17 steps
lem-CXbc-box-at0210243143 : Ws → ⟪ (ℓ "亃伱亃") ⟫ʷ ≈ ⟪ (ℓ "伱亠") ⟫ʷ
lem-CXbc-box-at0210243143 c4 = derive (ℓ "亃伱亃") (ℓ "伱亠")
  (rw 1 (q50 c4) ∷
   rw 0 (q100 c4) ∷
   rw⁻ 1 (q101 c4) ∷
   rw 3 (q102 c4) ∷
   rw 2 (q100 c4) ∷
   rw 5 (q103 c4) ∷
   rw⁻ 9 (q104 c4) ∷
   rw 8 (q105 c4) ∷
   rw⁻ 7 (q106 c4) ∷
   rw 6 (q105 c4) ∷
   rw⁻ 5 (q107 c4) ∷
   rw⁻ 6 (q103 c4) ∷
   rw⁻ 4 (q108 c4) ∷
   rw⁻ 3 (q101 c4) ∷
   rw 4 (q109 c4) ∷
   rw⁻ 0 (q50 c4) ∷
   rw⁻ 1 (q110 c4) ∷ []) Eq.refl

private
  q111 : Ws → Eqn
  q111 c4 = wpE 561 c4
  q112 : Ws → Eqn
  q112 c4 = wlE 696 (lit c4)
  q113 : Ws → Eqn
  q113 c4 = wlE 424 (lit c4)
  q114 : Ws → Eqn
  q114 c4 = wlE 184 (lit c4)
  q115 : Ws → Eqn
  q115 c4 = wpE 562 c4
  q116 : Ws → Eqn
  q116 c4 = wpE 497 c4
  q117 : Ws → Eqn
  q117 c4 = sE 223 (lem-comm-CSd13-TOFF204 c4)
  q118 : Ws → Eqn
  q118 c4 = sE 218 (lem-comm-CS13-TOFF204 c4)
  q119 : Ws → Eqn
  q119 c4 = wpE 563 c4
  q120 : Ws → Eqn
  q120 c4 = wpE 564 c4
  q121 : Ws → Eqn
  q121 c4 = wpE 565 c4

-- CXcb-box @0210243143: 18 steps
lem-CXcb-box-at0210243143 : Ws → ⟪ (ℓ "乙伱乙") ⟫ʷ ≈ ⟪ (ℓ "伱亐") ⟫ʷ
lem-CXcb-box-at0210243143 c4 = derive (ℓ "乙伱乙") (ℓ "伱亐")
  (rw 1 (q50 c4) ∷
   rw 0 (q111 c4) ∷
   rw⁻ 2 (q112 c4) ∷
   rw⁻ 1 (q113 c4) ∷
   rw 4 (q114 c4) ∷
   rw 8 (q115 c4) ∷
   rw 7 (q116 c4) ∷
   rw 6 (q117 c4) ∷
   rw 5 (q116 c4) ∷
   rw 4 (q118 c4) ∷
   rw⁻ 5 (q114 c4) ∷
   rw 3 (q119 c4) ∷
   rw 2 (q111 c4) ∷
   rw 3 (q120 c4) ∷
   rw 4 (q37 c4) ∷
   rw⁻ 3 (q113 c4) ∷
   rw⁻ 0 (q50 c4) ∷
   rw⁻ 1 (q121 c4) ∷ []) Eq.refl

private
  q122 : Ws → Eqn
  q122 c4 = wlE 420 (lit c4)
  q123 : Ws → Eqn
  q123 c4 = sE 302 (lem-VPQ-at0210213443 c4)
  q124 : Ws → Eqn
  q124 c4 = wlE 305 (lit c4)

-- QVQ @0210213443: 3 steps
lem-QVQ-at0210213443 : Ws → ⟪ (ℓ "亰亏二亰") ⟫ʷ ≈ ⟪ (ℓ "亱亏二亱") ⟫ʷ
lem-QVQ-at0210213443 c4 = derive (ℓ "亰亏二亰") (ℓ "亱亏二亱")
  (rw⁻ 0 (q122 c4) ∷
   rw⁻ 1 (q123 c4) ∷
   rw 4 (q124 c4) ∷ []) Eq.refl

private
  q125 : Ws → Eqn
  q125 c4 = sE 263 (lem-box-tQ-at243243 c4)
  q126 : Ws → Eqn
  q126 c4 = wpE 572 c4
  q127 : Ws → Eqn
  q127 c4 = wpE 573 c4
  q128 : Ws → Eqn
  q128 c4 = wlE 698 (lit c4)
  q129 : Ws → Eqn
  q129 c4 = sE 4 (lem-comm-CX14-CCZ023 c4)
  q130 : Ws → Eqn
  q130 c4 = wpE 574 c4
  q131 : Ws → Eqn
  q131 c4 = wpE 575 c4
  q132 : Ws → Eqn
  q132 c4 = wpE 576 c4
  q133 : Ws → Eqn
  q133 c4 = wlE 312 (lit c4)

-- CXbc-box @243243: 17 steps
lem-CXbc-box-at243243 : Ws → ⟪ (ℓ "了仄了") ⟫ʷ ≈ ⟪ (ℓ "仄京") ⟫ʷ
lem-CXbc-box-at243243 c4 = derive (ℓ "了仄了") (ℓ "仄京")
  (rw 1 (q125 c4) ∷
   rw 0 (q77 c4) ∷
   rw⁻ 1 (q126 c4) ∷
   rw 3 (q127 c4) ∷
   rw 2 (q77 c4) ∷
   rw 5 (q128 c4) ∷
   rw⁻ 9 (q68 c4) ∷
   rw 8 (q129 c4) ∷
   rw⁻ 7 (q130 c4) ∷
   rw 6 (q129 c4) ∷
   rw⁻ 5 (q65 c4) ∷
   rw⁻ 6 (q128 c4) ∷
   rw⁻ 4 (q131 c4) ∷
   rw⁻ 3 (q126 c4) ∷
   rw 4 (q132 c4) ∷
   rw⁻ 0 (q125 c4) ∷
   rw⁻ 1 (q133 c4) ∷ []) Eq.refl

private
  q134 : Ws → Eqn
  q134 c4 = wpE 577 c4
  q135 : Ws → Eqn
  q135 c4 = wlE 699 (lit c4)
  q136 : Ws → Eqn
  q136 c4 = wpE 578 c4
  q137 : Ws → Eqn
  q137 c4 = wlE 207 (lit c4)
  q138 : Ws → Eqn
  q138 c4 = wpE 579 c4
  q139 : Ws → Eqn
  q139 c4 = wpE 580 c4
  q140 : Ws → Eqn
  q140 c4 = wpE 581 c4
  q141 : Ws → Eqn
  q141 c4 = wlE 613 (lit c4)
  q142 : Ws → Eqn
  q142 c4 = wlE 315 (lit c4)

-- CXcb-box @243243: 18 steps
lem-CXcb-box-at243243 : Ws → ⟪ (ℓ "乭仄乭") ⟫ʷ ≈ ⟪ (ℓ "仄交") ⟫ʷ
lem-CXcb-box-at243243 c4 = derive (ℓ "乭仄乭") (ℓ "仄交")
  (rw 1 (q125 c4) ∷
   rw 0 (q134 c4) ∷
   rw⁻ 2 (q135 c4) ∷
   rw⁻ 1 (q136 c4) ∷
   rw 4 (q137 c4) ∷
   rw 8 (q138 c4) ∷
   rw 7 (q61 c4) ∷
   rw 6 (q48 c4) ∷
   rw 5 (q61 c4) ∷
   rw 4 (q78 c4) ∷
   rw⁻ 5 (q137 c4) ∷
   rw 3 (q139 c4) ∷
   rw 2 (q134 c4) ∷
   rw 3 (q140 c4) ∷
   rw⁻ 4 (q141 c4) ∷
   rw⁻ 3 (q136 c4) ∷
   rw⁻ 0 (q125 c4) ∷
   rw⁻ 1 (q142 c4) ∷ []) Eq.refl

private
  q143 : Ws → Eqn
  q143 c4 = sE 315 (lem-box-tQ-at1441 c4)
  q144 : Ws → Eqn
  q144 c4 = wlE 701 (lit c4)
  q145 : Ws → Eqn
  q145 c4 = wpE 587 c4
  q146 : Ws → Eqn
  q146 c4 = wlE 702 (lit c4)
  q147 : Ws → Eqn
  q147 c4 = sE 10 (lem-comm-CX42-CCZ013 c4)
  q148 : Ws → Eqn
  q148 c4 = wlE 703 (lit c4)
  q149 : Ws → Eqn
  q149 c4 = wlE 704 (lit c4)
  q150 : Ws → Eqn
  q150 c4 = wlE 705 (lit c4)
  q151 : Ws → Eqn
  q151 c4 = wlE 257 (lit c4)

-- CXbc-box @1441: 17 steps
lem-CXbc-box-at1441 : Ws → ⟪ (ℓ "书伈书") ⟫ʷ ≈ ⟪ (ℓ "伈亨") ⟫ʷ
lem-CXbc-box-at1441 c4 = derive (ℓ "书伈书") (ℓ "伈亨")
  (rw 1 (q143 c4) ∷
   rw 0 (q32 c4) ∷
   rw⁻ 1 (q144 c4) ∷
   rw 3 (q145 c4) ∷
   rw 2 (q32 c4) ∷
   rw 5 (q146 c4) ∷
   rw⁻ 9 (q23 c4) ∷
   rw 8 (q147 c4) ∷
   rw⁻ 7 (q148 c4) ∷
   rw 6 (q147 c4) ∷
   rw⁻ 5 (q20 c4) ∷
   rw⁻ 6 (q146 c4) ∷
   rw 4 (q149 c4) ∷
   rw⁻ 3 (q144 c4) ∷
   rw 4 (q150 c4) ∷
   rw⁻ 0 (q143 c4) ∷
   rw⁻ 1 (q151 c4) ∷ []) Eq.refl

private
  q152 : Ws → Eqn
  q152 c4 = wpE 588 c4
  q153 : Ws → Eqn
  q153 c4 = wpE 589 c4
  q154 : Ws → Eqn
  q154 c4 = wlE 706 (lit c4)
  q155 : Ws → Eqn
  q155 c4 = wlE 707 (lit c4)
  q156 : Ws → Eqn
  q156 c4 = wpE 590 c4
  q157 : Ws → Eqn
  q157 c4 = wpE 591 c4
  q158 : Ws → Eqn
  q158 c4 = wpE 592 c4
  q159 : Ws → Eqn
  q159 c4 = wpE 593 c4
  q160 : Ws → Eqn
  q160 c4 = wlE 254 (lit c4)

-- CXcb-box @1441: 18 steps
lem-CXcb-box-at1441 : Ws → ⟪ (ℓ "乶伈乶") ⟫ʷ ≈ ⟪ (ℓ "伈京") ⟫ʷ
lem-CXcb-box-at1441 c4 = derive (ℓ "乶伈乶") (ℓ "伈京")
  (rw 1 (q143 c4) ∷
   rw 0 (q152 c4) ∷
   rw⁻ 2 (q153 c4) ∷
   rw⁻ 1 (q154 c4) ∷
   rw 4 (q155 c4) ∷
   rw 8 (q156 c4) ∷
   rw 7 (q16 c4) ∷
   rw 6 (q33 c4) ∷
   rw 5 (q16 c4) ∷
   rw 4 (q34 c4) ∷
   rw⁻ 5 (q155 c4) ∷
   rw⁻ 3 (q157 c4) ∷
   rw 2 (q152 c4) ∷
   rw 3 (q158 c4) ∷
   rw⁻ 4 (q159 c4) ∷
   rw⁻ 3 (q154 c4) ∷
   rw⁻ 0 (q143 c4) ∷
   rw⁻ 1 (q160 c4) ∷ []) Eq.refl

private
  q161 : Ws → Eqn
  q161 c4 = wlE 162 (lit c4)
  q162 : Ws → Eqn
  q162 c4 = sE 305 (lem-VPQ-at14233241 c4)
  q163 : Ws → Eqn
  q163 c4 = wlE 341 (lit c4)

-- QVQ @14233241: 3 steps
lem-QVQ-at14233241 : Ws → ⟪ (ℓ "二亡亠二") ⟫ʷ ≈ ⟪ (ℓ "亍亡亠亍") ⟫ʷ
lem-QVQ-at14233241 c4 = derive (ℓ "二亡亠二") (ℓ "亍亡亠亍")
  (rw⁻ 0 (q161 c4) ∷
   rw⁻ 1 (q162 c4) ∷
   rw 4 (q163 c4) ∷ []) Eq.refl

private
  q164 : Ws → Eqn
  q164 c4 = wlE 158 (lit c4)
  q165 : Ws → Eqn
  q165 c4 = wpE 5 c4
  q166 : Ws → Eqn
  q166 c4 = eqn (ℓ "下乺") (ℓ "乺下") (c₁ (S • S • S) ((CS • CS • CS) ↑ ↑))
  q167 : Ws → Eqn
  q167 c4 = eqn (ℓ "亍乺") (ℓ "乺亍") (c₃ (Toff) (CS • CS • CS))
  q168 : Ws → Eqn
  q168 c4 = eqn (ℓ "上乺") (ℓ "乺上") (c₁ (S) ((CS • CS • CS) ↑ ↑))
  q169 : Ws → Eqn
  q169 c4 = eqn (ℓ "么乺") (ℓ "乺么") (c₃ ((CS • CS • CS) ↑) (CS • CS • CS))
  q170 : Ws → Eqn
  q170 c4 = sE 320 (lem-tP-at12213443 c4)
  q171 : Ws → Eqn
  q171 c4 = eqn (ℓ "上么") (ℓ "么上") (c₁ (S) (CS • CS • CS))
  q172 : Ws → Eqn
  q172 c4 = sE 63 (lem-comm-CSd12-TOFF034 c4)
  q173 : Ws → Eqn
  q173 c4 = eqn (ℓ "下么") (ℓ "么下") (c₁ (S • S • S) (CS • CS • CS))

-- VPQ @12213443: 14 steps
lem-VPQ-at12213443 : Ws → ⟪ (ℓ "亍二亡亠") ⟫ʷ ≈ ⟪ (ℓ "亡亠亍二") ⟫ʷ
lem-VPQ-at12213443 c4 = derive (ℓ "亍二亡亠") (ℓ "亡亠亍二")
  (rw⁻ 0 (q164 c4) ∷
   rw⁻ 4 (q165 c4) ∷
   rw 3 (q166 c4) ∷
   rw 2 (q167 c4) ∷
   rw 1 (q168 c4) ∷
   rw 0 (q169 c4) ∷
   rw 4 (q45 c4) ∷
   rw 3 (q170 c4) ∷
   rw⁻ 4 (q45 c4) ∷
   rw⁻ 1 (q171 c4) ∷
   rw 2 (q172 c4) ∷
   rw⁻ 3 (q173 c4) ∷
   rw 0 (q165 c4) ∷
   rw 2 (q164 c4) ∷ []) Eq.refl

private
  q174 : Ws → Eqn
  q174 c4 = sE 311 (lem-box-tQ-at0314213042 c4)
  q175 : Ws → Eqn
  q175 c4 = wpE 662 c4
  q176 : Ws → Eqn
  q176 c4 = wlE 751 (lit c4)
  q177 : Ws → Eqn
  q177 c4 = wlE 752 (lit c4)
  q178 : Ws → Eqn
  q178 c4 = wlE 334 (lit c4)
  q179 : Ws → Eqn
  q179 c4 = wpE 513 c4
  q180 : Ws → Eqn
  q180 c4 = wlE 620 (lit c4)
  q181 : Ws → Eqn
  q181 c4 = wlE 621 (lit c4)
  q182 : Ws → Eqn
  q182 c4 = wlE 753 (lit c4)
  q183 : Ws → Eqn
  q183 c4 = wpE 663 c4

-- CXbc-box @0314213042: 17 steps
lem-CXbc-box-at0314213042 : Ws → ⟪ (ℓ "乄侂乄") ⟫ʷ ≈ ⟪ (ℓ "侂亨") ⟫ʷ
lem-CXbc-box-at0314213042 c4 = derive (ℓ "乄侂乄") (ℓ "侂亨")
  (rw 1 (q174 c4) ∷
   rw 0 (q175 c4) ∷
   rw⁻ 1 (q176 c4) ∷
   rw 3 (q177 c4) ∷
   rw 2 (q175 c4) ∷
   rw 5 (q178 c4) ∷
   rw⁻ 9 (q179 c4) ∷
   rw 8 (q66 c4) ∷
   rw⁻ 7 (q180 c4) ∷
   rw 6 (q66 c4) ∷
   rw⁻ 5 (q181 c4) ∷
   rw⁻ 6 (q178 c4) ∷
   rw⁻ 4 (q141 c4) ∷
   rw⁻ 3 (q176 c4) ∷
   rw 4 (q182 c4) ∷
   rw⁻ 0 (q174 c4) ∷
   rw⁻ 1 (q183 c4) ∷ []) Eq.refl

private
  q184 : Ws → Eqn
  q184 c4 = wpE 664 c4
  q185 : Ws → Eqn
  q185 c4 = wpE 665 c4
  q186 : Ws → Eqn
  q186 c4 = wlE 560 (lit c4)
  q187 : Ws → Eqn
  q187 c4 = wpE 496 c4
  q188 : Ws → Eqn
  q188 c4 = wlE 754 (lit c4)
  q189 : Ws → Eqn
  q189 c4 = wpE 666 c4
  q190 : Ws → Eqn
  q190 c4 = sE 287 (lem-comm-CSd02-TOFF314 c4)
  q191 : Ws → Eqn
  q191 c4 = sE 282 (lem-comm-CS02-TOFF314 c4)
  q192 : Ws → Eqn
  q192 c4 = wpE 667 c4
  q193 : Ws → Eqn
  q193 c4 = wpE 668 c4
  q194 : Ws → Eqn
  q194 c4 = wpE 669 c4
  q195 : Ws → Eqn
  q195 c4 = wpE 670 c4

-- CXcb-box @0314213042: 18 steps
lem-CXcb-box-at0314213042 : Ws → ⟪ (ℓ "丬侂丬") ⟫ʷ ≈ ⟪ (ℓ "侂亜") ⟫ʷ
lem-CXcb-box-at0314213042 c4 = derive (ℓ "丬侂丬") (ℓ "侂亜")
  (rw 1 (q174 c4) ∷
   rw 0 (q184 c4) ∷
   rw⁻ 2 (q185 c4) ∷
   rw⁻ 1 (q186 c4) ∷
   rw 4 (q187 c4) ∷
   rw 8 (q188 c4) ∷
   rw 7 (q189 c4) ∷
   rw 6 (q190 c4) ∷
   rw 5 (q189 c4) ∷
   rw 4 (q191 c4) ∷
   rw⁻ 5 (q187 c4) ∷
   rw 3 (q192 c4) ∷
   rw 2 (q184 c4) ∷
   rw 3 (q193 c4) ∷
   rw⁻ 4 (q194 c4) ∷
   rw⁻ 3 (q186 c4) ∷
   rw⁻ 0 (q174 c4) ∷
   rw⁻ 1 (q195 c4) ∷ []) Eq.refl

private
  q196 : Ws → Eqn
  q196 c4 = sE 317 (lem-tP-at0213203441 c4)

-- VPQ @0213203441: 14 steps
lem-VPQ-at0213203441 : Ws → ⟪ (ℓ "亚亘亪亨") ⟫ʷ ≈ ⟪ (ℓ "亪亨亚亘") ⟫ʷ
lem-VPQ-at0213203441 c4 = derive (ℓ "亚亘亪亨") (ℓ "亪亨亚亘")
  (rw⁻ 0 (q2 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 3 (q11 c4) ∷
   rw 2 (q12 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   rw 0 (q6 c4) ∷
   rw 4 (q7 c4) ∷
   rw 3 (q196 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q14 c4) ∷
   rw 3 (q3 c4) ∷
   rw 0 (q1 c4) ∷
   rw 2 (q2 c4) ∷ []) Eq.refl

private
  q197 : Ws → Eqn
  q197 c4 = sE 306 (lem-box-tQ-at0210233441 c4)
  q198 : Ws → Eqn
  q198 c4 = wlE 766 (lit c4)
  q199 : Ws → Eqn
  q199 c4 = wlE 767 (lit c4)
  q200 : Ws → Eqn
  q200 c4 = sE 293 (lem-comm-CZ14-TOFF203 c4)
  q201 : Ws → Eqn
  q201 c4 = wlE 768 (lit c4)

-- P-box @0210233441: 8 steps
lem-P-box-at0210233441 : Ws → ⟪ (ℓ "亪估亪") ⟫ʷ ≈ ⟪ (ℓ "估") ⟫ʷ
lem-P-box-at0210233441 c4 = derive (ℓ "亪估亪") (ℓ "估")
  (rw 1 (q197 c4) ∷
   rw⁻ 0 (q13 c4) ∷
   rw⁻ 1 (q198 c4) ∷
   rw⁻ 3 (q13 c4) ∷
   rw⁻ 4 (q199 c4) ∷
   rw 2 (q200 c4) ∷
   rw⁻ 3 (q201 c4) ∷
   rw⁻ 0 (q197 c4) ∷ []) Eq.refl

private
  q202 : Ws → Eqn
  q202 c4 = sE 310 (lem-box-tQ-at0314203142 c4)
  q203 : Ws → Eqn
  q203 c4 = wpE 688 c4
  q204 : Ws → Eqn
  q204 c4 = wlE 612 (lit c4)
  q205 : Ws → Eqn
  q205 c4 = wpE 689 c4
  q206 : Ws → Eqn
  q206 c4 = sE 20 (lem-comm-CX40-CCZ123 c4)
  q207 : Ws → Eqn
  q207 c4 = wlE 611 (lit c4)
  q208 : Ws → Eqn
  q208 c4 = wlE 171 (lit c4)
  q209 : Ws → Eqn
  q209 c4 = wlE 614 (lit c4)

-- CXbc-box @0314203142: 17 steps
lem-CXbc-box-at0314203142 : Ws → ⟪ (ℓ "丬佹丬") ⟫ʷ ≈ ⟪ (ℓ "佹亜") ⟫ʷ
lem-CXbc-box-at0314203142 c4 = derive (ℓ "丬佹丬") (ℓ "佹亜")
  (rw 1 (q202 c4) ∷
   rw 0 (q203 c4) ∷
   rw⁻ 1 (q204 c4) ∷
   rw 3 (q205 c4) ∷
   rw 2 (q203 c4) ∷
   rw 5 (q187 c4) ∷
   rw⁻ 9 (q53 c4) ∷
   rw 8 (q206 c4) ∷
   rw⁻ 7 (q207 c4) ∷
   rw 6 (q206 c4) ∷
   rw⁻ 5 (q208 c4) ∷
   rw⁻ 6 (q187 c4) ∷
   rw 4 (q141 c4) ∷
   rw⁻ 3 (q204 c4) ∷
   rw 4 (q209 c4) ∷
   rw⁻ 0 (q202 c4) ∷
   rw⁻ 1 (q195 c4) ∷ []) Eq.refl

private
  q210 : Ws → Eqn
  q210 c4 = wpE 690 c4
  q211 : Ws → Eqn
  q211 c4 = wlE 769 (lit c4)
  q212 : Ws → Eqn
  q212 c4 = wlE 616 (lit c4)
  q213 : Ws → Eqn
  q213 c4 = wpE 691 c4
  q214 : Ws → Eqn
  q214 c4 = wpE 692 c4
  q215 : Ws → Eqn
  q215 c4 = sE 222 (lem-comm-CSd12-TOFF304 c4)
  q216 : Ws → Eqn
  q216 c4 = sE 285 (lem-comm-CS12-TOFF304 c4)
  q217 : Ws → Eqn
  q217 c4 = wpE 693 c4
  q218 : Ws → Eqn
  q218 c4 = wlE 770 (lit c4)

-- CXcb-box @0314203142: 18 steps
lem-CXcb-box-at0314203142 : Ws → ⟪ (ℓ "乄佹乄") ⟫ʷ ≈ ⟪ (ℓ "佹亨") ⟫ʷ
lem-CXcb-box-at0314203142 c4 = derive (ℓ "乄佹乄") (ℓ "佹亨")
  (rw 1 (q202 c4) ∷
   rw 0 (q210 c4) ∷
   rw⁻ 2 (q211 c4) ∷
   rw⁻ 1 (q212 c4) ∷
   rw 4 (q178 c4) ∷
   rw 8 (q213 c4) ∷
   rw 7 (q214 c4) ∷
   rw 6 (q215 c4) ∷
   rw 5 (q214 c4) ∷
   rw 4 (q216 c4) ∷
   rw⁻ 5 (q178 c4) ∷
   rw⁻ 3 (q192 c4) ∷
   rw 2 (q210 c4) ∷
   rw 3 (q217 c4) ∷
   rw⁻ 4 (q218 c4) ∷
   rw⁻ 3 (q212 c4) ∷
   rw⁻ 0 (q202 c4) ∷
   rw⁻ 1 (q183 c4) ∷ []) Eq.refl

private
  q219 : Ws → Eqn
  q219 c4 = wlE 783 (lit c4)
  q220 : Ws → Eqn
  q220 c4 = wlE 784 (lit c4)
  q221 : Ws → Eqn
  q221 c4 = eqn (ℓ "丰丝") (ℓ "丝丰") (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S • S • S))
  q222 : Ws → Eqn
  q222 c4 = sE 298 (lem-comm-TOFF314-CSd02 c4)
  q223 : Ws → Eqn
  q223 c4 = eqn (ℓ "丰东") (ℓ "东丰") (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S))
  q224 : Ws → Eqn
  q224 c4 = wpE 703 c4
  q225 : Ws → Eqn
  q225 c4 = wlE 441 (lit c4)
  q226 : Ws → Eqn
  q226 c4 = sE 319 (lem-tP-at0314213042 c4)
  q227 : Ws → Eqn
  q227 c4 = wlE 785 (lit c4)
  q228 : Ws → Eqn
  q228 c4 = sE 290 (lem-comm-CSd14-TOFF302 c4)
  q229 : Ws → Eqn
  q229 c4 = wlE 786 (lit c4)

-- VPQ @0314213042: 14 steps
lem-VPQ-at0314213042 : Ws → ⟪ (ℓ "亮京些亘") ⟫ʷ ≈ ⟪ (ℓ "些亘亮京") ⟫ʷ
lem-VPQ-at0314213042 c4 = derive (ℓ "亮京些亘") (ℓ "些亘亮京")
  (rw⁻ 0 (q219 c4) ∷
   rw⁻ 4 (q220 c4) ∷
   rw⁻ 3 (q221 c4) ∷
   rw 2 (q222 c4) ∷
   rw⁻ 1 (q223 c4) ∷
   rw⁻ 0 (q224 c4) ∷
   rw 4 (q225 c4) ∷
   rw 3 (q226 c4) ∷
   rw⁻ 4 (q225 c4) ∷
   rw 1 (q227 c4) ∷
   rw 2 (q228 c4) ∷
   rw 3 (q229 c4) ∷
   rw 0 (q220 c4) ∷
   rw 2 (q219 c4) ∷ []) Eq.refl

private
  q230 : Ws → Eqn
  q230 c4 = wlE 803 (lit c4)
  q231 : Ws → Eqn
  q231 c4 = sE 294 (lem-comm-CZ14-TOFF302 c4)
  q232 : Ws → Eqn
  q232 c4 = wlE 804 (lit c4)

-- t-cP @0314213042: 5 steps
lem-t-cP-at0314213042 : Ws → ⟪ (ℓ "亮京些京些") ⟫ʷ ≈ ⟪ (ℓ "京些京些亮") ⟫ʷ
lem-t-cP-at0314213042 c4 = derive (ℓ "亮京些京些") (ℓ "京些京些亮")
  (rw⁻ 0 (q230 c4) ∷
   rw 2 (q231 c4) ∷
   rw 1 (q226 c4) ∷
   rw⁻ 2 (q232 c4) ∷
   rw 3 (q226 c4) ∷ []) Eq.refl

private
  q233 : Ws → Eqn
  q233 c4 = sE 250 (lem-box-tQ-at0214213043 c4)
  q234 : Ws → Eqn
  q234 c4 = wpE 707 c4
  q235 : Ws → Eqn
  q235 c4 = wlE 805 (lit c4)
  q236 : Ws → Eqn
  q236 c4 = wpE 505 c4

-- CXbc-box @0214213043: 17 steps
lem-CXbc-box-at0214213043 : Ws → ⟪ (ℓ "乄佝乄") ⟫ʷ ≈ ⟪ (ℓ "佝京") ⟫ʷ
lem-CXbc-box-at0214213043 c4 = derive (ℓ "乄佝乄") (ℓ "佝京")
  (rw 1 (q233 c4) ∷
   rw 0 (q234 c4) ∷
   rw⁻ 1 (q176 c4) ∷
   rw 3 (q235 c4) ∷
   rw 2 (q234 c4) ∷
   rw 5 (q64 c4) ∷
   rw⁻ 9 (q65 c4) ∷
   rw 8 (q66 c4) ∷
   rw⁻ 7 (q67 c4) ∷
   rw 6 (q66 c4) ∷
   rw⁻ 5 (q68 c4) ∷
   rw⁻ 6 (q64 c4) ∷
   rw⁻ 4 (q141 c4) ∷
   rw⁻ 3 (q176 c4) ∷
   rw 4 (q182 c4) ∷
   rw⁻ 0 (q233 c4) ∷
   rw⁻ 1 (q236 c4) ∷ []) Eq.refl

private
  q237 : Ws → Eqn
  q237 c4 = wpE 708 c4
  q238 : Ws → Eqn
  q238 c4 = wpE 709 c4
  q239 : Ws → Eqn
  q239 c4 = wpE 320 c4
  q240 : Ws → Eqn
  q240 c4 = wlE 761 (lit c4)
  q241 : Ws → Eqn
  q241 c4 = wpE 710 c4
  q242 : Ws → Eqn
  q242 c4 = sE 283 (lem-comm-CS03-TOFF214 c4)
  q243 : Ws → Eqn
  q243 c4 = wpE 503 c4
  q244 : Ws → Eqn
  q244 c4 = wpE 711 c4
  q245 : Ws → Eqn
  q245 c4 = wpE 499 c4

-- CXcb-box @0214213043: 18 steps
lem-CXcb-box-at0214213043 : Ws → ⟪ (ℓ "丬佝丬") ⟫ʷ ≈ ⟪ (ℓ "佝亠") ⟫ʷ
lem-CXcb-box-at0214213043 c4 = derive (ℓ "丬佝丬") (ℓ "佝亠")
  (rw 1 (q233 c4) ∷
   rw 0 (q237 c4) ∷
   rw⁻ 2 (q238 c4) ∷
   rw⁻ 1 (q186 c4) ∷
   rw 4 (q239 c4) ∷
   rw 8 (q240 c4) ∷
   rw 7 (q241 c4) ∷
   rw 6 (q14 c4) ∷
   rw 5 (q241 c4) ∷
   rw 4 (q242 c4) ∷
   rw⁻ 5 (q239 c4) ∷
   rw 3 (q243 c4) ∷
   rw 2 (q237 c4) ∷
   rw 3 (q244 c4) ∷
   rw⁻ 4 (q131 c4) ∷
   rw⁻ 3 (q186 c4) ∷
   rw⁻ 0 (q233 c4) ∷
   rw⁻ 1 (q245 c4) ∷ []) Eq.refl

private
  q246 : Ws → Eqn
  q246 c4 = sE 280 (lem-tP-at243243 c4)
  q247 : Ws → Eqn
  q247 c4 = wlE 825 (lit c4)
  q248 : Ws → Eqn
  q248 c4 = wlE 826 (lit c4)
  q249 : Ws → Eqn
  q249 c4 = sE 295 (lem-comm-CZ23-TOFF014 c4)
  q250 : Ws → Eqn
  q250 c4 = wlE 827 (lit c4)

-- P-box @243243: 8 steps
lem-P-box-at243243 : Ws → ⟪ (ℓ "亙仄亙") ⟫ʷ ≈ ⟪ (ℓ "仄") ⟫ʷ
lem-P-box-at243243 c4 = derive (ℓ "亙仄亙") (ℓ "仄")
  (rw 1 (q125 c4) ∷
   rw⁻ 0 (q246 c4) ∷
   rw⁻ 1 (q247 c4) ∷
   rw⁻ 3 (q246 c4) ∷
   rw⁻ 4 (q248 c4) ∷
   rw 2 (q249 c4) ∷
   rw⁻ 3 (q250 c4) ∷
   rw⁻ 0 (q125 c4) ∷ []) Eq.refl

private
  q251 : Ws → Eqn
  q251 c4 = sE 260 (lem-box-tQ-at1331 c4)
  q252 : Ws → Eqn
  q252 c4 = wlE 828 (lit c4)
  q253 : Ws → Eqn
  q253 c4 = wpE 720 c4
  q254 : Ws → Eqn
  q254 c4 = wpE 721 c4
  q255 : Ws → Eqn
  q255 c4 = wlE 829 (lit c4)
  q256 : Ws → Eqn
  q256 c4 = wpE 64 c4
  q257 : Ws → Eqn
  q257 c4 = sE 9 (lem-comm-CX32-CCZ014 c4)
  q258 : Ws → Eqn
  q258 c4 = wpE 722 c4
  q259 : Ws → Eqn
  q259 c4 = wpE 62 c4
  q260 : Ws → Eqn
  q260 c4 = wpE 38 c4
  q261 : Ws → Eqn
  q261 c4 = wpE 723 c4

-- CXbc-box @1331: 17 steps
lem-CXbc-box-at1331 : Ws → ⟪ (ℓ "也仭也") ⟫ʷ ≈ ⟪ (ℓ "仭亰") ⟫ʷ
lem-CXbc-box-at1331 c4 = derive (ℓ "也仭也") (ℓ "仭亰")
  (rw 1 (q251 c4) ∷
   rw 0 (q252 c4) ∷
   rw⁻ 1 (q253 c4) ∷
   rw 3 (q254 c4) ∷
   rw 2 (q252 c4) ∷
   rw 5 (q255 c4) ∷
   rw⁻ 9 (q256 c4) ∷
   rw 8 (q257 c4) ∷
   rw⁻ 7 (q258 c4) ∷
   rw 6 (q257 c4) ∷
   rw⁻ 5 (q259 c4) ∷
   rw⁻ 6 (q255 c4) ∷
   rw⁻ 4 (q260 c4) ∷
   rw⁻ 3 (q253 c4) ∷
   rw 4 (q261 c4) ∷
   rw⁻ 0 (q251 c4) ∷
   rw⁻ 1 (q82 c4) ∷ []) Eq.refl

private
  q262 : Ws → Eqn
  q262 c4 = wlE 830 (lit c4)
  q263 : Ws → Eqn
  q263 c4 = wpE 724 c4
  q264 : Ws → Eqn
  q264 c4 = wpE 54 c4
  q265 : Ws → Eqn
  q265 c4 = wlE 831 (lit c4)
  q266 : Ws → Eqn
  q266 c4 = wpE 725 c4
  q267 : Ws → Eqn
  q267 c4 = wlE 832 (lit c4)
  q268 : Ws → Eqn
  q268 c4 = sE 202 (lem-comm-CSd14-TOFF023 c4)
  q269 : Ws → Eqn
  q269 c4 = sE 193 (lem-comm-CS14-TOFF023 c4)
  q270 : Ws → Eqn
  q270 c4 = wlE 833 (lit c4)
  q271 : Ws → Eqn
  q271 c4 = wlE 834 (lit c4)
  q272 : Ws → Eqn
  q272 c4 = wpE 272 c4

-- CXcb-box @1331: 18 steps
lem-CXcb-box-at1331 : Ws → ⟪ (ℓ "之仭之") ⟫ʷ ≈ ⟪ (ℓ "仭京") ⟫ʷ
lem-CXcb-box-at1331 c4 = derive (ℓ "之仭之") (ℓ "仭京")
  (rw 1 (q251 c4) ∷
   rw 0 (q262 c4) ∷
   rw⁻ 2 (q263 c4) ∷
   rw⁻ 1 (q264 c4) ∷
   rw 4 (q265 c4) ∷
   rw 8 (q266 c4) ∷
   rw 7 (q267 c4) ∷
   rw 6 (q268 c4) ∷
   rw 5 (q267 c4) ∷
   rw 4 (q269 c4) ∷
   rw⁻ 5 (q265 c4) ∷
   rw 3 (q270 c4) ∷
   rw 2 (q262 c4) ∷
   rw 3 (q271 c4) ∷
   rw⁻ 4 (q272 c4) ∷
   rw⁻ 3 (q264 c4) ∷
   rw⁻ 0 (q251 c4) ∷
   rw⁻ 1 (q71 c4) ∷ []) Eq.refl

private
  q273 : Ws → Eqn
  q273 c4 = wlE 442 (lit c4)
  q274 : Ws → Eqn
  q274 c4 = sE 304 (lem-VPQ-at032032 c4)

-- QVQ @032032: 3 steps
lem-QVQ-at032032 : Ws → ⟪ (ℓ "亰亓亐亰") ⟫ʷ ≈ ⟪ (ℓ "亲亓亐亲") ⟫ʷ
lem-QVQ-at032032 c4 = derive (ℓ "亰亓亐亰") (ℓ "亲亓亐亲")
  (rw⁻ 0 (q273 c4) ∷
   rw⁻ 1 (q274 c4) ∷
   rw 4 (q124 c4) ∷ []) Eq.refl

private
  q275 : Ws → Eqn
  q275 c4 = sE 309 (lem-box-tQ-at0312243140 c4)
  q276 : Ws → Eqn
  q276 c4 = wlE 848 (lit c4)
  q277 : Ws → Eqn
  q277 c4 = wpE 182 c4
  q278 : Ws → Eqn
  q278 c4 = wpE 726 c4
  q279 : Ws → Eqn
  q279 c4 = wpE 75 c4
  q280 : Ws → Eqn
  q280 c4 = wlE 225 (lit c4)
  q281 : Ws → Eqn
  q281 c4 = wpE 76 c4
  q282 : Ws → Eqn
  q282 c4 = wpE 77 c4
  q283 : Ws → Eqn
  q283 c4 = wpE 186 c4
  q284 : Ws → Eqn
  q284 c4 = wpE 187 c4
  q285 : Ws → Eqn
  q285 c4 = wpE 727 c4

-- CXbc-box @0312243140: 17 steps
lem-CXbc-box-at0312243140 : Ws → ⟪ (ℓ "亃併亃") ⟫ʷ ≈ ⟪ (ℓ "併亜") ⟫ʷ
lem-CXbc-box-at0312243140 c4 = derive (ℓ "亃併亃") (ℓ "併亜")
  (rw 1 (q275 c4) ∷
   rw 0 (q276 c4) ∷
   rw⁻ 1 (q277 c4) ∷
   rw 3 (q278 c4) ∷
   rw 2 (q276 c4) ∷
   rw 5 (q279 c4) ∷
   rw⁻ 9 (q280 c4) ∷
   rw 8 (q21 c4) ∷
   rw⁻ 7 (q281 c4) ∷
   rw 6 (q21 c4) ∷
   rw⁻ 5 (q282 c4) ∷
   rw⁻ 6 (q279 c4) ∷
   rw⁻ 4 (q283 c4) ∷
   rw⁻ 3 (q277 c4) ∷
   rw 4 (q284 c4) ∷
   rw⁻ 0 (q275 c4) ∷
   rw⁻ 1 (q285 c4) ∷ []) Eq.refl

private
  q286 : Ws → Eqn
  q286 c4 = wlE 849 (lit c4)
  q287 : Ws → Eqn
  q287 c4 = wlE 850 (lit c4)
  q288 : Ws → Eqn
  q288 c4 = wpE 189 c4
  q289 : Ws → Eqn
  q289 c4 = wlE 270 (lit c4)
  q290 : Ws → Eqn
  q290 c4 = wpE 298 c4
  q291 : Ws → Eqn
  q291 c4 = wlE 851 (lit c4)
  q292 : Ws → Eqn
  q292 c4 = eqn (ℓ "丩亲") (ℓ "亲丩") (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI))
  q293 : Ws → Eqn
  q293 c4 = eqn (ℓ "丨亲") (ℓ "亲丨") (c₂ (CS) (K ↑ • CCZ • K ↑ • iI))
  q294 : Ws → Eqn
  q294 c4 = wlE 852 (lit c4)
  q295 : Ws → Eqn
  q295 c4 = wlE 853 (lit c4)
  q296 : Ws → Eqn
  q296 c4 = wpE 728 c4

-- CXcb-box @0312243140: 18 steps
lem-CXcb-box-at0312243140 : Ws → ⟪ (ℓ "乙併乙") ⟫ʷ ≈ ⟪ (ℓ "併二") ⟫ʷ
lem-CXcb-box-at0312243140 c4 = derive (ℓ "乙併乙") (ℓ "併二")
  (rw 1 (q275 c4) ∷
   rw 0 (q286 c4) ∷
   rw⁻ 2 (q287 c4) ∷
   rw⁻ 1 (q288 c4) ∷
   rw 4 (q289 c4) ∷
   rw 8 (q290 c4) ∷
   rw 7 (q291 c4) ∷
   rw 6 (q292 c4) ∷
   rw 5 (q291 c4) ∷
   rw 4 (q293 c4) ∷
   rw⁻ 5 (q289 c4) ∷
   rw 3 (q294 c4) ∷
   rw 2 (q286 c4) ∷
   rw 3 (q295 c4) ∷
   rw 4 (q149 c4) ∷
   rw⁻ 3 (q288 c4) ∷
   rw⁻ 0 (q275 c4) ∷
   rw⁻ 1 (q296 c4) ∷ []) Eq.refl

private
  q297 : Ws → Eqn
  q297 c4 = sE 308 (lem-box-tQ-at0312213440 c4)
  q298 : Ws → Eqn
  q298 c4 = wlE 858 (lit c4)
  q299 : Ws → Eqn
  q299 c4 = wpE 735 c4
  q300 : Ws → Eqn
  q300 c4 = wlE 859 (lit c4)
  q301 : Ws → Eqn
  q301 c4 = wpE 3 c4
  q302 : Ws → Eqn
  q302 c4 = sE 5 (lem-comm-CX21-CCZ034 c4)
  q303 : Ws → Eqn
  q303 c4 = wpE 120 c4
  q304 : Ws → Eqn
  q304 c4 = wpE 1 c4
  q305 : Ws → Eqn
  q305 c4 = wpE 736 c4

-- CXbc-box @0312213440: 17 steps
lem-CXbc-box-at0312213440 : Ws → ⟪ (ℓ "乙佳乙") ⟫ʷ ≈ ⟪ (ℓ "佳二") ⟫ʷ
lem-CXbc-box-at0312213440 c4 = derive (ℓ "乙佳乙") (ℓ "佳二")
  (rw 1 (q297 c4) ∷
   rw 0 (q298 c4) ∷
   rw⁻ 1 (q299 c4) ∷
   rw 3 (q300 c4) ∷
   rw 2 (q298 c4) ∷
   rw 5 (q289 c4) ∷
   rw⁻ 9 (q301 c4) ∷
   rw 8 (q302 c4) ∷
   rw⁻ 7 (q303 c4) ∷
   rw 6 (q302 c4) ∷
   rw⁻ 5 (q304 c4) ∷
   rw⁻ 6 (q289 c4) ∷
   rw 4 (q283 c4) ∷
   rw⁻ 3 (q299 c4) ∷
   rw 4 (q305 c4) ∷
   rw⁻ 0 (q297 c4) ∷
   rw⁻ 1 (q296 c4) ∷ []) Eq.refl

private
  q306 : Ws → Eqn
  q306 c4 = wlE 860 (lit c4)
  q307 : Ws → Eqn
  q307 c4 = wpE 737 c4
  q308 : Ws → Eqn
  q308 c4 = wpE 357 c4
  q309 : Ws → Eqn
  q309 c4 = wlE 861 (lit c4)
  q310 : Ws → Eqn
  q310 c4 = wlE 862 (lit c4)
  q311 : Ws → Eqn
  q311 c4 = sE 221 (lem-comm-CSd04-TOFF312 c4)
  q312 : Ws → Eqn
  q312 c4 = sE 217 (lem-comm-CS04-TOFF312 c4)
  q313 : Ws → Eqn
  q313 c4 = wlE 863 (lit c4)
  q314 : Ws → Eqn
  q314 c4 = wpE 109 c4

-- CXcb-box @0312213440: 18 steps
lem-CXcb-box-at0312213440 : Ws → ⟪ (ℓ "亃佳亃") ⟫ʷ ≈ ⟪ (ℓ "佳亜") ⟫ʷ
lem-CXcb-box-at0312213440 c4 = derive (ℓ "亃佳亃") (ℓ "佳亜")
  (rw 1 (q297 c4) ∷
   rw 0 (q306 c4) ∷
   rw⁻ 2 (q307 c4) ∷
   rw⁻ 1 (q308 c4) ∷
   rw 4 (q279 c4) ∷
   rw 8 (q309 c4) ∷
   rw 7 (q310 c4) ∷
   rw 6 (q311 c4) ∷
   rw 5 (q310 c4) ∷
   rw 4 (q312 c4) ∷
   rw⁻ 5 (q279 c4) ∷
   rw⁻ 3 (q294 c4) ∷
   rw 2 (q306 c4) ∷
   rw 3 (q313 c4) ∷
   rw 4 (q314 c4) ∷
   rw⁻ 3 (q308 c4) ∷
   rw⁻ 0 (q297 c4) ∷
   rw⁻ 1 (q285 c4) ∷ []) Eq.refl

private
  q315 : Ws → Eqn
  q315 c4 = sE 318 (lem-tP-at0312243140 c4)
  q316 : Ws → Eqn
  q316 c4 = wlE 866 (lit c4)
  q317 : Ws → Eqn
  q317 c4 = wlE 867 (lit c4)
  q318 : Ws → Eqn
  q318 c4 = eqn (ℓ "个亲") (ℓ "亲个") (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI))
  q319 : Ws → Eqn
  q319 c4 = wlE 868 (lit c4)

-- P-box @0312243140: 8 steps
lem-P-box-at0312243140 : Ws → ⟪ (ℓ "亓併亓") ⟫ʷ ≈ ⟪ (ℓ "併") ⟫ʷ
lem-P-box-at0312243140 c4 = derive (ℓ "亓併亓") (ℓ "併")
  (rw 1 (q275 c4) ∷
   rw⁻ 0 (q315 c4) ∷
   rw⁻ 1 (q316 c4) ∷
   rw⁻ 3 (q315 c4) ∷
   rw⁻ 4 (q317 c4) ∷
   rw 2 (q318 c4) ∷
   rw⁻ 3 (q319 c4) ∷
   rw⁻ 0 (q275 c4) ∷ []) Eq.refl

private
  q320 : Ws → Eqn
  q320 c4 = wlE 438 (lit c4)
  q321 : Ws → Eqn
  q321 c4 = wlE 437 (lit c4)
  q322 : Ws → Eqn
  q322 c4 = eqn (ℓ "丩丝") (ℓ "丝丩") (c₂ (CS • CS • CS) ((S • S • S) ↑))
  q323 : Ws → Eqn
  q323 c4 = eqn (ℓ "丩东") (ℓ "东丩") (c₂ (CS • CS • CS) (S ↑))
  q324 : Ws → Eqn
  q324 c4 = eqn (ℓ "丩乪") (ℓ "乪丩") (c₂ (CS • CS • CS) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q325 : Ws → Eqn
  q325 c4 = wlE 440 (lit c4)
  q326 : Ws → Eqn
  q326 c4 = sE 77 (lem-comm-CSd24-TOFF301 c4)
  q327 : Ws → Eqn
  q327 c4 = wlE 439 (lit c4)

-- VPQ @0312243140: 14 steps
lem-VPQ-at0312243140 : Ws → ⟪ (ℓ "亲亰亓亐") ⟫ʷ ≈ ⟪ (ℓ "亓亐亲亰") ⟫ʷ
lem-VPQ-at0312243140 c4 = derive (ℓ "亲亰亓亐") (ℓ "亓亐亲亰")
  (rw⁻ 0 (q320 c4) ∷
   rw⁻ 4 (q321 c4) ∷
   rw⁻ 3 (q322 c4) ∷
   rw⁻ 2 (q292 c4) ∷
   rw⁻ 1 (q323 c4) ∷
   rw⁻ 0 (q324 c4) ∷
   rw 4 (q225 c4) ∷
   rw 3 (q315 c4) ∷
   rw⁻ 4 (q225 c4) ∷
   rw 1 (q325 c4) ∷
   rw 2 (q326 c4) ∷
   rw 3 (q327 c4) ∷
   rw 0 (q321 c4) ∷
   rw 2 (q320 c4) ∷ []) Eq.refl

private
  q328 : Ws → Eqn
  q328 c4 = sE 258 (lem-box-tQ-at132132 c4)
  q329 : Ws → Eqn
  q329 c4 = wlE 872 (lit c4)
  q330 : Ws → Eqn
  q330 c4 = wpE 744 c4
  q331 : Ws → Eqn
  q331 c4 = wpE 745 c4
  q332 : Ws → Eqn
  q332 c4 = wpE 36 c4
  q333 : Ws → Eqn
  q333 c4 = sE 8 (lem-comm-CX31-CCZ024 c4)
  q334 : Ws → Eqn
  q334 c4 = wpE 746 c4
  q335 : Ws → Eqn
  q335 c4 = wpE 34 c4
  q336 : Ws → Eqn
  q336 c4 = wpE 747 c4

-- CXbc-box @132132: 17 steps
lem-CXbc-box-at132132 : Ws → ⟪ (ℓ "之令之") ⟫ʷ ≈ ⟪ (ℓ "令京") ⟫ʷ
lem-CXbc-box-at132132 c4 = derive (ℓ "之令之") (ℓ "令京")
  (rw 1 (q328 c4) ∷
   rw 0 (q329 c4) ∷
   rw⁻ 1 (q330 c4) ∷
   rw 3 (q331 c4) ∷
   rw 2 (q329 c4) ∷
   rw 5 (q265 c4) ∷
   rw⁻ 9 (q332 c4) ∷
   rw 8 (q333 c4) ∷
   rw⁻ 7 (q334 c4) ∷
   rw 6 (q333 c4) ∷
   rw⁻ 5 (q335 c4) ∷
   rw⁻ 6 (q265 c4) ∷
   rw 4 (q260 c4) ∷
   rw⁻ 3 (q330 c4) ∷
   rw 4 (q336 c4) ∷
   rw⁻ 0 (q328 c4) ∷
   rw⁻ 1 (q71 c4) ∷ []) Eq.refl

private
  q337 : Ws → Eqn
  q337 c4 = wlE 873 (lit c4)
  q338 : Ws → Eqn
  q338 c4 = wpE 748 c4
  q339 : Ws → Eqn
  q339 c4 = wpE 749 c4
  q340 : Ws → Eqn
  q340 c4 = wpE 95 c4
  q341 : Ws → Eqn
  q341 c4 = wlE 874 (lit c4)
  q342 : Ws → Eqn
  q342 c4 = sE 195 (lem-comm-CS24-TOFF013 c4)
  q343 : Ws → Eqn
  q343 c4 = wlE 875 (lit c4)
  q344 : Ws → Eqn
  q344 c4 = wpE 90 c4

-- CXcb-box @132132: 18 steps
lem-CXcb-box-at132132 : Ws → ⟪ (ℓ "也令也") ⟫ʷ ≈ ⟪ (ℓ "令亰") ⟫ʷ
lem-CXcb-box-at132132 c4 = derive (ℓ "也令也") (ℓ "令亰")
  (rw 1 (q328 c4) ∷
   rw 0 (q337 c4) ∷
   rw⁻ 2 (q338 c4) ∷
   rw⁻ 1 (q339 c4) ∷
   rw 4 (q255 c4) ∷
   rw 8 (q340 c4) ∷
   rw 7 (q341 c4) ∷
   rw 6 (q96 c4) ∷
   rw 5 (q341 c4) ∷
   rw 4 (q342 c4) ∷
   rw⁻ 5 (q255 c4) ∷
   rw⁻ 3 (q270 c4) ∷
   rw 2 (q337 c4) ∷
   rw 3 (q343 c4) ∷
   rw⁻ 4 (q344 c4) ∷
   rw⁻ 3 (q339 c4) ∷
   rw⁻ 0 (q328 c4) ∷
   rw⁻ 1 (q82 c4) ∷ []) Eq.refl

private
  q345 : Ws → Eqn
  q345 c4 = sE 267 (lem-tP-at0210243143 c4)
  q346 : Ws → Eqn
  q346 c4 = wlE 912 (lit c4)
  q347 : Ws → Eqn
  q347 c4 = wlE 913 (lit c4)
  q348 : Ws → Eqn
  q348 c4 = sE 292 (lem-comm-CZ13-TOFF204 c4)
  q349 : Ws → Eqn
  q349 c4 = wlE 914 (lit c4)

-- P-box @0210243143: 8 steps
lem-P-box-at0210243143 : Ws → ⟪ (ℓ "亦伱亦") ⟫ʷ ≈ ⟪ (ℓ "伱") ⟫ʷ
lem-P-box-at0210243143 c4 = derive (ℓ "亦伱亦") (ℓ "伱")
  (rw 1 (q50 c4) ∷
   rw⁻ 0 (q345 c4) ∷
   rw⁻ 1 (q346 c4) ∷
   rw⁻ 3 (q345 c4) ∷
   rw⁻ 4 (q347 c4) ∷
   rw 2 (q348 c4) ∷
   rw⁻ 3 (q349 c4) ∷
   rw⁻ 0 (q50 c4) ∷ []) Eq.refl

private
  q350 : Ws → Eqn
  q350 c4 = sE 307 (lem-box-tQ-at022330 c4)
  q351 : Ws → Eqn
  q351 c4 = wlE 917 (lit c4)
  q352 : Ws → Eqn
  q352 c4 = wpE 757 c4
  q353 : Ws → Eqn
  q353 c4 = wlE 918 (lit c4)
  q354 : Ws → Eqn
  q354 c4 = wlE 166 (lit c4)
  q355 : Ws → Eqn
  q355 c4 = sE 3 (lem-comm-CX13-CCZ024 c4)
  q356 : Ws → Eqn
  q356 c4 = wpE 35 c4
  q357 : Ws → Eqn
  q357 c4 = wpE 758 c4
  q358 : Ws → Eqn
  q358 c4 = wpE 759 c4

-- CXbc-box @022330: 17 steps
lem-CXbc-box-at022330 : Ws → ⟪ (ℓ "买伴买") ⟫ʷ ≈ ⟪ (ℓ "伴京") ⟫ʷ
lem-CXbc-box-at022330 c4 = derive (ℓ "买伴买") (ℓ "伴京")
  (rw 1 (q350 c4) ∷
   rw 0 (q351 c4) ∷
   rw⁻ 1 (q352 c4) ∷
   rw 3 (q353 c4) ∷
   rw 2 (q351 c4) ∷
   rw 5 (q354 c4) ∷
   rw⁻ 9 (q335 c4) ∷
   rw 8 (q355 c4) ∷
   rw⁻ 7 (q356 c4) ∷
   rw 6 (q355 c4) ∷
   rw⁻ 5 (q332 c4) ∷
   rw⁻ 6 (q354 c4) ∷
   rw⁻ 4 (q344 c4) ∷
   rw⁻ 3 (q352 c4) ∷
   rw 4 (q357 c4) ∷
   rw⁻ 0 (q350 c4) ∷
   rw⁻ 1 (q358 c4) ∷ []) Eq.refl

private
  q359 : Ws → Eqn
  q359 c4 = wlE 919 (lit c4)
  q360 : Ws → Eqn
  q360 c4 = wpE 760 c4
  q361 : Ws → Eqn
  q361 c4 = wpE 756 c4
  q362 : Ws → Eqn
  q362 c4 = wpE 341 c4
  q363 : Ws → Eqn
  q363 c4 = wlE 195 (lit c4)
  q364 : Ws → Eqn
  q364 c4 = wlE 920 (lit c4)
  q365 : Ws → Eqn
  q365 c4 = sE 198 (lem-comm-CSd04-TOFF213 c4)
  q366 : Ws → Eqn
  q366 c4 = sE 284 (lem-comm-CS04-TOFF213 c4)
  q367 : Ws → Eqn
  q367 c4 = wlE 921 (lit c4)
  q368 : Ws → Eqn
  q368 c4 = wlE 922 (lit c4)
  q369 : Ws → Eqn
  q369 c4 = wpE 761 c4

-- CXcb-box @022330: 18 steps
lem-CXcb-box-at022330 : Ws → ⟪ (ℓ "为伴为") ⟫ʷ ≈ ⟪ (ℓ "伴五") ⟫ʷ
lem-CXcb-box-at022330 c4 = derive (ℓ "为伴为") (ℓ "伴五")
  (rw 1 (q350 c4) ∷
   rw 0 (q359 c4) ∷
   rw⁻ 2 (q360 c4) ∷
   rw⁻ 1 (q361 c4) ∷
   rw 4 (q362 c4) ∷
   rw 8 (q363 c4) ∷
   rw 7 (q364 c4) ∷
   rw 6 (q365 c4) ∷
   rw 5 (q364 c4) ∷
   rw 4 (q366 c4) ∷
   rw⁻ 5 (q362 c4) ∷
   rw 3 (q367 c4) ∷
   rw 2 (q359 c4) ∷
   rw 3 (q368 c4) ∷
   rw 4 (q260 c4) ∷
   rw⁻ 3 (q361 c4) ∷
   rw⁻ 0 (q350 c4) ∷
   rw⁻ 1 (q369 c4) ∷ []) Eq.refl

private
  q370 : Ws → Eqn
  q370 c4 = sE 303 (lem-VPQ-at0220 c4)

-- QVQ @0220: 3 steps
lem-QVQ-at0220 : Ws → ⟪ (ℓ "亰亏二亰") ⟫ʷ ≈ ⟪ (ℓ "亱亏二亱") ⟫ʷ
lem-QVQ-at0220 c4 = derive (ℓ "亰亏二亰") (ℓ "亱亏二亱")
  (rw⁻ 0 (q122 c4) ∷
   rw⁻ 1 (q370 c4) ∷
   rw 4 (q124 c4) ∷ []) Eq.refl

private
  q371 : Ws → Eqn
  q371 c4 = wlE 300 (lit c4)
  q372 : Ws → Eqn
  q372 c4 = sE 300 (lem-CXbc-box-at0213243140 c4)
  q373 : Ws → Eqn
  q373 c4 = wpE 566 c4
  q374 : Ws → Eqn
  q374 c4 = sE 301 (lem-CXcb-box-at0213243140 c4)
  q375 : Ws → Eqn
  q375 c4 = wpE 567 c4
  q376 : Ws → Eqn
  q376 c4 = wpE 568 c4
  q377 : Ws → Eqn
  q377 c4 = wpE 7 c4

-- SWbc-box @0213243140: 11 steps
lem-SWbc-box-at0213243140 : Ws → ⟪ (ℓ "乘低乘") ⟫ʷ ≈ ⟪ (ℓ "低") ⟫ʷ
lem-SWbc-box-at0213243140 c4 = derive (ℓ "乘低乘") (ℓ "低")
  (rw⁻ 0 (q371 c4) ∷
   rw⁻ 4 (q371 c4) ∷
   rw 2 (q372 c4) ∷
   rw 3 (q373 c4) ∷
   rw 1 (q374 c4) ∷
   rw 4 (q308 c4) ∷
   rw 3 (q375 c4) ∷
   rw 2 (q375 c4) ∷
   rw 3 (q376 c4) ∷
   rw 0 (q372 c4) ∷
   rw 1 (q377 c4) ∷ []) Eq.refl

private
  q378 : Ws → Eqn
  q378 c4 = sE 329 (lem-box-tQ-at0213213440 c4)
  q379 : Ws → Eqn
  q379 c4 = wlE 944 (lit c4)
  q380 : Ws → Eqn
  q380 c4 = wpE 282 c4
  q381 : Ws → Eqn
  q381 c4 = wlE 945 (lit c4)
  q382 : Ws → Eqn
  q382 c4 = wlE 323 (lit c4)
  q383 : Ws → Eqn
  q383 c4 = wpE 21 c4
  q384 : Ws → Eqn
  q384 c4 = wpE 179 c4
  q385 : Ws → Eqn
  q385 c4 = wpE 39 c4
  q386 : Ws → Eqn
  q386 c4 = wpE 142 c4
  q387 : Ws → Eqn
  q387 c4 = wpE 283 c4

-- CXbc-box @0213213440: 17 steps
lem-CXbc-box-at0213213440 : Ws → ⟪ (ℓ "乙佈乙") ⟫ʷ ≈ ⟪ (ℓ "佈亐") ⟫ʷ
lem-CXbc-box-at0213213440 c4 = derive (ℓ "乙佈乙") (ℓ "佈亐")
  (rw 1 (q378 c4) ∷
   rw 0 (q379 c4) ∷
   rw⁻ 1 (q380 c4) ∷
   rw 3 (q381 c4) ∷
   rw 2 (q379 c4) ∷
   rw 5 (q382 c4) ∷
   rw⁻ 9 (q383 c4) ∷
   rw 8 (q333 c4) ∷
   rw⁻ 7 (q384 c4) ∷
   rw 6 (q333 c4) ∷
   rw⁻ 5 (q385 c4) ∷
   rw⁻ 6 (q382 c4) ∷
   rw 4 (q386 c4) ∷
   rw⁻ 3 (q380 c4) ∷
   rw 4 (q387 c4) ∷
   rw⁻ 0 (q378 c4) ∷
   rw⁻ 1 (q121 c4) ∷ []) Eq.refl

private
  q388 : Ws → Eqn
  q388 c4 = wlE 946 (lit c4)
  q389 : Ws → Eqn
  q389 c4 = wpE 768 c4
  q390 : Ws → Eqn
  q390 c4 = wpE 285 c4
  q391 : Ws → Eqn
  q391 c4 = wpE 115 c4
  q392 : Ws → Eqn
  q392 c4 = wlE 196 (lit c4)
  q393 : Ws → Eqn
  q393 c4 = wlE 947 (lit c4)
  q394 : Ws → Eqn
  q394 c4 = wlE 942 (lit c4)
  q395 : Ws → Eqn
  q395 c4 = wlE 948 (lit c4)

-- CXcb-box @0213213440: 18 steps
lem-CXcb-box-at0213213440 : Ws → ⟪ (ℓ "亃佈亃") ⟫ʷ ≈ ⟪ (ℓ "佈亠") ⟫ʷ
lem-CXcb-box-at0213213440 c4 = derive (ℓ "亃佈亃") (ℓ "佈亠")
  (rw 1 (q378 c4) ∷
   rw 0 (q388 c4) ∷
   rw⁻ 2 (q389 c4) ∷
   rw⁻ 1 (q390 c4) ∷
   rw 4 (q391 c4) ∷
   rw 8 (q392 c4) ∷
   rw 7 (q393 c4) ∷
   rw 6 (q365 c4) ∷
   rw 5 (q393 c4) ∷
   rw 4 (q366 c4) ∷
   rw⁻ 5 (q391 c4) ∷
   rw⁻ 3 (q394 c4) ∷
   rw 2 (q388 c4) ∷
   rw 3 (q395 c4) ∷
   rw⁻ 4 (q314 c4) ∷
   rw⁻ 3 (q390 c4) ∷
   rw⁻ 0 (q378 c4) ∷
   rw⁻ 1 (q110 c4) ∷ []) Eq.refl

private
  q396 : Ws → Eqn
  q396 c4 = wlE 421 (lit c4)
  q397 : Ws → Eqn
  q397 c4 = sE 328 (lem-VPQ-at0213243140 c4)

-- QVQ @0213243140: 3 steps
lem-QVQ-at0213243140 : Ws → ⟪ (ℓ "二亱亰二") ⟫ʷ ≈ ⟪ (ℓ "亏亱亰亏") ⟫ʷ
lem-QVQ-at0213243140 c4 = derive (ℓ "二亱亰二") (ℓ "亏亱亰亏")
  (rw⁻ 0 (q396 c4) ∷
   rw⁻ 1 (q397 c4) ∷
   rw 4 (q163 c4) ∷ []) Eq.refl

private
  q398 : Ws → Eqn
  q398 c4 = wlE 961 (lit c4)
  q399 : Ws → Eqn
  q399 c4 = sE 324 (lem-CXbc-box-at0220 c4)
  q400 : Ws → Eqn
  q400 c4 = wpE 763 c4
  q401 : Ws → Eqn
  q401 c4 = sE 326 (lem-CXcb-box-at0220 c4)
  q402 : Ws → Eqn
  q402 c4 = wpE 778 c4
  q403 : Ws → Eqn
  q403 c4 = wpE 762 c4
  q404 : Ws → Eqn
  q404 c4 = wpE 779 c4
  q405 : Ws → Eqn
  q405 c4 = wpE 161 c4

-- SWbc-box @0220: 11 steps
lem-SWbc-box-at0220 : Ws → ⟪ (ℓ "丹伳丹") ⟫ʷ ≈ ⟪ (ℓ "伳") ⟫ʷ
lem-SWbc-box-at0220 c4 = derive (ℓ "丹伳丹") (ℓ "伳")
  (rw⁻ 0 (q398 c4) ∷
   rw⁻ 4 (q398 c4) ∷
   rw 2 (q399 c4) ∷
   rw 3 (q400 c4) ∷
   rw 1 (q401 c4) ∷
   rw 4 (q402 c4) ∷
   rw 3 (q403 c4) ∷
   rw 2 (q403 c4) ∷
   rw 3 (q404 c4) ∷
   rw 0 (q399 c4) ∷
   rw 1 (q405 c4) ∷ []) Eq.refl

private
  q406 : Ws → Eqn
  q406 c4 = sE 333 (lem-tP-at022330 c4)
  q407 : Ws → Eqn
  q407 c4 = wpE 780 c4
  q408 : Ws → Eqn
  q408 c4 = wpE 781 c4
  q409 : Ws → Eqn
  q409 c4 = sE 206 (lem-comm-CZ04-TOFF213 c4)
  q410 : Ws → Eqn
  q410 c4 = wpE 782 c4

-- P-box @022330: 8 steps
lem-P-box-at022330 : Ws → ⟪ (ℓ "亞伴亞") ⟫ʷ ≈ ⟪ (ℓ "伴") ⟫ʷ
lem-P-box-at022330 c4 = derive (ℓ "亞伴亞") (ℓ "伴")
  (rw 1 (q350 c4) ∷
   rw⁻ 0 (q406 c4) ∷
   rw⁻ 1 (q407 c4) ∷
   rw⁻ 3 (q406 c4) ∷
   rw⁻ 4 (q408 c4) ∷
   rw 2 (q409 c4) ∷
   rw⁻ 3 (q410 c4) ∷
   rw⁻ 0 (q350 c4) ∷ []) Eq.refl

private
  q411 : Ws → Eqn
  q411 c4 = wlE 176 (lit c4)
  q412 : Ws → Eqn
  q412 c4 = wpE 15 c4
  q413 : Ws → Eqn
  q413 c4 = wpE 18 c4
  q414 : Ws → Eqn
  q414 c4 = sE 296 (lem-comm-TOFF213-CSd04 c4)
  q415 : Ws → Eqn
  q415 c4 = wpE 17 c4
  q416 : Ws → Eqn
  q416 c4 = wpE 16 c4
  q417 : Ws → Eqn
  q417 c4 = wlE 178 (lit c4)
  q418 : Ws → Eqn
  q418 c4 = wlE 177 (lit c4)

-- VPQ @022330: 14 steps
lem-VPQ-at022330 : Ws → ⟪ (ℓ "亦交亞亜") ⟫ʷ ≈ ⟪ (ℓ "亞亜亦交") ⟫ʷ
lem-VPQ-at022330 c4 = derive (ℓ "亦交亞亜") (ℓ "亞亜亦交")
  (rw⁻ 0 (q411 c4) ∷
   rw⁻ 4 (q412 c4) ∷
   rw⁻ 3 (q413 c4) ∷
   rw 2 (q414 c4) ∷
   rw⁻ 1 (q415 c4) ∷
   rw⁻ 0 (q416 c4) ∷
   rw 4 (q7 c4) ∷
   rw 3 (q406 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw 1 (q417 c4) ∷
   rw 2 (q117 c4) ∷
   rw 3 (q418 c4) ∷
   rw 0 (q412 c4) ∷
   rw 2 (q411 c4) ∷ []) Eq.refl

private
  q419 : Ws → Eqn
  q419 c4 = sE 255 (lem-box-tQ-at122331 c4)
  q420 : Ws → Eqn
  q420 c4 = wpE 792 c4
  q421 : Ws → Eqn
  q421 c4 = wpE 793 c4
  q422 : Ws → Eqn
  q422 c4 = wlE 274 (lit c4)
  q423 : Ws → Eqn
  q423 c4 = sE 6 (lem-comm-CX23-CCZ014 c4)
  q424 : Ws → Eqn
  q424 c4 = wpE 63 c4
  q425 : Ws → Eqn
  q425 c4 = wpE 124 c4
  q426 : Ws → Eqn
  q426 c4 = wpE 794 c4
  q427 : Ws → Eqn
  q427 c4 = wlE 277 (lit c4)

-- CXbc-box @122331: 17 steps
lem-CXbc-box-at122331 : Ws → ⟪ (ℓ "乳仕乳") ⟫ʷ ≈ ⟪ (ℓ "仕亰") ⟫ʷ
lem-CXbc-box-at122331 c4 = derive (ℓ "乳仕乳") (ℓ "仕亰")
  (rw 1 (q419 c4) ∷
   rw 0 (q267 c4) ∷
   rw⁻ 1 (q420 c4) ∷
   rw 3 (q421 c4) ∷
   rw 2 (q267 c4) ∷
   rw 5 (q422 c4) ∷
   rw⁻ 9 (q259 c4) ∷
   rw 8 (q423 c4) ∷
   rw⁻ 7 (q424 c4) ∷
   rw 6 (q423 c4) ∷
   rw⁻ 5 (q256 c4) ∷
   rw⁻ 6 (q422 c4) ∷
   rw⁻ 4 (q425 c4) ∷
   rw⁻ 3 (q420 c4) ∷
   rw 4 (q426 c4) ∷
   rw⁻ 0 (q419 c4) ∷
   rw⁻ 1 (q427 c4) ∷ []) Eq.refl

private
  q428 : Ws → Eqn
  q428 c4 = wlE 987 (lit c4)
  q429 : Ws → Eqn
  q429 c4 = wpE 310 c4
  q430 : Ws → Eqn
  q430 c4 = wpE 795 c4
  q431 : Ws → Eqn
  q431 c4 = wlE 271 (lit c4)
  q432 : Ws → Eqn
  q432 c4 = wpE 70 c4
  q433 : Ws → Eqn
  q433 c4 = wlE 275 (lit c4)
  q434 : Ws → Eqn
  q434 c4 = wlE 988 (lit c4)
  q435 : Ws → Eqn
  q435 c4 = wpE 66 c4
  q436 : Ws → Eqn
  q436 c4 = wlE 272 (lit c4)

-- CXcb-box @122331: 18 steps
lem-CXcb-box-at122331 : Ws → ⟪ (ℓ "乒仕乒") ⟫ʷ ≈ ⟪ (ℓ "仕亨") ⟫ʷ
lem-CXcb-box-at122331 c4 = derive (ℓ "乒仕乒") (ℓ "仕亨")
  (rw 1 (q419 c4) ∷
   rw 0 (q428 c4) ∷
   rw⁻ 2 (q429 c4) ∷
   rw⁻ 1 (q430 c4) ∷
   rw 4 (q431 c4) ∷
   rw 8 (q432 c4) ∷
   rw 7 (q252 c4) ∷
   rw 6 (q268 c4) ∷
   rw 5 (q252 c4) ∷
   rw 4 (q269 c4) ∷
   rw⁻ 5 (q431 c4) ∷
   rw 3 (q433 c4) ∷
   rw 2 (q428 c4) ∷
   rw 3 (q434 c4) ∷
   rw⁻ 4 (q435 c4) ∷
   rw⁻ 3 (q430 c4) ∷
   rw⁻ 0 (q419 c4) ∷
   rw⁻ 1 (q436 c4) ∷ []) Eq.refl

private
  q437 : Ws → Eqn
  q437 c4 = sE 335 (lem-tP-at14213243 c4)

-- P-box @14213243: 8 steps
lem-P-box-at14213243 : Ws → ⟪ (ℓ "亙仼亙") ⟫ʷ ≈ ⟪ (ℓ "仼") ⟫ʷ
lem-P-box-at14213243 c4 = derive (ℓ "亙仼亙") (ℓ "仼")
  (rw 1 (q60 c4) ∷
   rw⁻ 0 (q437 c4) ∷
   rw⁻ 1 (q247 c4) ∷
   rw⁻ 3 (q437 c4) ∷
   rw⁻ 4 (q248 c4) ∷
   rw 2 (q249 c4) ∷
   rw⁻ 3 (q250 c4) ∷
   rw⁻ 0 (q60 c4) ∷ []) Eq.refl

private
  q438 : Ws → Eqn
  q438 c4 = sE 211 (lem-comm-TOFF014-CSd23 c4)

-- VPQ @14213243: 14 steps
lem-VPQ-at14213243 : Ws → ⟪ (ℓ "井五亙亘") ⟫ʷ ≈ ⟪ (ℓ "亙亘井五") ⟫ʷ
lem-VPQ-at14213243 c4 = derive (ℓ "井五亙亘") (ℓ "亙亘井五")
  (rw⁻ 0 (q40 c4) ∷
   rw⁻ 4 (q39 c4) ∷
   rw 3 (q49 c4) ∷
   rw 2 (q438 c4) ∷
   rw 1 (q47 c4) ∷
   rw 0 (q44 c4) ∷
   rw 4 (q45 c4) ∷
   rw 3 (q437 c4) ∷
   rw⁻ 4 (q45 c4) ∷
   rw⁻ 1 (q43 c4) ∷
   rw 2 (q268 c4) ∷
   rw⁻ 3 (q41 c4) ∷
   rw 0 (q39 c4) ∷
   rw 2 (q40 c4) ∷ []) Eq.refl

private
  q439 : Ws → Eqn
  q439 c4 = sE 312 (lem-box-tQ-at12233441 c4)
  q440 : Ws → Eqn
  q440 c4 = wpE 270 c4
  q441 : Ws → Eqn
  q441 c4 = wpE 807 c4
  q442 : Ws → Eqn
  q442 c4 = wlE 1007 (lit c4)
  q443 : Ws → Eqn
  q443 c4 = wpE 67 c4
  q444 : Ws → Eqn
  q444 c4 = wpE 60 c4
  q445 : Ws → Eqn
  q445 c4 = wpE 53 c4
  q446 : Ws → Eqn
  q446 c4 = wpE 808 c4

-- CXbc-box @12233441: 17 steps
lem-CXbc-box-at12233441 : Ws → ⟪ (ℓ "乽付乽") ⟫ʷ ≈ ⟪ (ℓ "付交") ⟫ʷ
lem-CXbc-box-at12233441 c4 = derive (ℓ "乽付乽") (ℓ "付交")
  (rw 1 (q439 c4) ∷
   rw 0 (q440 c4) ∷
   rw⁻ 1 (q441 c4) ∷
   rw 3 (q442 c4) ∷
   rw 2 (q440 c4) ∷
   rw 5 (q30 c4) ∷
   rw⁻ 9 (q443 c4) ∷
   rw 8 (q423 c4) ∷
   rw⁻ 7 (q444 c4) ∷
   rw 6 (q423 c4) ∷
   rw⁻ 5 (q445 c4) ∷
   rw⁻ 6 (q30 c4) ∷
   rw 4 (q24 c4) ∷
   rw⁻ 3 (q441 c4) ∷
   rw 4 (q446 c4) ∷
   rw⁻ 0 (q439 c4) ∷
   rw⁻ 1 (q38 c4) ∷ []) Eq.refl

private
  q447 : Ws → Eqn
  q447 c4 = wpE 809 c4
  q448 : Ws → Eqn
  q448 c4 = wpE 71 c4
  q449 : Ws → Eqn
  q449 c4 = wpE 810 c4
  q450 : Ws → Eqn
  q450 c4 = wlE 221 (lit c4)
  q451 : Ws → Eqn
  q451 c4 = wpE 263 c4
  q452 : Ws → Eqn
  q452 c4 = wpE 811 c4

-- CXcb-box @12233441: 18 steps
lem-CXcb-box-at12233441 : Ws → ⟪ (ℓ "争付争") ⟫ʷ ≈ ⟪ (ℓ "付亨") ⟫ʷ
lem-CXcb-box-at12233441 c4 = derive (ℓ "争付争") (ℓ "付亨")
  (rw 1 (q439 c4) ∷
   rw 0 (q447 c4) ∷
   rw⁻ 2 (q448 c4) ∷
   rw⁻ 1 (q449 c4) ∷
   rw 4 (q19 c4) ∷
   rw 8 (q450 c4) ∷
   rw 7 (q451 c4) ∷
   rw 6 (q268 c4) ∷
   rw 5 (q451 c4) ∷
   rw 4 (q269 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw⁻ 3 (q35 c4) ∷
   rw 2 (q447 c4) ∷
   rw 3 (q452 c4) ∷
   rw⁻ 4 (q435 c4) ∷
   rw⁻ 3 (q449 c4) ∷
   rw⁻ 0 (q439 c4) ∷
   rw⁻ 1 (q26 c4) ∷ []) Eq.refl

private
  q453 : Ws → Eqn
  q453 c4 = wpE 158 c4
  q454 : Ws → Eqn
  q454 c4 = wpE 159 c4
  q455 : Ws → Eqn
  q455 c4 = sE 208 (lem-comm-CZ14-TOFF023 c4)
  q456 : Ws → Eqn
  q456 c4 = wpE 160 c4

-- P-box @12233441: 8 steps
lem-P-box-at12233441 : Ws → ⟪ (ℓ "井付井") ⟫ʷ ≈ ⟪ (ℓ "付") ⟫ʷ
lem-P-box-at12233441 c4 = derive (ℓ "井付井") (ℓ "付")
  (rw 1 (q439 c4) ∷
   rw⁻ 0 (q46 c4) ∷
   rw⁻ 1 (q453 c4) ∷
   rw⁻ 3 (q46 c4) ∷
   rw⁻ 4 (q454 c4) ∷
   rw 2 (q455 c4) ∷
   rw⁻ 3 (q456 c4) ∷
   rw⁻ 0 (q439 c4) ∷ []) Eq.refl

private
  q457 : Ws → Eqn
  q457 c4 = sE 275 (lem-tP-at122441 c4)

-- P-box @122441: 8 steps
lem-P-box-at122441 : Ws → ⟪ (ℓ "云仞云") ⟫ʷ ≈ ⟪ (ℓ "仞") ⟫ʷ
lem-P-box-at122441 c4 = derive (ℓ "云仞云") (ℓ "仞")
  (rw 1 (q15 c4) ∷
   rw⁻ 0 (q457 c4) ∷
   rw⁻ 1 (q85 c4) ∷
   rw⁻ 3 (q457 c4) ∷
   rw⁻ 4 (q86 c4) ∷
   rw 2 (q87 c4) ∷
   rw⁻ 3 (q88 c4) ∷
   rw⁻ 0 (q15 c4) ∷ []) Eq.refl

private
  q458 : Ws → Eqn
  q458 c4 = sE 262 (lem-box-tQ-at2332 c4)
  q459 : Ws → Eqn
  q459 c4 = wpE 717 c4
  q460 : Ws → Eqn
  q460 c4 = wpE 825 c4
  q461 : Ws → Eqn
  q461 c4 = wpE 718 c4

-- CXbc-box @2332: 17 steps
lem-CXbc-box-at2332 : Ws → ⟪ (ℓ "乶亾乶") ⟫ʷ ≈ ⟪ (ℓ "亾京") ⟫ʷ
lem-CXbc-box-at2332 c4 = derive (ℓ "乶亾乶") (ℓ "亾京")
  (rw 1 (q458 c4) ∷
   rw 0 (q341 c4) ∷
   rw⁻ 1 (q459 c4) ∷
   rw 3 (q460 c4) ∷
   rw 2 (q341 c4) ∷
   rw 5 (q354 c4) ∷
   rw⁻ 9 (q335 c4) ∷
   rw 8 (q355 c4) ∷
   rw⁻ 7 (q356 c4) ∷
   rw 6 (q355 c4) ∷
   rw⁻ 5 (q332 c4) ∷
   rw⁻ 6 (q354 c4) ∷
   rw⁻ 4 (q314 c4) ∷
   rw⁻ 3 (q459 c4) ∷
   rw 4 (q461 c4) ∷
   rw⁻ 0 (q458 c4) ∷
   rw⁻ 1 (q160 c4) ∷ []) Eq.refl

private
  q462 : Ws → Eqn
  q462 c4 = wlE 1018 (lit c4)
  q463 : Ws → Eqn
  q463 c4 = wpE 826 c4
  q464 : Ws → Eqn
  q464 c4 = wpE 82 c4
  q465 : Ws → Eqn
  q465 c4 = wlE 256 (lit c4)
  q466 : Ws → Eqn
  q466 c4 = wpE 785 c4
  q467 : Ws → Eqn
  q467 c4 = wlE 252 (lit c4)
  q468 : Ws → Eqn
  q468 c4 = wlE 1019 (lit c4)
  q469 : Ws → Eqn
  q469 c4 = wpE 827 c4

-- CXcb-box @2332: 18 steps
lem-CXcb-box-at2332 : Ws → ⟪ (ℓ "书亾书") ⟫ʷ ≈ ⟪ (ℓ "亾亨") ⟫ʷ
lem-CXcb-box-at2332 c4 = derive (ℓ "书亾书") (ℓ "亾亨")
  (rw 1 (q458 c4) ∷
   rw 0 (q462 c4) ∷
   rw⁻ 2 (q463 c4) ∷
   rw⁻ 1 (q464 c4) ∷
   rw 4 (q465 c4) ∷
   rw 8 (q466 c4) ∷
   rw 7 (q329 c4) ∷
   rw 6 (q96 c4) ∷
   rw 5 (q329 c4) ∷
   rw 4 (q342 c4) ∷
   rw⁻ 5 (q465 c4) ∷
   rw 3 (q467 c4) ∷
   rw 2 (q462 c4) ∷
   rw 3 (q468 c4) ∷
   rw⁻ 4 (q469 c4) ∷
   rw⁻ 3 (q464 c4) ∷
   rw⁻ 0 (q458 c4) ∷
   rw⁻ 1 (q151 c4) ∷ []) Eq.refl

private
  q470 : Ws → Eqn
  q470 c4 = wlE 677 (lit c4)
  q471 : Ws → Eqn
  q471 c4 = sE 325 (lem-CXbc-box-at03102132 c4)
  q472 : Ws → Eqn
  q472 c4 = wpE 899 c4
  q473 : Ws → Eqn
  q473 c4 = sE 327 (lem-CXcb-box-at03102132 c4)
  q474 : Ws → Eqn
  q474 c4 = wpE 653 c4
  q475 : Ws → Eqn
  q475 c4 = wpE 900 c4

-- SWbc-box @03102132: 11 steps
lem-SWbc-box-at03102132 : Ws → ⟪ (ℓ "乊佤乊") ⟫ʷ ≈ ⟪ (ℓ "佤") ⟫ʷ
lem-SWbc-box-at03102132 c4 = derive (ℓ "乊佤乊") (ℓ "佤")
  (rw⁻ 0 (q470 c4) ∷
   rw⁻ 4 (q470 c4) ∷
   rw 2 (q471 c4) ∷
   rw 3 (q472 c4) ∷
   rw 1 (q473 c4) ∷
   rw 4 (q264 c4) ∷
   rw 3 (q474 c4) ∷
   rw 2 (q474 c4) ∷
   rw 3 (q475 c4) ∷
   rw 0 (q471 c4) ∷
   rw 1 (q405 c4) ∷ []) Eq.refl

private
  q476 : Ws → Eqn
  q476 c4 = sE 249 (lem-box-tQ-at0214203143 c4)
  q477 : Ws → Eqn
  q477 c4 = sE 332 (lem-tP-at0214203143 c4)

-- P-box @0214203143: 8 steps
lem-P-box-at0214203143 : Ws → ⟪ (ℓ "亦佔亦") ⟫ʷ ≈ ⟪ (ℓ "佔") ⟫ʷ
lem-P-box-at0214203143 c4 = derive (ℓ "亦佔亦") (ℓ "佔")
  (rw 1 (q476 c4) ∷
   rw⁻ 0 (q477 c4) ∷
   rw⁻ 1 (q346 c4) ∷
   rw⁻ 3 (q477 c4) ∷
   rw⁻ 4 (q347 c4) ∷
   rw 2 (q348 c4) ∷
   rw⁻ 3 (q349 c4) ∷
   rw⁻ 0 (q476 c4) ∷ []) Eq.refl

private
  q478 : Ws → Eqn
  q478 c4 = sE 213 (lem-comm-TOFF204-CSd13 c4)

-- VPQ @0214203143: 14 steps
lem-VPQ-at0214203143 : Ws → ⟪ (ℓ "亞亜亦交") ⟫ʷ ≈ ⟪ (ℓ "亦交亞亜") ⟫ʷ
lem-VPQ-at0214203143 c4 = derive (ℓ "亞亜亦交") (ℓ "亦交亞亜")
  (rw⁻ 0 (q412 c4) ∷
   rw⁻ 4 (q411 c4) ∷
   rw⁻ 3 (q418 c4) ∷
   rw 2 (q478 c4) ∷
   rw⁻ 1 (q417 c4) ∷
   rw 0 (q416 c4) ∷
   rw 4 (q7 c4) ∷
   rw 3 (q477 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw 1 (q415 c4) ∷
   rw 2 (q365 c4) ∷
   rw 3 (q413 c4) ∷
   rw 0 (q411 c4) ∷
   rw 2 (q412 c4) ∷ []) Eq.refl

private
  q479 : Ws → Eqn
  q479 c4 = sE 330 (lem-box-tQ-at02233440 c4)
  q480 : Ws → Eqn
  q480 c4 = wpE 911 c4
  q481 : Ws → Eqn
  q481 c4 = wlE 1119 (lit c4)
  q482 : Ws → Eqn
  q482 c4 = wlE 289 (lit c4)
  q483 : Ws → Eqn
  q483 c4 = wpE 32 c4
  q484 : Ws → Eqn
  q484 c4 = wpE 912 c4
  q485 : Ws → Eqn
  q485 c4 = wpE 913 c4

-- CXbc-box @02233440: 17 steps
lem-CXbc-box-at02233440 : Ws → ⟪ (ℓ "乽伵乽") ⟫ʷ ≈ ⟪ (ℓ "伵亐") ⟫ʷ
lem-CXbc-box-at02233440 c4 = derive (ℓ "乽伵乽") (ℓ "伵亐")
  (rw 1 (q479 c4) ∷
   rw 0 (q393 c4) ∷
   rw⁻ 1 (q480 c4) ∷
   rw 3 (q481 c4) ∷
   rw 2 (q393 c4) ∷
   rw 5 (q482 c4) ∷
   rw⁻ 9 (q385 c4) ∷
   rw 8 (q355 c4) ∷
   rw⁻ 7 (q483 c4) ∷
   rw 6 (q355 c4) ∷
   rw⁻ 5 (q383 c4) ∷
   rw⁻ 6 (q482 c4) ∷
   rw 4 (q194 c4) ∷
   rw⁻ 3 (q480 c4) ∷
   rw 4 (q484 c4) ∷
   rw⁻ 0 (q479 c4) ∷
   rw⁻ 1 (q485 c4) ∷ []) Eq.refl

private
  q486 : Ws → Eqn
  q486 c4 = wlE 1120 (lit c4)
  q487 : Ws → Eqn
  q487 c4 = wpE 42 c4
  q488 : Ws → Eqn
  q488 c4 = wpE 914 c4
  q489 : Ws → Eqn
  q489 c4 = wpE 46 c4
  q490 : Ws → Eqn
  q490 c4 = wlE 193 (lit c4)
  q491 : Ws → Eqn
  q491 c4 = wlE 197 (lit c4)
  q492 : Ws → Eqn
  q492 c4 = wlE 1121 (lit c4)
  q493 : Ws → Eqn
  q493 c4 = wpE 915 c4

-- CXcb-box @02233440: 18 steps
lem-CXcb-box-at02233440 : Ws → ⟪ (ℓ "争伵争") ⟫ʷ ≈ ⟪ (ℓ "伵五") ⟫ʷ
lem-CXcb-box-at02233440 c4 = derive (ℓ "争伵争") (ℓ "伵五")
  (rw 1 (q479 c4) ∷
   rw 0 (q486 c4) ∷
   rw⁻ 2 (q487 c4) ∷
   rw⁻ 1 (q488 c4) ∷
   rw 4 (q489 c4) ∷
   rw 8 (q490 c4) ∷
   rw 7 (q379 c4) ∷
   rw 6 (q365 c4) ∷
   rw 5 (q379 c4) ∷
   rw 4 (q366 c4) ∷
   rw⁻ 5 (q489 c4) ∷
   rw⁻ 3 (q491 c4) ∷
   rw 2 (q486 c4) ∷
   rw 3 (q492 c4) ∷
   rw 4 (q260 c4) ∷
   rw⁻ 3 (q488 c4) ∷
   rw⁻ 0 (q479 c4) ∷
   rw⁻ 1 (q493 c4) ∷ []) Eq.refl

private
  q494 : Ws → Eqn
  q494 c4 = sE 334 (lem-tP-at022440 c4)

-- VPQ @022440: 14 steps
lem-VPQ-at022440 : Ws → ⟪ (ℓ "亪亨亚亘") ⟫ʷ ≈ ⟪ (ℓ "亚亘亪亨") ⟫ʷ
lem-VPQ-at022440 c4 = derive (ℓ "亪亨亚亘") (ℓ "亚亘亪亨")
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw 2 (q4 c4) ∷
   rw⁻ 1 (q5 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   rw 4 (q7 c4) ∷
   rw 3 (q494 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw 1 (q9 c4) ∷
   rw 2 (q10 c4) ∷
   rw 3 (q11 c4) ∷
   rw 0 (q2 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q495 : Ws → Eqn
  q495 c4 = sE 331 (lem-box-tQ-at022440 c4)
  q496 : Ws → Eqn
  q496 c4 = wlE 1132 (lit c4)
  q497 : Ws → Eqn
  q497 c4 = wpE 920 c4
  q498 : Ws → Eqn
  q498 c4 = wpE 921 c4
  q499 : Ws → Eqn
  q499 c4 = wlE 199 (lit c4)
  q500 : Ws → Eqn
  q500 c4 = wpE 47 c4
  q501 : Ws → Eqn
  q501 c4 = wpE 48 c4
  q502 : Ws → Eqn
  q502 c4 = wpE 922 c4

-- CXbc-box @022440: 17 steps
lem-CXbc-box-at022440 : Ws → ⟪ (ℓ "争伶争") ⟫ʷ ≈ ⟪ (ℓ "伶五") ⟫ʷ
lem-CXbc-box-at022440 c4 = derive (ℓ "争伶争") (ℓ "伶五")
  (rw 1 (q495 c4) ∷
   rw 0 (q496 c4) ∷
   rw⁻ 1 (q497 c4) ∷
   rw 3 (q498 c4) ∷
   rw 2 (q496 c4) ∷
   rw 5 (q489 c4) ∷
   rw⁻ 9 (q499 c4) ∷
   rw 8 (q129 c4) ∷
   rw⁻ 7 (q500 c4) ∷
   rw 6 (q129 c4) ∷
   rw⁻ 5 (q501 c4) ∷
   rw⁻ 6 (q489 c4) ∷
   rw⁻ 4 (q194 c4) ∷
   rw⁻ 3 (q497 c4) ∷
   rw 4 (q502 c4) ∷
   rw⁻ 0 (q495 c4) ∷
   rw⁻ 1 (q493 c4) ∷ []) Eq.refl
