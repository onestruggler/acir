{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD009 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D009 (Sᴰ : SD009) where

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
  lem-comm-CS12-CCZ034 : Ws → St 191
  lem-comm-CS12-CCZ034 = pickᴰ 1 Sᴰ
  lem-comm-CS13-TOFF024 : Ws → St 192
  lem-comm-CS13-TOFF024 = pickᴰ 2 Sᴰ
  lem-comm-CS14-TOFF023 : Ws → St 193
  lem-comm-CS14-TOFF023 = pickᴰ 3 Sᴰ
  lem-comm-CS24-CCZ013 : Ws → St 194
  lem-comm-CS24-CCZ013 = pickᴰ 4 Sᴰ
  lem-comm-CS24-TOFF013 : Ws → St 195
  lem-comm-CS24-TOFF013 = pickᴰ 5 Sᴰ
  lem-comm-CSd02-TOFF134 : Ws → St 196
  lem-comm-CSd02-TOFF134 = pickᴰ 6 Sᴰ
  lem-comm-CSd03-TOFF412 : Ws → St 197
  lem-comm-CSd03-TOFF412 = pickᴰ 7 Sᴰ
  lem-comm-CSd04-TOFF213 : Ws → St 198
  lem-comm-CSd04-TOFF213 = pickᴰ 8 Sᴰ
  lem-comm-CSd12-CCZ034 : Ws → St 199
  lem-comm-CSd12-CCZ034 = pickᴰ 9 Sᴰ
  lem-comm-CSd12-TOFF034 : Ws → St 63
  lem-comm-CSd12-TOFF034 = pickᴰ 10 Sᴰ
  lem-comm-CSd12-TOFF403 : Ws → St 200
  lem-comm-CSd12-TOFF403 = pickᴰ 11 Sᴰ
  lem-comm-CSd13-TOFF024 : Ws → St 201
  lem-comm-CSd13-TOFF024 = pickᴰ 12 Sᴰ
  lem-comm-CSd14-TOFF023 : Ws → St 202
  lem-comm-CSd14-TOFF023 = pickᴰ 13 Sᴰ
  lem-comm-CSd23-TOFF014 : Ws → St 203
  lem-comm-CSd23-TOFF014 = pickᴰ 14 Sᴰ
  lem-comm-CSd24-CCZ013 : Ws → St 204
  lem-comm-CSd24-CCZ013 = pickᴰ 15 Sᴰ
  lem-comm-CSd24-TOFF013 : Ws → St 205
  lem-comm-CSd24-TOFF013 = pickᴰ 16 Sᴰ
  lem-comm-CX12-CCZ034 : Ws → St 2
  lem-comm-CX12-CCZ034 = pickᴰ 17 Sᴰ
  lem-comm-CX21-CCZ034 : Ws → St 5
  lem-comm-CX21-CCZ034 = pickᴰ 18 Sᴰ
  lem-comm-CX24-CCZ013 : Ws → St 7
  lem-comm-CX24-CCZ013 = pickᴰ 19 Sᴰ
  lem-comm-CX31-CCZ024 : Ws → St 8
  lem-comm-CX31-CCZ024 = pickᴰ 20 Sᴰ
  lem-comm-CX32-CCZ014 : Ws → St 9
  lem-comm-CX32-CCZ014 = pickᴰ 21 Sᴰ
  lem-comm-CZ04-TOFF213 : Ws → St 206
  lem-comm-CZ04-TOFF213 = pickᴰ 22 Sᴰ
  lem-comm-CZ04-TOFF312 : Ws → St 207
  lem-comm-CZ04-TOFF312 = pickᴰ 23 Sᴰ
  lem-comm-CZ12-CCZ034 : Ws → St 65
  lem-comm-CZ12-CCZ034 = pickᴰ 24 Sᴰ
  lem-comm-CZ12-TOFF034 : Ws → St 66
  lem-comm-CZ12-TOFF034 = pickᴰ 25 Sᴰ
  lem-comm-CZ14-TOFF023 : Ws → St 208
  lem-comm-CZ14-TOFF023 = pickᴰ 26 Sᴰ
  lem-comm-CZ24-TOFF013 : Ws → St 209
  lem-comm-CZ24-TOFF013 = pickᴰ 27 Sᴰ
  lem-comm-TOFF013-CSd24 : Ws → St 210
  lem-comm-TOFF013-CSd24 = pickᴰ 28 Sᴰ
  lem-comm-TOFF014-CSd23 : Ws → St 211
  lem-comm-TOFF014-CSd23 = pickᴰ 29 Sᴰ
  lem-comm-TOFF024-CSd13 : Ws → St 212
  lem-comm-TOFF024-CSd13 = pickᴰ 30 Sᴰ
  lem-comm-TOFF204-CSd13 : Ws → St 213
  lem-comm-TOFF204-CSd13 = pickᴰ 31 Sᴰ
  lem-comm-TOFF312-CSd04 : Ws → St 214
  lem-comm-TOFF312-CSd04 = pickᴰ 32 Sᴰ
  lem-comm-TOFF412-CSd03 : Ws → St 215
  lem-comm-TOFF412-CSd03 = pickᴰ 33 Sᴰ
  lem-comm-CS04-CCZ123 : Ws → St 216
  lem-comm-CS04-CCZ123 = pickᴰ 34 Sᴰ
  lem-comm-CS04-TOFF312 : Ws → St 217
  lem-comm-CS04-TOFF312 = pickᴰ 35 Sᴰ
  lem-comm-CS13-TOFF204 : Ws → St 218
  lem-comm-CS13-TOFF204 = pickᴰ 36 Sᴰ
  lem-comm-CS14-CCZ023 : Ws → St 219
  lem-comm-CS14-CCZ023 = pickᴰ 37 Sᴰ
  lem-comm-CSd04-CCZ123 : Ws → St 220
  lem-comm-CSd04-CCZ123 = pickᴰ 38 Sᴰ
  lem-comm-CSd04-TOFF312 : Ws → St 221
  lem-comm-CSd04-TOFF312 = pickᴰ 39 Sᴰ
  lem-comm-CSd12-TOFF304 : Ws → St 222
  lem-comm-CSd12-TOFF304 = pickᴰ 40 Sᴰ
  lem-comm-CSd13-TOFF204 : Ws → St 223
  lem-comm-CSd13-TOFF204 = pickᴰ 41 Sᴰ
  lem-comm-CSd14-CCZ023 : Ws → St 224
  lem-comm-CSd14-CCZ023 = pickᴰ 42 Sᴰ
  lem-comm-CX40-CCZ123 : Ws → St 20
  lem-comm-CX40-CCZ123 = pickᴰ 43 Sᴰ
  lem-comm-CZ03-TOFF214 : Ws → St 225
  lem-comm-CZ03-TOFF214 = pickᴰ 44 Sᴰ
  lem-comm-CZ12-TOFF304 : Ws → St 226
  lem-comm-CZ12-TOFF304 = pickᴰ 45 Sᴰ
  lem-comm-CZ12-TOFF403 : Ws → St 227
  lem-comm-CZ12-TOFF403 = pickᴰ 46 Sᴰ
  lem-comm-TOFF304-CSd12 : Ws → St 228
  lem-comm-TOFF304-CSd12 = pickᴰ 47 Sᴰ
  lem-comm-TOFF023-CSd14 : Ws → St 229
  lem-comm-TOFF023-CSd14 = pickᴰ 48 Sᴰ
  lem-CXbc-box-at032032 : Ws → St 230
  lem-CXbc-box-at032032 = pickᴰ 49 Sᴰ
  lem-CXbc-box-at04203243 : Ws → St 231
  lem-CXbc-box-at04203243 = pickᴰ 50 Sᴰ
  lem-CXbc-box-at13243142 : Ws → St 232
  lem-CXbc-box-at13243142 = pickᴰ 51 Sᴰ
  lem-CXbc-box-at13243241 : Ws → St 233
  lem-CXbc-box-at13243241 = pickᴰ 52 Sᴰ
  lem-CXbc-box-at14233142 : Ws → St 234
  lem-CXbc-box-at14233142 = pickᴰ 53 Sᴰ
  lem-CXcb-box-at032032 : Ws → St 235
  lem-CXcb-box-at032032 = pickᴰ 54 Sᴰ
  lem-CXcb-box-at04203243 : Ws → St 236
  lem-CXcb-box-at04203243 = pickᴰ 55 Sᴰ
  lem-CXcb-box-at13243142 : Ws → St 237
  lem-CXcb-box-at13243142 = pickᴰ 56 Sᴰ
  lem-CXcb-box-at13243241 : Ws → St 238
  lem-CXcb-box-at13243241 = pickᴰ 57 Sᴰ
  lem-CXcb-box-at14233142 : Ws → St 239
  lem-CXcb-box-at14233142 = pickᴰ 58 Sᴰ
  lem-VPQ-at021021 : Ws → St 240
  lem-VPQ-at021021 = pickᴰ 59 Sᴰ
  lem-VPQ-at03102132 : Ws → St 241
  lem-VPQ-at03102132 = pickᴰ 60 Sᴰ
  lem-VPQ-at0410213243 : Ws → St 242
  lem-VPQ-at0410213243 = pickᴰ 61 Sᴰ
  lem-VPQ-at04203243 : Ws → St 243
  lem-VPQ-at04203243 = pickᴰ 62 Sᴰ
  lem-VPQ-at13243142 : Ws → St 244
  lem-VPQ-at13243142 = pickᴰ 63 Sᴰ
  lem-VPQ-at13243241 : Ws → St 245
  lem-VPQ-at13243241 = pickᴰ 64 Sᴰ
  lem-VPQ-at14233142 : Ws → St 246
  lem-VPQ-at14233142 = pickᴰ 65 Sᴰ
  lem-box-tQ : Ws → St 247
  lem-box-tQ = pickᴰ 66 Sᴰ
  lem-box-tQ-at0210243143 : Ws → St 248
  lem-box-tQ-at0210243143 = pickᴰ 67 Sᴰ
  lem-box-tQ-at0214203143 : Ws → St 249
  lem-box-tQ-at0214203143 = pickᴰ 68 Sᴰ
  lem-box-tQ-at0214213043 : Ws → St 250
  lem-box-tQ-at0214213043 = pickᴰ 69 Sᴰ
  lem-box-tQ-at0310243142 : Ws → St 251
  lem-box-tQ-at0310243142 = pickᴰ 70 Sᴰ
  lem-box-tQ-at0330 : Ws → St 252
  lem-box-tQ-at0330 = pickᴰ 71 Sᴰ
  lem-box-tQ-at043043 : Ws → St 253
  lem-box-tQ-at043043 = pickᴰ 72 Sᴰ
  lem-box-tQ-at1221 : Ws → St 254
  lem-box-tQ-at1221 = pickᴰ 73 Sᴰ
  lem-box-tQ-at122331 : Ws → St 255
  lem-box-tQ-at122331 = pickᴰ 74 Sᴰ
  lem-box-tQ-at12243143 : Ws → St 256
  lem-box-tQ-at12243143 = pickᴰ 75 Sᴰ
  lem-box-tQ-at122441 : Ws → St 257
  lem-box-tQ-at122441 = pickᴰ 76 Sᴰ
  lem-box-tQ-at132132 : Ws → St 258
  lem-box-tQ-at132132 = pickᴰ 77 Sᴰ
  lem-box-tQ-at13213442 : Ws → St 259
  lem-box-tQ-at13213442 = pickᴰ 78 Sᴰ
  lem-box-tQ-at1331 : Ws → St 260
  lem-box-tQ-at1331 = pickᴰ 79 Sᴰ
  lem-box-tQ-at133441 : Ws → St 261
  lem-box-tQ-at133441 = pickᴰ 80 Sᴰ
  lem-box-tQ-at2332 : Ws → St 262
  lem-box-tQ-at2332 = pickᴰ 81 Sᴰ
  lem-box-tQ-at243243 : Ws → St 263
  lem-box-tQ-at243243 = pickᴰ 82 Sᴰ
  lem-box-tQ-at3443 : Ws → St 264
  lem-box-tQ-at3443 = pickᴰ 83 Sᴰ
  lem-tP : Ws → St 265
  lem-tP = pickᴰ 84 Sᴰ
  lem-tP-at0110 : Ws → St 266
  lem-tP-at0110 = pickᴰ 85 Sᴰ
  lem-tP-at0210243143 : Ws → St 267
  lem-tP-at0210243143 = pickᴰ 86 Sᴰ
  lem-tP-at0214213043 : Ws → St 268
  lem-tP-at0214213043 = pickᴰ 87 Sᴰ
  lem-tP-at0310243142 : Ws → St 269
  lem-tP-at0310243142 = pickᴰ 88 Sᴰ
  lem-tP-at0314203142 : Ws → St 270
  lem-tP-at0314203142 = pickᴰ 89 Sᴰ
  lem-tP-at0330 : Ws → St 271
  lem-tP-at0330 = pickᴰ 90 Sᴰ
  lem-tP-at043043 : Ws → St 272
  lem-tP-at043043 = pickᴰ 91 Sᴰ
  lem-tP-at1221 : Ws → St 273
  lem-tP-at1221 = pickᴰ 92 Sᴰ
  lem-tP-at122331 : Ws → St 274
  lem-tP-at122331 = pickᴰ 93 Sᴰ
  lem-tP-at122441 : Ws → St 275
  lem-tP-at122441 = pickᴰ 94 Sᴰ
  lem-tP-at132132 : Ws → St 276
  lem-tP-at132132 = pickᴰ 95 Sᴰ
  lem-tP-at13213442 : Ws → St 277
  lem-tP-at13213442 = pickᴰ 96 Sᴰ
  lem-tP-at1331 : Ws → St 278
  lem-tP-at1331 = pickᴰ 97 Sᴰ
  lem-tP-at2332 : Ws → St 279
  lem-tP-at2332 = pickᴰ 98 Sᴰ
  lem-tP-at243243 : Ws → St 280
  lem-tP-at243243 = pickᴰ 99 Sᴰ
  lem-tP-at3443 : Ws → St 281
  lem-tP-at3443 = pickᴰ 100 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = wlE 158 (lit c4)
  q2 : Ws → Eqn
  q2 c4 = wpE 5 c4
  q3 : Ws → Eqn
  q3 c4 = eqn (ℓ "下乺") (ℓ "乺下") (c₁ (S • S • S) ((CS • CS • CS) ↑ ↑))
  q4 : Ws → Eqn
  q4 c4 = eqn (ℓ "亍乺") (ℓ "乺亍") (c₃ (Toff) (CS • CS • CS))
  q5 : Ws → Eqn
  q5 c4 = eqn (ℓ "上乺") (ℓ "乺上") (c₁ (S) ((CS • CS • CS) ↑ ↑))
  q6 : Ws → Eqn
  q6 c4 = eqn (ℓ "么乺") (ℓ "乺么") (c₃ ((CS • CS • CS) ↑) (CS • CS • CS))
  q7 : Ws → Eqn
  q7 c4 = wlE 159 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = sE 265 (lem-tP c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (ℓ "上么") (ℓ "么上") (c₁ (S) (CS • CS • CS))
  q10 : Ws → Eqn
  q10 c4 = sE 63 (lem-comm-CSd12-TOFF034 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (ℓ "下么") (ℓ "么下") (c₁ (S • S • S) (CS • CS • CS))

-- VPQ: 14 steps
lem-VPQ : Ws → ⟪ (ℓ "亍二亡亠") ⟫ʷ ≈ ⟪ (ℓ "亡亠亍二") ⟫ʷ
lem-VPQ c4 = derive (ℓ "亍二亡亠") (ℓ "亡亠亍二")
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw 3 (q3 c4) ∷
   rw 2 (q4 c4) ∷
   rw 1 (q5 c4) ∷
   rw 0 (q6 c4) ∷
   rw 4 (q7 c4) ∷
   rw 3 (q8 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   rw 2 (q10 c4) ∷
   rw⁻ 3 (q11 c4) ∷
   rw 0 (q2 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q12 : Ws → Eqn
  q12 c4 = wlE 163 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = sE 66 (lem-comm-CZ12-TOFF034 c4)
  q14 : Ws → Eqn
  q14 c4 = wlE 164 (lit c4)

-- t-cP: 5 steps
lem-t-cP : Ws → ⟪ (ℓ "亍二亡二亡") ⟫ʷ ≈ ⟪ (ℓ "二亡二亡亍") ⟫ʷ
lem-t-cP c4 = derive (ℓ "亍二亡二亡") (ℓ "二亡二亡亍")
  (rw⁻ 0 (q12 c4) ∷
   rw 2 (q13 c4) ∷
   rw 1 (q8 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw 3 (q8 c4) ∷ []) Eq.refl

private
  q15 : Ws → Eqn
  q15 c4 = wpE 15 c4
  q16 : Ws → Eqn
  q16 c4 = wlE 176 (lit c4)
  q17 : Ws → Eqn
  q17 c4 = wlE 177 (lit c4)
  q18 : Ws → Eqn
  q18 c4 = sE 213 (lem-comm-TOFF204-CSd13 c4)
  q19 : Ws → Eqn
  q19 c4 = wlE 178 (lit c4)
  q20 : Ws → Eqn
  q20 c4 = wpE 16 c4
  q21 : Ws → Eqn
  q21 c4 = wlE 179 (lit c4)
  q22 : Ws → Eqn
  q22 c4 = sE 267 (lem-tP-at0210243143 c4)
  q23 : Ws → Eqn
  q23 c4 = wpE 17 c4
  q24 : Ws → Eqn
  q24 c4 = sE 198 (lem-comm-CSd04-TOFF213 c4)
  q25 : Ws → Eqn
  q25 c4 = wpE 18 c4

-- VPQ @0210243143: 14 steps
lem-VPQ-at0210243143 : Ws → ⟪ (ℓ "亞亜亦交") ⟫ʷ ≈ ⟪ (ℓ "亦交亞亜") ⟫ʷ
lem-VPQ-at0210243143 c4 = derive (ℓ "亞亜亦交") (ℓ "亦交亞亜")
  (rw⁻ 0 (q15 c4) ∷
   rw⁻ 4 (q16 c4) ∷
   rw⁻ 3 (q17 c4) ∷
   rw 2 (q18 c4) ∷
   rw⁻ 1 (q19 c4) ∷
   rw 0 (q20 c4) ∷
   rw 4 (q21 c4) ∷
   rw 3 (q22 c4) ∷
   rw⁻ 4 (q21 c4) ∷
   rw 1 (q23 c4) ∷
   rw 2 (q24 c4) ∷
   rw 3 (q25 c4) ∷
   rw 0 (q16 c4) ∷
   rw 2 (q15 c4) ∷ []) Eq.refl

private
  q26 : Ws → Eqn
  q26 c4 = wpE 27 c4
  q27 : Ws → Eqn
  q27 c4 = sE 206 (lem-comm-CZ04-TOFF213 c4)
  q28 : Ws → Eqn
  q28 c4 = wpE 28 c4

-- t-cP @0210243143: 5 steps
lem-t-cP-at0210243143 : Ws → ⟪ (ℓ "亞亜亦亜亦") ⟫ʷ ≈ ⟪ (ℓ "亜亦亜亦亞") ⟫ʷ
lem-t-cP-at0210243143 c4 = derive (ℓ "亞亜亦亜亦") (ℓ "亜亦亜亦亞")
  (rw⁻ 0 (q26 c4) ∷
   rw 2 (q27 c4) ∷
   rw 1 (q22 c4) ∷
   rw⁻ 2 (q28 c4) ∷
   rw 3 (q22 c4) ∷ []) Eq.refl

private
  q29 : Ws → Eqn
  q29 c4 = wpE 50 c4
  q30 : Ws → Eqn
  q30 c4 = wlE 201 (lit c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (ℓ "下乣") (ℓ "乣下") (c₁ (S • S • S) ((CS • CS • CS) ↑))
  q32 : Ws → Eqn
  q32 c4 = sE 211 (lem-comm-TOFF014-CSd23 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (ℓ "上乣") (ℓ "乣上") (c₁ (S) ((CS • CS • CS) ↑))
  q34 : Ws → Eqn
  q34 c4 = wlE 202 (lit c4)
  q35 : Ws → Eqn
  q35 c4 = sE 280 (lem-tP-at243243 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (ℓ "上乖") (ℓ "乖上") (c₁ (S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))
  q37 : Ws → Eqn
  q37 c4 = sE 202 (lem-comm-CSd14-TOFF023 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (ℓ "下乖") (ℓ "乖下") (c₁ (S • S • S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))

-- VPQ @243243: 14 steps
lem-VPQ-at243243 : Ws → ⟪ (ℓ "井五亙亘") ⟫ʷ ≈ ⟪ (ℓ "亙亘井五") ⟫ʷ
lem-VPQ-at243243 c4 = derive (ℓ "井五亙亘") (ℓ "亙亘井五")
  (rw⁻ 0 (q29 c4) ∷
   rw⁻ 4 (q30 c4) ∷
   rw 3 (q31 c4) ∷
   rw 2 (q32 c4) ∷
   rw 1 (q33 c4) ∷
   rw 0 (q34 c4) ∷
   rw 4 (q7 c4) ∷
   rw 3 (q35 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 1 (q36 c4) ∷
   rw 2 (q37 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   rw 0 (q30 c4) ∷
   rw 2 (q29 c4) ∷ []) Eq.refl

private
  q39 : Ws → Eqn
  q39 c4 = wpE 58 c4
  q40 : Ws → Eqn
  q40 c4 = sE 208 (lem-comm-CZ14-TOFF023 c4)
  q41 : Ws → Eqn
  q41 c4 = wpE 59 c4

-- t-cP @243243: 5 steps
lem-t-cP-at243243 : Ws → ⟪ (ℓ "井五亙五亙") ⟫ʷ ≈ ⟪ (ℓ "五亙五亙井") ⟫ʷ
lem-t-cP-at243243 c4 = derive (ℓ "井五亙五亙") (ℓ "五亙五亙井")
  (rw⁻ 0 (q39 c4) ∷
   rw 2 (q40 c4) ∷
   rw 1 (q35 c4) ∷
   rw⁻ 2 (q41 c4) ∷
   rw 3 (q35 c4) ∷ []) Eq.refl

private
  q42 : Ws → Eqn
  q42 c4 = wpE 79 c4
  q43 : Ws → Eqn
  q43 c4 = wlE 227 (lit c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (ℓ "下乏") (ℓ "乏下") (c₁ (S • S • S) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q45 : Ws → Eqn
  q45 c4 = sE 212 (lem-comm-TOFF024-CSd13 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (ℓ "上乏") (ℓ "乏上") (c₁ (S) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q47 : Ws → Eqn
  q47 c4 = wlE 228 (lit c4)
  q48 : Ws → Eqn
  q48 c4 = sE 275 (lem-tP-at122441 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (ℓ "上乪") (ℓ "乪上") (c₁ (S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑))
  q50 : Ws → Eqn
  q50 c4 = sE 205 (lem-comm-CSd24-TOFF013 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (ℓ "下乪") (ℓ "乪下") (c₁ (S • S • S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑))

-- VPQ @122441: 14 steps
lem-VPQ-at122441 : Ws → ⟪ (ℓ "亝亜云亐") ⟫ʷ ≈ ⟪ (ℓ "云亐亝亜") ⟫ʷ
lem-VPQ-at122441 c4 = derive (ℓ "亝亜云亐") (ℓ "云亐亝亜")
  (rw⁻ 0 (q42 c4) ∷
   rw⁻ 4 (q43 c4) ∷
   rw 3 (q44 c4) ∷
   rw 2 (q45 c4) ∷
   rw 1 (q46 c4) ∷
   rw⁻ 0 (q47 c4) ∷
   rw 4 (q7 c4) ∷
   rw 3 (q48 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 1 (q49 c4) ∷
   rw 2 (q50 c4) ∷
   rw⁻ 3 (q51 c4) ∷
   rw 0 (q43 c4) ∷
   rw 2 (q42 c4) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = wpE 85 c4
  q53 : Ws → Eqn
  q53 c4 = sE 209 (lem-comm-CZ24-TOFF013 c4)
  q54 : Ws → Eqn
  q54 c4 = wpE 86 c4

-- t-cP @122441: 5 steps
lem-t-cP-at122441 : Ws → ⟪ (ℓ "亝亜云亜云") ⟫ʷ ≈ ⟪ (ℓ "亜云亜云亝") ⟫ʷ
lem-t-cP-at122441 c4 = derive (ℓ "亝亜云亜云") (ℓ "亜云亜云亝")
  (rw⁻ 0 (q52 c4) ∷
   rw 2 (q53 c4) ∷
   rw 1 (q48 c4) ∷
   rw⁻ 2 (q54 c4) ∷
   rw 3 (q48 c4) ∷ []) Eq.refl

private
  q55 : Ws → Eqn
  q55 c4 = sE 247 (lem-box-tQ c4)
  q56 : Ws → Eqn
  q56 c4 = wlE 250 (lit c4)
  q57 : Ws → Eqn
  q57 c4 = wpE 100 c4
  q58 : Ws → Eqn
  q58 c4 = wpE 101 c4
  q59 : Ws → Eqn
  q59 c4 = wlE 166 (lit c4)
  q60 : Ws → Eqn
  q60 c4 = wpE 102 c4
  q61 : Ws → Eqn
  q61 c4 = wlE 251 (lit c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (ℓ "亍乹") (ℓ "乹亍") (c₃ (Toff) (CS))
  q63 : Ws → Eqn
  q63 c4 = wlE 252 (lit c4)
  q64 : Ws → Eqn
  q64 c4 = wlE 253 (lit c4)
  q65 : Ws → Eqn
  q65 c4 = wpE 103 c4
  q66 : Ws → Eqn
  q66 c4 = wlE 254 (lit c4)

-- CXcb-box: 18 steps
lem-CXcb-box : Ws → ⟪ (ℓ "乶亹乶") ⟫ʷ ≈ ⟪ (ℓ "亹京") ⟫ʷ
lem-CXcb-box c4 = derive (ℓ "乶亹乶") (ℓ "亹京")
  (rw 1 (q55 c4) ∷
   rw 0 (q56 c4) ∷
   rw⁻ 2 (q57 c4) ∷
   rw⁻ 1 (q58 c4) ∷
   rw 4 (q59 c4) ∷
   rw 8 (q60 c4) ∷
   rw 7 (q61 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw 5 (q61 c4) ∷
   rw⁻ 4 (q62 c4) ∷
   rw⁻ 5 (q59 c4) ∷
   rw⁻ 3 (q63 c4) ∷
   rw 2 (q56 c4) ∷
   rw 3 (q64 c4) ∷
   rw⁻ 4 (q65 c4) ∷
   rw⁻ 3 (q58 c4) ∷
   rw⁻ 0 (q55 c4) ∷
   rw⁻ 1 (q66 c4) ∷ []) Eq.refl

private
  q67 : Ws → Eqn
  q67 c4 = wlE 255 (lit c4)
  q68 : Ws → Eqn
  q68 c4 = wpE 104 c4
  q69 : Ws → Eqn
  q69 c4 = wpE 105 c4
  q70 : Ws → Eqn
  q70 c4 = wlE 256 (lit c4)
  q71 : Ws → Eqn
  q71 c4 = wpE 106 c4
  q72 : Ws → Eqn
  q72 c4 = sE 2 (lem-comm-CX12-CCZ034 c4)
  q73 : Ws → Eqn
  q73 c4 = wpE 107 c4
  q74 : Ws → Eqn
  q74 c4 = wpE 108 c4
  q75 : Ws → Eqn
  q75 c4 = wpE 109 c4
  q76 : Ws → Eqn
  q76 c4 = wpE 110 c4
  q77 : Ws → Eqn
  q77 c4 = wlE 257 (lit c4)

-- CXbc-box: 17 steps
lem-CXbc-box : Ws → ⟪ (ℓ "书亹书") ⟫ʷ ≈ ⟪ (ℓ "亹亨") ⟫ʷ
lem-CXbc-box c4 = derive (ℓ "书亹书") (ℓ "亹亨")
  (rw 1 (q55 c4) ∷
   rw 0 (q67 c4) ∷
   rw⁻ 1 (q68 c4) ∷
   rw 3 (q69 c4) ∷
   rw 2 (q67 c4) ∷
   rw 5 (q70 c4) ∷
   rw⁻ 9 (q71 c4) ∷
   rw 8 (q72 c4) ∷
   rw⁻ 7 (q73 c4) ∷
   rw 6 (q72 c4) ∷
   rw⁻ 5 (q74 c4) ∷
   rw⁻ 6 (q70 c4) ∷
   rw 4 (q75 c4) ∷
   rw⁻ 3 (q68 c4) ∷
   rw 4 (q76 c4) ∷
   rw⁻ 0 (q55 c4) ∷
   rw⁻ 1 (q77 c4) ∷ []) Eq.refl

private
  q78 : Ws → Eqn
  q78 c4 = wpE 112 c4
  q79 : Ws → Eqn
  q79 c4 = wpE 113 c4
  q80 : Ws → Eqn
  q80 c4 = eqn (ℓ "亍乻") (ℓ "乻亍") (c₃ (Toff) (CZ))
  q81 : Ws → Eqn
  q81 c4 = wpE 114 c4

-- P-box: 8 steps
lem-P-box : Ws → ⟪ (ℓ "亡亹亡") ⟫ʷ ≈ ⟪ (ℓ "亹") ⟫ʷ
lem-P-box c4 = derive (ℓ "亡亹亡") (ℓ "亹")
  (rw 1 (q55 c4) ∷
   rw⁻ 0 (q8 c4) ∷
   rw⁻ 1 (q78 c4) ∷
   rw⁻ 3 (q8 c4) ∷
   rw⁻ 4 (q79 c4) ∷
   rw⁻ 2 (q80 c4) ∷
   rw⁻ 3 (q81 c4) ∷
   rw⁻ 0 (q55 c4) ∷ []) Eq.refl

private
  q82 : Ws → Eqn
  q82 c4 = sE 254 (lem-box-tQ-at1221 c4)
  q83 : Ws → Eqn
  q83 c4 = wpE 121 c4
  q84 : Ws → Eqn
  q84 c4 = wpE 122 c4
  q85 : Ws → Eqn
  q85 c4 = wlE 271 (lit c4)
  q86 : Ws → Eqn
  q86 c4 = sE 5 (lem-comm-CX21-CCZ034 c4)
  q87 : Ws → Eqn
  q87 c4 = wpE 123 c4
  q88 : Ws → Eqn
  q88 c4 = wpE 124 c4
  q89 : Ws → Eqn
  q89 c4 = wpE 125 c4
  q90 : Ws → Eqn
  q90 c4 = wlE 272 (lit c4)

-- CXbc-box @1221: 17 steps
lem-CXbc-box-at1221 : Ws → ⟪ (ℓ "乒仌乒") ⟫ʷ ≈ ⟪ (ℓ "仌亨") ⟫ʷ
lem-CXbc-box-at1221 c4 = derive (ℓ "乒仌乒") (ℓ "仌亨")
  (rw 1 (q82 c4) ∷
   rw 0 (q61 c4) ∷
   rw⁻ 1 (q83 c4) ∷
   rw 3 (q84 c4) ∷
   rw 2 (q61 c4) ∷
   rw 5 (q85 c4) ∷
   rw⁻ 9 (q74 c4) ∷
   rw 8 (q86 c4) ∷
   rw⁻ 7 (q87 c4) ∷
   rw 6 (q86 c4) ∷
   rw⁻ 5 (q71 c4) ∷
   rw⁻ 6 (q85 c4) ∷
   rw 4 (q88 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   rw 4 (q89 c4) ∷
   rw⁻ 0 (q82 c4) ∷
   rw⁻ 1 (q90 c4) ∷ []) Eq.refl

private
  q91 : Ws → Eqn
  q91 c4 = wlE 273 (lit c4)
  q92 : Ws → Eqn
  q92 c4 = wpE 126 c4
  q93 : Ws → Eqn
  q93 c4 = wpE 127 c4
  q94 : Ws → Eqn
  q94 c4 = wlE 274 (lit c4)
  q95 : Ws → Eqn
  q95 c4 = wpE 128 c4
  q96 : Ws → Eqn
  q96 c4 = wlE 275 (lit c4)
  q97 : Ws → Eqn
  q97 c4 = wlE 276 (lit c4)
  q98 : Ws → Eqn
  q98 c4 = wpE 129 c4
  q99 : Ws → Eqn
  q99 c4 = wlE 277 (lit c4)

-- CXcb-box @1221: 18 steps
lem-CXcb-box-at1221 : Ws → ⟪ (ℓ "乳仌乳") ⟫ʷ ≈ ⟪ (ℓ "仌亰") ⟫ʷ
lem-CXcb-box-at1221 c4 = derive (ℓ "乳仌乳") (ℓ "仌亰")
  (rw 1 (q82 c4) ∷
   rw 0 (q91 c4) ∷
   rw⁻ 2 (q92 c4) ∷
   rw⁻ 1 (q93 c4) ∷
   rw 4 (q94 c4) ∷
   rw 8 (q95 c4) ∷
   rw 7 (q67 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw 5 (q67 c4) ∷
   rw⁻ 4 (q62 c4) ∷
   rw⁻ 5 (q94 c4) ∷
   rw⁻ 3 (q96 c4) ∷
   rw 2 (q91 c4) ∷
   rw 3 (q97 c4) ∷
   rw⁻ 4 (q98 c4) ∷
   rw⁻ 3 (q93 c4) ∷
   rw⁻ 0 (q82 c4) ∷
   rw⁻ 1 (q99 c4) ∷ []) Eq.refl

private
  q100 : Ws → Eqn
  q100 c4 = sE 273 (lem-tP-at1221 c4)

-- P-box @1221: 8 steps
lem-P-box-at1221 : Ws → ⟪ (ℓ "亡仌亡") ⟫ʷ ≈ ⟪ (ℓ "仌") ⟫ʷ
lem-P-box-at1221 c4 = derive (ℓ "亡仌亡") (ℓ "仌")
  (rw 1 (q82 c4) ∷
   rw⁻ 0 (q100 c4) ∷
   rw⁻ 1 (q78 c4) ∷
   rw⁻ 3 (q100 c4) ∷
   rw⁻ 4 (q79 c4) ∷
   rw⁻ 2 (q80 c4) ∷
   rw⁻ 3 (q81 c4) ∷
   rw⁻ 0 (q82 c4) ∷ []) Eq.refl

-- VPQ @1221: 14 steps
lem-VPQ-at1221 : Ws → ⟪ (ℓ "亍二亡亠") ⟫ʷ ≈ ⟪ (ℓ "亡亠亍二") ⟫ʷ
lem-VPQ-at1221 c4 = derive (ℓ "亍二亡亠") (ℓ "亡亠亍二")
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw 3 (q3 c4) ∷
   rw 2 (q4 c4) ∷
   rw 1 (q5 c4) ∷
   rw 0 (q6 c4) ∷
   rw 4 (q7 c4) ∷
   rw 3 (q100 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   rw 2 (q10 c4) ∷
   rw⁻ 3 (q11 c4) ∷
   rw 0 (q2 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q101 : Ws → Eqn
  q101 c4 = sE 262 (lem-box-tQ-at2332 c4)
  q102 : Ws → Eqn
  q102 c4 = sE 279 (lem-tP-at2332 c4)
  q103 : Ws → Eqn
  q103 c4 = wpE 132 c4
  q104 : Ws → Eqn
  q104 c4 = wpE 133 c4
  q105 : Ws → Eqn
  q105 c4 = wpE 134 c4

-- P-box @2332: 8 steps
lem-P-box-at2332 : Ws → ⟪ (ℓ "亝亾亝") ⟫ʷ ≈ ⟪ (ℓ "亾") ⟫ʷ
lem-P-box-at2332 c4 = derive (ℓ "亝亾亝") (ℓ "亾")
  (rw 1 (q101 c4) ∷
   rw⁻ 0 (q102 c4) ∷
   rw⁻ 1 (q103 c4) ∷
   rw⁻ 3 (q102 c4) ∷
   rw⁻ 4 (q104 c4) ∷
   rw 2 (q53 c4) ∷
   rw⁻ 3 (q105 c4) ∷
   rw⁻ 0 (q101 c4) ∷ []) Eq.refl

private
  q106 : Ws → Eqn
  q106 c4 = sE 210 (lem-comm-TOFF013-CSd24 c4)
  q107 : Ws → Eqn
  q107 c4 = sE 201 (lem-comm-CSd13-TOFF024 c4)

-- VPQ @2332: 14 steps
lem-VPQ-at2332 : Ws → ⟪ (ℓ "云亐亝亜") ⟫ʷ ≈ ⟪ (ℓ "亝亜云亐") ⟫ʷ
lem-VPQ-at2332 c4 = derive (ℓ "云亐亝亜") (ℓ "亝亜云亐")
  (rw⁻ 0 (q43 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   rw 3 (q51 c4) ∷
   rw 2 (q106 c4) ∷
   rw 1 (q49 c4) ∷
   rw 0 (q47 c4) ∷
   rw 4 (q7 c4) ∷
   rw 3 (q102 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 1 (q46 c4) ∷
   rw 2 (q107 c4) ∷
   rw⁻ 3 (q44 c4) ∷
   rw 0 (q42 c4) ∷
   rw 2 (q43 c4) ∷ []) Eq.refl

private
  q108 : Ws → Eqn
  q108 c4 = wlE 300 (lit c4)
  q109 : Ws → Eqn
  q109 c4 = sE 232 (lem-CXbc-box-at13243142 c4)
  q110 : Ws → Eqn
  q110 c4 = wlE 301 (lit c4)
  q111 : Ws → Eqn
  q111 c4 = sE 237 (lem-CXcb-box-at13243142 c4)
  q112 : Ws → Eqn
  q112 c4 = wlE 302 (lit c4)
  q113 : Ws → Eqn
  q113 c4 = wlE 303 (lit c4)
  q114 : Ws → Eqn
  q114 c4 = wlE 304 (lit c4)
  q115 : Ws → Eqn
  q115 c4 = wlE 305 (lit c4)

-- SWbc-box @13243142: 11 steps
lem-SWbc-box-at13243142 : Ws → ⟪ (ℓ "乘仳乘") ⟫ʷ ≈ ⟪ (ℓ "仳") ⟫ʷ
lem-SWbc-box-at13243142 c4 = derive (ℓ "乘仳乘") (ℓ "仳")
  (rw⁻ 0 (q108 c4) ∷
   rw⁻ 4 (q108 c4) ∷
   rw 2 (q109 c4) ∷
   rw 3 (q110 c4) ∷
   rw 1 (q111 c4) ∷
   rw 4 (q112 c4) ∷
   rw 3 (q113 c4) ∷
   rw 2 (q113 c4) ∷
   rw 3 (q114 c4) ∷
   rw 0 (q109 c4) ∷
   rw 1 (q115 c4) ∷ []) Eq.refl

private
  q116 : Ws → Eqn
  q116 c4 = sE 255 (lem-box-tQ-at122331 c4)
  q117 : Ws → Eqn
  q117 c4 = sE 274 (lem-tP-at122331 c4)
  q118 : Ws → Eqn
  q118 c4 = wpE 158 c4
  q119 : Ws → Eqn
  q119 c4 = wpE 159 c4
  q120 : Ws → Eqn
  q120 c4 = wpE 160 c4

-- P-box @122331: 8 steps
lem-P-box-at122331 : Ws → ⟪ (ℓ "井仕井") ⟫ʷ ≈ ⟪ (ℓ "仕") ⟫ʷ
lem-P-box-at122331 c4 = derive (ℓ "井仕井") (ℓ "仕")
  (rw 1 (q116 c4) ∷
   rw⁻ 0 (q117 c4) ∷
   rw⁻ 1 (q118 c4) ∷
   rw⁻ 3 (q117 c4) ∷
   rw⁻ 4 (q119 c4) ∷
   rw 2 (q40 c4) ∷
   rw⁻ 3 (q120 c4) ∷
   rw⁻ 0 (q116 c4) ∷ []) Eq.refl

private
  q121 : Ws → Eqn
  q121 c4 = sE 229 (lem-comm-TOFF023-CSd14 c4)
  q122 : Ws → Eqn
  q122 c4 = sE 203 (lem-comm-CSd23-TOFF014 c4)

-- VPQ @122331: 14 steps
lem-VPQ-at122331 : Ws → ⟪ (ℓ "亙亘井五") ⟫ʷ ≈ ⟪ (ℓ "井五亙亘") ⟫ʷ
lem-VPQ-at122331 c4 = derive (ℓ "亙亘井五") (ℓ "井五亙亘")
  (rw⁻ 0 (q30 c4) ∷
   rw⁻ 4 (q29 c4) ∷
   rw 3 (q38 c4) ∷
   rw 2 (q121 c4) ∷
   rw 1 (q36 c4) ∷
   rw⁻ 0 (q34 c4) ∷
   rw 4 (q7 c4) ∷
   rw 3 (q117 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 1 (q33 c4) ∷
   rw 2 (q122 c4) ∷
   rw⁻ 3 (q31 c4) ∷
   rw 0 (q29 c4) ∷
   rw 2 (q30 c4) ∷ []) Eq.refl

private
  q123 : Ws → Eqn
  q123 c4 = wlE 316 (lit c4)
  q124 : Ws → Eqn
  q124 c4 = sE 233 (lem-CXbc-box-at13243241 c4)
  q125 : Ws → Eqn
  q125 c4 = wlE 317 (lit c4)
  q126 : Ws → Eqn
  q126 c4 = sE 238 (lem-CXcb-box-at13243241 c4)
  q127 : Ws → Eqn
  q127 c4 = wlE 318 (lit c4)
  q128 : Ws → Eqn
  q128 c4 = wlE 319 (lit c4)
  q129 : Ws → Eqn
  q129 c4 = wlE 320 (lit c4)
  q130 : Ws → Eqn
  q130 c4 = wlE 321 (lit c4)

-- SWbc-box @13243241: 11 steps
lem-SWbc-box-at13243241 : Ws → ⟪ (ℓ "乬件乬") ⟫ʷ ≈ ⟪ (ℓ "件") ⟫ʷ
lem-SWbc-box-at13243241 c4 = derive (ℓ "乬件乬") (ℓ "件")
  (rw⁻ 0 (q123 c4) ∷
   rw⁻ 4 (q123 c4) ∷
   rw 2 (q124 c4) ∷
   rw 3 (q125 c4) ∷
   rw 1 (q126 c4) ∷
   rw 4 (q127 c4) ∷
   rw 3 (q128 c4) ∷
   rw 2 (q128 c4) ∷
   rw 3 (q129 c4) ∷
   rw 0 (q124 c4) ∷
   rw 1 (q130 c4) ∷ []) Eq.refl

private
  q131 : Ws → Eqn
  q131 c4 = sE 258 (lem-box-tQ-at132132 c4)
  q132 : Ws → Eqn
  q132 c4 = sE 276 (lem-tP-at132132 c4)

-- P-box @132132: 8 steps
lem-P-box-at132132 : Ws → ⟪ (ℓ "亝令亝") ⟫ʷ ≈ ⟪ (ℓ "令") ⟫ʷ
lem-P-box-at132132 c4 = derive (ℓ "亝令亝") (ℓ "令")
  (rw 1 (q131 c4) ∷
   rw⁻ 0 (q132 c4) ∷
   rw⁻ 1 (q103 c4) ∷
   rw⁻ 3 (q132 c4) ∷
   rw⁻ 4 (q104 c4) ∷
   rw 2 (q53 c4) ∷
   rw⁻ 3 (q105 c4) ∷
   rw⁻ 0 (q131 c4) ∷ []) Eq.refl

-- VPQ @132132: 14 steps
lem-VPQ-at132132 : Ws → ⟪ (ℓ "云亐亝亜") ⟫ʷ ≈ ⟪ (ℓ "亝亜云亐") ⟫ʷ
lem-VPQ-at132132 c4 = derive (ℓ "云亐亝亜") (ℓ "亝亜云亐")
  (rw⁻ 0 (q43 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   rw 3 (q51 c4) ∷
   rw 2 (q106 c4) ∷
   rw 1 (q49 c4) ∷
   rw 0 (q47 c4) ∷
   rw 4 (q7 c4) ∷
   rw 3 (q132 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 1 (q46 c4) ∷
   rw 2 (q107 c4) ∷
   rw⁻ 3 (q44 c4) ∷
   rw 0 (q42 c4) ∷
   rw 2 (q43 c4) ∷ []) Eq.refl

private
  q133 : Ws → Eqn
  q133 c4 = sE 256 (lem-box-tQ-at12243143 c4)
  q134 : Ws → Eqn
  q134 c4 = wpE 181 c4
  q135 : Ws → Eqn
  q135 c4 = wpE 182 c4
  q136 : Ws → Eqn
  q136 c4 = wpE 183 c4
  q137 : Ws → Eqn
  q137 c4 = wlE 245 (lit c4)
  q138 : Ws → Eqn
  q138 c4 = wlE 324 (lit c4)
  q139 : Ws → Eqn
  q139 c4 = sE 7 (lem-comm-CX24-CCZ013 c4)
  q140 : Ws → Eqn
  q140 c4 = wpE 184 c4
  q141 : Ws → Eqn
  q141 c4 = wpE 185 c4
  q142 : Ws → Eqn
  q142 c4 = wpE 186 c4
  q143 : Ws → Eqn
  q143 c4 = wpE 187 c4
  q144 : Ws → Eqn
  q144 c4 = wlE 295 (lit c4)

-- CXbc-box @12243143: 17 steps
lem-CXbc-box-at12243143 : Ws → ⟪ (ℓ "亃仛亃") ⟫ʷ ≈ ⟪ (ℓ "仛亰") ⟫ʷ
lem-CXbc-box-at12243143 c4 = derive (ℓ "亃仛亃") (ℓ "仛亰")
  (rw 1 (q133 c4) ∷
   rw 0 (q134 c4) ∷
   rw⁻ 1 (q135 c4) ∷
   rw 3 (q136 c4) ∷
   rw 2 (q134 c4) ∷
   rw 5 (q137 c4) ∷
   rw⁻ 9 (q138 c4) ∷
   rw 8 (q139 c4) ∷
   rw⁻ 7 (q140 c4) ∷
   rw 6 (q139 c4) ∷
   rw⁻ 5 (q141 c4) ∷
   rw⁻ 6 (q137 c4) ∷
   rw⁻ 4 (q142 c4) ∷
   rw⁻ 3 (q135 c4) ∷
   rw 4 (q143 c4) ∷
   rw⁻ 0 (q133 c4) ∷
   rw⁻ 1 (q144 c4) ∷ []) Eq.refl

private
  q145 : Ws → Eqn
  q145 c4 = wpE 188 c4
  q146 : Ws → Eqn
  q146 c4 = wlE 325 (lit c4)
  q147 : Ws → Eqn
  q147 c4 = wpE 189 c4
  q148 : Ws → Eqn
  q148 c4 = wlE 326 (lit c4)
  q149 : Ws → Eqn
  q149 c4 = wpE 190 c4
  q150 : Ws → Eqn
  q150 c4 = wpE 191 c4
  q151 : Ws → Eqn
  q151 c4 = sE 192 (lem-comm-CS13-TOFF024 c4)
  q152 : Ws → Eqn
  q152 c4 = wpE 192 c4
  q153 : Ws → Eqn
  q153 c4 = wpE 193 c4
  q154 : Ws → Eqn
  q154 c4 = wlE 327 (lit c4)
  q155 : Ws → Eqn
  q155 c4 = wlE 299 (lit c4)

-- CXcb-box @12243143: 18 steps
lem-CXcb-box-at12243143 : Ws → ⟪ (ℓ "乙仛乙") ⟫ʷ ≈ ⟪ (ℓ "仛交") ⟫ʷ
lem-CXcb-box-at12243143 c4 = derive (ℓ "乙仛乙") (ℓ "仛交")
  (rw 1 (q133 c4) ∷
   rw 0 (q145 c4) ∷
   rw⁻ 2 (q146 c4) ∷
   rw⁻ 1 (q147 c4) ∷
   rw 4 (q148 c4) ∷
   rw 8 (q149 c4) ∷
   rw 7 (q150 c4) ∷
   rw 6 (q107 c4) ∷
   rw 5 (q150 c4) ∷
   rw 4 (q151 c4) ∷
   rw⁻ 5 (q148 c4) ∷
   rw 3 (q152 c4) ∷
   rw 2 (q145 c4) ∷
   rw 3 (q153 c4) ∷
   rw⁻ 4 (q154 c4) ∷
   rw⁻ 3 (q147 c4) ∷
   rw⁻ 0 (q133 c4) ∷
   rw⁻ 1 (q155 c4) ∷ []) Eq.refl

private
  q156 : Ws → Eqn
  q156 c4 = wlE 335 (lit c4)
  q157 : Ws → Eqn
  q157 c4 = sE 234 (lem-CXbc-box-at14233142 c4)
  q158 : Ws → Eqn
  q158 c4 = wlE 281 (lit c4)
  q159 : Ws → Eqn
  q159 c4 = sE 239 (lem-CXcb-box-at14233142 c4)
  q160 : Ws → Eqn
  q160 c4 = wlE 336 (lit c4)
  q161 : Ws → Eqn
  q161 c4 = wlE 279 (lit c4)
  q162 : Ws → Eqn
  q162 c4 = wlE 337 (lit c4)

-- SWbc-box @14233142: 11 steps
lem-SWbc-box-at14233142 : Ws → ⟪ (ℓ "乑伋乑") ⟫ʷ ≈ ⟪ (ℓ "伋") ⟫ʷ
lem-SWbc-box-at14233142 c4 = derive (ℓ "乑伋乑") (ℓ "伋")
  (rw⁻ 0 (q156 c4) ∷
   rw⁻ 4 (q156 c4) ∷
   rw 2 (q157 c4) ∷
   rw 3 (q158 c4) ∷
   rw 1 (q159 c4) ∷
   rw 4 (q160 c4) ∷
   rw 3 (q161 c4) ∷
   rw 2 (q161 c4) ∷
   rw 3 (q162 c4) ∷
   rw 0 (q157 c4) ∷
   rw 1 (q115 c4) ∷ []) Eq.refl

private
  q163 : Ws → Eqn
  q163 c4 = wlE 162 (lit c4)
  q164 : Ws → Eqn
  q164 c4 = sE 246 (lem-VPQ-at14233142 c4)
  q165 : Ws → Eqn
  q165 c4 = wlE 341 (lit c4)

-- QVQ @14233142: 3 steps
lem-QVQ-at14233142 : Ws → ⟪ (ℓ "二亡亠二") ⟫ʷ ≈ ⟪ (ℓ "亍亡亠亍") ⟫ʷ
lem-QVQ-at14233142 c4 = derive (ℓ "二亡亠二") (ℓ "亍亡亠亍")
  (rw⁻ 0 (q163 c4) ∷
   rw⁻ 1 (q164 c4) ∷
   rw 4 (q165 c4) ∷ []) Eq.refl

private
  q166 : Ws → Eqn
  q166 c4 = sE 259 (lem-box-tQ-at13213442 c4)
  q167 : Ws → Eqn
  q167 c4 = sE 277 (lem-tP-at13213442 c4)

-- P-box @13213442: 8 steps
lem-P-box-at13213442 : Ws → ⟪ (ℓ "亝仩亝") ⟫ʷ ≈ ⟪ (ℓ "仩") ⟫ʷ
lem-P-box-at13213442 c4 = derive (ℓ "亝仩亝") (ℓ "仩")
  (rw 1 (q166 c4) ∷
   rw⁻ 0 (q167 c4) ∷
   rw⁻ 1 (q103 c4) ∷
   rw⁻ 3 (q167 c4) ∷
   rw⁻ 4 (q104 c4) ∷
   rw 2 (q53 c4) ∷
   rw⁻ 3 (q105 c4) ∷
   rw⁻ 0 (q166 c4) ∷ []) Eq.refl

-- VPQ @13213442: 14 steps
lem-VPQ-at13213442 : Ws → ⟪ (ℓ "云亐亝亜") ⟫ʷ ≈ ⟪ (ℓ "亝亜云亐") ⟫ʷ
lem-VPQ-at13213442 c4 = derive (ℓ "云亐亝亜") (ℓ "亝亜云亐")
  (rw⁻ 0 (q43 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   rw 3 (q51 c4) ∷
   rw 2 (q106 c4) ∷
   rw 1 (q49 c4) ∷
   rw 0 (q47 c4) ∷
   rw 4 (q7 c4) ∷
   rw 3 (q167 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 1 (q46 c4) ∷
   rw 2 (q107 c4) ∷
   rw⁻ 3 (q44 c4) ∷
   rw 0 (q42 c4) ∷
   rw 2 (q43 c4) ∷ []) Eq.refl

private
  q168 : Ws → Eqn
  q168 c4 = sE 260 (lem-box-tQ-at1331 c4)
  q169 : Ws → Eqn
  q169 c4 = sE 278 (lem-tP-at1331 c4)

-- P-box @1331: 8 steps
lem-P-box-at1331 : Ws → ⟪ (ℓ "井仭井") ⟫ʷ ≈ ⟪ (ℓ "仭") ⟫ʷ
lem-P-box-at1331 c4 = derive (ℓ "井仭井") (ℓ "仭")
  (rw 1 (q168 c4) ∷
   rw⁻ 0 (q169 c4) ∷
   rw⁻ 1 (q118 c4) ∷
   rw⁻ 3 (q169 c4) ∷
   rw⁻ 4 (q119 c4) ∷
   rw 2 (q40 c4) ∷
   rw⁻ 3 (q120 c4) ∷
   rw⁻ 0 (q168 c4) ∷ []) Eq.refl

-- VPQ @1331: 14 steps
lem-VPQ-at1331 : Ws → ⟪ (ℓ "亙亘井五") ⟫ʷ ≈ ⟪ (ℓ "井五亙亘") ⟫ʷ
lem-VPQ-at1331 c4 = derive (ℓ "亙亘井五") (ℓ "井五亙亘")
  (rw⁻ 0 (q30 c4) ∷
   rw⁻ 4 (q29 c4) ∷
   rw 3 (q38 c4) ∷
   rw 2 (q121 c4) ∷
   rw 1 (q36 c4) ∷
   rw⁻ 0 (q34 c4) ∷
   rw 4 (q7 c4) ∷
   rw 3 (q169 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 1 (q33 c4) ∷
   rw 2 (q122 c4) ∷
   rw⁻ 3 (q31 c4) ∷
   rw 0 (q29 c4) ∷
   rw 2 (q30 c4) ∷ []) Eq.refl

private
  q170 : Ws → Eqn
  q170 c4 = wlE 347 (lit c4)
  q171 : Ws → Eqn
  q171 c4 = wlE 348 (lit c4)
  q172 : Ws → Eqn
  q172 c4 = wpE 3 c4
  q173 : Ws → Eqn
  q173 c4 = wpE 221 c4
  q174 : Ws → Eqn
  q174 c4 = sE 199 (lem-comm-CSd12-CCZ034 c4)
  q175 : Ws → Eqn
  q175 c4 = sE 191 (lem-comm-CS12-CCZ034 c4)
  q176 : Ws → Eqn
  q176 c4 = wpE 222 c4
  q177 : Ws → Eqn
  q177 c4 = wlE 349 (lit c4)
  q178 : Ws → Eqn
  q178 c4 = wlE 350 (lit c4)

-- Su-box: 17 steps
lem-Su-box : Ws → ⟪ (ℓ "上亹") ⟫ʷ ≈ ⟪ (ℓ "亹上") ⟫ʷ
lem-Su-box c4 = derive (ℓ "上亹") (ℓ "亹上")
  (rw 1 (q55 c4) ∷
   rw 0 (q170 c4) ∷
   rw 3 (q171 c4) ∷
   rw⁻ 7 (q172 c4) ∷
   rw⁻ 6 (q173 c4) ∷
   rw 5 (q174 c4) ∷
   rw⁻ 4 (q173 c4) ∷
   rw 3 (q175 c4) ∷
   rw⁻ 4 (q171 c4) ∷
   rw 2 (q175 c4) ∷
   rw⁻ 1 (q176 c4) ∷
   rw 4 (q14 c4) ∷
   rw 3 (q177 c4) ∷
   rw 2 (q170 c4) ∷
   rw 3 (q178 c4) ∷
   rw⁻ 3 (q176 c4) ∷
   rw⁻ 0 (q55 c4) ∷ []) Eq.refl

private
  q179 : Ws → Eqn
  q179 c4 = wlE 351 (lit c4)
  q180 : Ws → Eqn
  q180 c4 = wpE 223 c4
  q181 : Ws → Eqn
  q181 c4 = wlE 352 (lit c4)
  q182 : Ws → Eqn
  q182 c4 = wlE 353 (lit c4)

-- Sdu-box: 17 steps
lem-Sdu-box : Ws → ⟪ (ℓ "下亹") ⟫ʷ ≈ ⟪ (ℓ "亹下") ⟫ʷ
lem-Sdu-box c4 = derive (ℓ "下亹") (ℓ "亹下")
  (rw 1 (q55 c4) ∷
   rw 0 (q179 c4) ∷
   rw 3 (q171 c4) ∷
   rw⁻ 7 (q172 c4) ∷
   rw⁻ 6 (q173 c4) ∷
   rw 5 (q174 c4) ∷
   rw⁻ 4 (q173 c4) ∷
   rw 3 (q175 c4) ∷
   rw⁻ 4 (q171 c4) ∷
   rw 2 (q174 c4) ∷
   rw⁻ 1 (q180 c4) ∷
   rw 4 (q14 c4) ∷
   rw 3 (q181 c4) ∷
   rw 2 (q179 c4) ∷
   rw 3 (q182 c4) ∷
   rw⁻ 3 (q180 c4) ∷
   rw⁻ 0 (q55 c4) ∷ []) Eq.refl

private
  q183 : Ws → Eqn
  q183 c4 = wlE 354 (lit c4)
  q184 : Ws → Eqn
  q184 c4 = wpE 1 c4
  q185 : Ws → Eqn
  q185 c4 = wlE 355 (lit c4)

-- CSu-box-1: 17 steps
lem-CSu-box-1 : Ws → ⟪ (ℓ "丨亹") ⟫ʷ ≈ ⟪ (ℓ "亹丨") ⟫ʷ
lem-CSu-box-1 c4 = derive (ℓ "丨亹") (ℓ "亹丨")
  (rw 1 (q55 c4) ∷
   rw 0 (q183 c4) ∷
   rw 3 (q171 c4) ∷
   rw⁻ 7 (q172 c4) ∷
   rw⁻ 6 (q173 c4) ∷
   rw 5 (q174 c4) ∷
   rw⁻ 4 (q173 c4) ∷
   rw 3 (q175 c4) ∷
   rw⁻ 4 (q171 c4) ∷
   rw 2 (q175 c4) ∷
   rw⁻ 1 (q184 c4) ∷
   rw 4 (q14 c4) ∷
   rw 3 (q177 c4) ∷
   rw 2 (q183 c4) ∷
   rw 3 (q185 c4) ∷
   rw⁻ 3 (q184 c4) ∷
   rw⁻ 0 (q55 c4) ∷ []) Eq.refl

private
  q186 : Ws → Eqn
  q186 c4 = wlE 356 (lit c4)
  q187 : Ws → Eqn
  q187 c4 = wpE 120 c4
  q188 : Ws → Eqn
  q188 c4 = wlE 357 (lit c4)

-- CSdu-box-1: 17 steps
lem-CSdu-box-1 : Ws → ⟪ (ℓ "丩亹") ⟫ʷ ≈ ⟪ (ℓ "亹丩") ⟫ʷ
lem-CSdu-box-1 c4 = derive (ℓ "丩亹") (ℓ "亹丩")
  (rw 1 (q55 c4) ∷
   rw 0 (q186 c4) ∷
   rw 3 (q171 c4) ∷
   rw⁻ 7 (q172 c4) ∷
   rw⁻ 6 (q173 c4) ∷
   rw 5 (q174 c4) ∷
   rw⁻ 4 (q173 c4) ∷
   rw 3 (q175 c4) ∷
   rw⁻ 4 (q171 c4) ∷
   rw 2 (q174 c4) ∷
   rw⁻ 1 (q187 c4) ∷
   rw 4 (q14 c4) ∷
   rw 3 (q181 c4) ∷
   rw 2 (q186 c4) ∷
   rw 3 (q188 c4) ∷
   rw⁻ 3 (q187 c4) ∷
   rw⁻ 0 (q55 c4) ∷ []) Eq.refl

private
  q189 : Ws → Eqn
  q189 c4 = wlE 358 (lit c4)
  q190 : Ws → Eqn
  q190 c4 = sE 65 (lem-comm-CZ12-CCZ034 c4)
  q191 : Ws → Eqn
  q191 c4 = wpE 224 c4
  q192 : Ws → Eqn
  q192 c4 = wlE 359 (lit c4)
  q193 : Ws → Eqn
  q193 c4 = wlE 360 (lit c4)

-- CZu-box-1: 9 steps
lem-CZu-box-1 : Ws → ⟪ (ℓ "个亹") ⟫ʷ ≈ ⟪ (ℓ "亹个") ⟫ʷ
lem-CZu-box-1 c4 = derive (ℓ "个亹") (ℓ "亹个")
  (rw 1 (q55 c4) ∷
   rw 0 (q189 c4) ∷
   rw 2 (q190 c4) ∷
   rw⁻ 1 (q191 c4) ∷
   rw 3 (q192 c4) ∷
   rw 2 (q189 c4) ∷
   rw 3 (q193 c4) ∷
   rw⁻ 3 (q191 c4) ∷
   rw⁻ 0 (q55 c4) ∷ []) Eq.refl

private
  q194 : Ws → Eqn
  q194 c4 = wlE 361 (lit c4)
  q195 : Ws → Eqn
  q195 c4 = wpE 225 c4
  q196 : Ws → Eqn
  q196 c4 = wpE 226 c4

-- CXu-box-1: 15 steps
lem-CXu-box-1 : Ws → ⟪ (ℓ "乄亹") ⟫ʷ ≈ ⟪ (ℓ "亹乄") ⟫ʷ
lem-CXu-box-1 c4 = derive (ℓ "乄亹") (ℓ "亹乄")
  (rw 1 (q55 c4) ∷
   rw 0 (q194 c4) ∷
   rw⁻ 1 (q195 c4) ∷
   rw 3 (q59 c4) ∷
   rw 7 (q60 c4) ∷
   rw 6 (q61 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw 4 (q61 c4) ∷
   rw⁻ 3 (q62 c4) ∷
   rw⁻ 4 (q59 c4) ∷
   rw 2 (q194 c4) ∷
   rw⁻ 4 (q65 c4) ∷
   rw⁻ 3 (q195 c4) ∷
   rw 4 (q196 c4) ∷
   rw⁻ 0 (q55 c4) ∷ []) Eq.refl

private
  q197 : Ws → Eqn
  q197 c4 = wlE 368 (lit c4)
  q198 : Ws → Eqn
  q198 c4 = wlE 369 (lit c4)

-- CSu-box-2: 17 steps
lem-CSu-box-2 : Ws → ⟪ (ℓ "丯亹") ⟫ʷ ≈ ⟪ (ℓ "亹丯") ⟫ʷ
lem-CSu-box-2 c4 = derive (ℓ "丯亹") (ℓ "亹丯")
  (rw 1 (q55 c4) ∷
   rw 0 (q197 c4) ∷
   rw 3 (q171 c4) ∷
   rw⁻ 7 (q172 c4) ∷
   rw⁻ 6 (q173 c4) ∷
   rw 5 (q174 c4) ∷
   rw⁻ 4 (q173 c4) ∷
   rw 3 (q175 c4) ∷
   rw⁻ 4 (q171 c4) ∷
   rw 2 (q175 c4) ∷
   rw⁻ 1 (q172 c4) ∷
   rw 4 (q14 c4) ∷
   rw 3 (q177 c4) ∷
   rw 2 (q197 c4) ∷
   rw 3 (q198 c4) ∷
   rw⁻ 3 (q172 c4) ∷
   rw⁻ 0 (q55 c4) ∷ []) Eq.refl

private
  q199 : Ws → Eqn
  q199 c4 = wlE 370 (lit c4)
  q200 : Ws → Eqn
  q200 c4 = wpE 2 c4
  q201 : Ws → Eqn
  q201 c4 = wlE 371 (lit c4)

-- CSdu-box-2: 17 steps
lem-CSdu-box-2 : Ws → ⟪ (ℓ "丰亹") ⟫ʷ ≈ ⟪ (ℓ "亹丰") ⟫ʷ
lem-CSdu-box-2 c4 = derive (ℓ "丰亹") (ℓ "亹丰")
  (rw 1 (q55 c4) ∷
   rw 0 (q199 c4) ∷
   rw 3 (q171 c4) ∷
   rw⁻ 7 (q172 c4) ∷
   rw⁻ 6 (q173 c4) ∷
   rw 5 (q174 c4) ∷
   rw⁻ 4 (q173 c4) ∷
   rw 3 (q175 c4) ∷
   rw⁻ 4 (q171 c4) ∷
   rw 2 (q174 c4) ∷
   rw⁻ 1 (q200 c4) ∷
   rw 4 (q14 c4) ∷
   rw 3 (q181 c4) ∷
   rw 2 (q199 c4) ∷
   rw 3 (q201 c4) ∷
   rw⁻ 3 (q200 c4) ∷
   rw⁻ 0 (q55 c4) ∷ []) Eq.refl

private
  q202 : Ws → Eqn
  q202 c4 = wlE 372 (lit c4)
  q203 : Ws → Eqn
  q203 c4 = wpE 227 c4
  q204 : Ws → Eqn
  q204 c4 = wlE 373 (lit c4)

-- CZu-box-2: 9 steps
lem-CZu-box-2 : Ws → ⟪ (ℓ "丱亹") ⟫ʷ ≈ ⟪ (ℓ "亹丱") ⟫ʷ
lem-CZu-box-2 c4 = derive (ℓ "丱亹") (ℓ "亹丱")
  (rw 1 (q55 c4) ∷
   rw 0 (q202 c4) ∷
   rw 2 (q190 c4) ∷
   rw⁻ 1 (q203 c4) ∷
   rw 3 (q192 c4) ∷
   rw 2 (q202 c4) ∷
   rw 3 (q204 c4) ∷
   rw⁻ 3 (q203 c4) ∷
   rw⁻ 0 (q55 c4) ∷ []) Eq.refl

private
  q205 : Ws → Eqn
  q205 c4 = wlE 374 (lit c4)
  q206 : Ws → Eqn
  q206 c4 = wpE 228 c4
  q207 : Ws → Eqn
  q207 c4 = wpE 229 c4

-- CXu-box-2: 15 steps
lem-CXu-box-2 : Ws → ⟪ (ℓ "乜亹") ⟫ʷ ≈ ⟪ (ℓ "亹乜") ⟫ʷ
lem-CXu-box-2 c4 = derive (ℓ "乜亹") (ℓ "亹乜")
  (rw 1 (q55 c4) ∷
   rw 0 (q205 c4) ∷
   rw⁻ 1 (q206 c4) ∷
   rw 3 (q94 c4) ∷
   rw 7 (q95 c4) ∷
   rw 6 (q67 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw 4 (q67 c4) ∷
   rw⁻ 3 (q62 c4) ∷
   rw⁻ 4 (q94 c4) ∷
   rw 2 (q205 c4) ∷
   rw⁻ 4 (q98 c4) ∷
   rw⁻ 3 (q206 c4) ∷
   rw 4 (q207 c4) ∷
   rw⁻ 0 (q55 c4) ∷ []) Eq.refl

private
  q208 : Ws → Eqn
  q208 c4 = wlE 397 (lit c4)
  q209 : Ws → Eqn
  q209 c4 = wlE 398 (lit c4)
  q210 : Ws → Eqn
  q210 c4 = eqn (ℓ "丑乺") (ℓ "乺丑") (c₂ ((S • S • S) ↑) ((CS • CS • CS) ↑))
  q211 : Ws → Eqn
  q211 c4 = eqn (ℓ "于乺") (ℓ "乺于") (c₃ (K ↑ • CCZ • K ↑ • iI) (CS • CS • CS))
  q212 : Ws → Eqn
  q212 c4 = eqn (ℓ "丐乺") (ℓ "乺丐") (c₂ (S ↑) ((CS • CS • CS) ↑))
  q213 : Ws → Eqn
  q213 c4 = eqn (ℓ "丰乺") (ℓ "乺丰") (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (CS • CS • CS))
  q214 : Ws → Eqn
  q214 c4 = wlE 399 (lit c4)
  q215 : Ws → Eqn
  q215 c4 = sE 266 (lem-tP-at0110 c4)
  q216 : Ws → Eqn
  q216 c4 = wlE 400 (lit c4)
  q217 : Ws → Eqn
  q217 c4 = sE 196 (lem-comm-CSd02-TOFF134 c4)
  q218 : Ws → Eqn
  q218 c4 = wlE 401 (lit c4)

-- VPQ @0110: 14 steps
lem-VPQ-at0110 : Ws → ⟪ (ℓ "于二亭京") ⟫ʷ ≈ ⟪ (ℓ "亭京于二") ⟫ʷ
lem-VPQ-at0110 c4 = derive (ℓ "于二亭京") (ℓ "亭京于二")
  (rw⁻ 0 (q208 c4) ∷
   rw⁻ 4 (q209 c4) ∷
   rw 3 (q210 c4) ∷
   rw 2 (q211 c4) ∷
   rw 1 (q212 c4) ∷
   rw 0 (q213 c4) ∷
   rw 4 (q214 c4) ∷
   rw 3 (q215 c4) ∷
   rw⁻ 4 (q214 c4) ∷
   rw 1 (q216 c4) ∷
   rw 2 (q217 c4) ∷
   rw 3 (q218 c4) ∷
   rw 0 (q209 c4) ∷
   rw 2 (q208 c4) ∷ []) Eq.refl

private
  q219 : Ws → Eqn
  q219 c4 = sE 261 (lem-box-tQ-at133441 c4)
  q220 : Ws → Eqn
  q220 c4 = wpE 263 c4
  q221 : Ws → Eqn
  q221 c4 = wpE 264 c4
  q222 : Ws → Eqn
  q222 c4 = wlE 404 (lit c4)
  q223 : Ws → Eqn
  q223 c4 = wlE 314 (lit c4)
  q224 : Ws → Eqn
  q224 c4 = wpE 53 c4
  q225 : Ws → Eqn
  q225 c4 = sE 9 (lem-comm-CX32-CCZ014 c4)
  q226 : Ws → Eqn
  q226 c4 = wpE 265 c4
  q227 : Ws → Eqn
  q227 c4 = wpE 67 c4
  q228 : Ws → Eqn
  q228 c4 = wpE 167 c4
  q229 : Ws → Eqn
  q229 c4 = wpE 266 c4
  q230 : Ws → Eqn
  q230 c4 = wlE 315 (lit c4)

-- CXbc-box @133441: 17 steps
lem-CXbc-box-at133441 : Ws → ⟪ (ℓ "乭仰乭") ⟫ʷ ≈ ⟪ (ℓ "仰交") ⟫ʷ
lem-CXbc-box-at133441 c4 = derive (ℓ "乭仰乭") (ℓ "仰交")
  (rw 1 (q219 c4) ∷
   rw 0 (q220 c4) ∷
   rw⁻ 1 (q221 c4) ∷
   rw 3 (q222 c4) ∷
   rw 2 (q220 c4) ∷
   rw 5 (q223 c4) ∷
   rw⁻ 9 (q224 c4) ∷
   rw 8 (q225 c4) ∷
   rw⁻ 7 (q226 c4) ∷
   rw 6 (q225 c4) ∷
   rw⁻ 5 (q227 c4) ∷
   rw⁻ 6 (q223 c4) ∷
   rw 4 (q228 c4) ∷
   rw⁻ 3 (q221 c4) ∷
   rw 4 (q229 c4) ∷
   rw⁻ 0 (q219 c4) ∷
   rw⁻ 1 (q230 c4) ∷ []) Eq.refl

private
  q231 : Ws → Eqn
  q231 c4 = wpE 267 c4
  q232 : Ws → Eqn
  q232 c4 = wpE 268 c4
  q233 : Ws → Eqn
  q233 c4 = wpE 269 c4
  q234 : Ws → Eqn
  q234 c4 = wlE 310 (lit c4)
  q235 : Ws → Eqn
  q235 c4 = wlE 222 (lit c4)
  q236 : Ws → Eqn
  q236 c4 = wpE 270 c4
  q237 : Ws → Eqn
  q237 c4 = sE 193 (lem-comm-CS14-TOFF023 c4)
  q238 : Ws → Eqn
  q238 c4 = wpE 173 c4
  q239 : Ws → Eqn
  q239 c4 = wpE 271 c4
  q240 : Ws → Eqn
  q240 c4 = wpE 272 c4
  q241 : Ws → Eqn
  q241 c4 = wlE 312 (lit c4)

-- CXcb-box @133441: 18 steps
lem-CXcb-box-at133441 : Ws → ⟪ (ℓ "了仰了") ⟫ʷ ≈ ⟪ (ℓ "仰京") ⟫ʷ
lem-CXcb-box-at133441 c4 = derive (ℓ "了仰了") (ℓ "仰京")
  (rw 1 (q219 c4) ∷
   rw 0 (q231 c4) ∷
   rw⁻ 2 (q232 c4) ∷
   rw⁻ 1 (q233 c4) ∷
   rw 4 (q234 c4) ∷
   rw 8 (q235 c4) ∷
   rw 7 (q236 c4) ∷
   rw 6 (q37 c4) ∷
   rw 5 (q236 c4) ∷
   rw 4 (q237 c4) ∷
   rw⁻ 5 (q234 c4) ∷
   rw⁻ 3 (q238 c4) ∷
   rw 2 (q231 c4) ∷
   rw 3 (q239 c4) ∷
   rw⁻ 4 (q240 c4) ∷
   rw⁻ 3 (q233 c4) ∷
   rw⁻ 0 (q219 c4) ∷
   rw⁻ 1 (q241 c4) ∷ []) Eq.refl

private
  q242 : Ws → Eqn
  q242 c4 = sE 245 (lem-VPQ-at13243241 c4)

-- QVQ @13243241: 3 steps
lem-QVQ-at13243241 : Ws → ⟪ (ℓ "二亡亠二") ⟫ʷ ≈ ⟪ (ℓ "亍亡亠亍") ⟫ʷ
lem-QVQ-at13243241 c4 = derive (ℓ "二亡亠二") (ℓ "亍亡亠亍")
  (rw⁻ 0 (q163 c4) ∷
   rw⁻ 1 (q242 c4) ∷
   rw 4 (q165 c4) ∷ []) Eq.refl

private
  q243 : Ws → Eqn
  q243 c4 = wlE 420 (lit c4)
  q244 : Ws → Eqn
  q244 c4 = sE 240 (lem-VPQ-at021021 c4)

-- QVQ @021021: 3 steps
lem-QVQ-at021021 : Ws → ⟪ (ℓ "亰亏二亰") ⟫ʷ ≈ ⟪ (ℓ "亱亏二亱") ⟫ʷ
lem-QVQ-at021021 c4 = derive (ℓ "亰亏二亰") (ℓ "亱亏二亱")
  (rw⁻ 0 (q243 c4) ∷
   rw⁻ 1 (q244 c4) ∷
   rw 4 (q115 c4) ∷ []) Eq.refl

private
  q245 : Ws → Eqn
  q245 c4 = wpE 281 c4
  q246 : Ws → Eqn
  q246 c4 = wpE 282 c4
  q247 : Ws → Eqn
  q247 c4 = wlE 422 (lit c4)
  q248 : Ws → Eqn
  q248 c4 = wlE 297 (lit c4)
  q249 : Ws → Eqn
  q249 c4 = wpE 92 c4
  q250 : Ws → Eqn
  q250 c4 = sE 8 (lem-comm-CX31-CCZ024 c4)
  q251 : Ws → Eqn
  q251 c4 = wpE 87 c4
  q252 : Ws → Eqn
  q252 c4 = wpE 81 c4
  q253 : Ws → Eqn
  q253 c4 = wpE 142 c4
  q254 : Ws → Eqn
  q254 c4 = wpE 283 c4

-- CXbc-box @13213442: 17 steps
lem-CXbc-box-at13213442 : Ws → ⟪ (ℓ "乙仩乙") ⟫ʷ ≈ ⟪ (ℓ "仩交") ⟫ʷ
lem-CXbc-box-at13213442 c4 = derive (ℓ "乙仩乙") (ℓ "仩交")
  (rw 1 (q166 c4) ∷
   rw 0 (q245 c4) ∷
   rw⁻ 1 (q246 c4) ∷
   rw 3 (q247 c4) ∷
   rw 2 (q245 c4) ∷
   rw 5 (q248 c4) ∷
   rw⁻ 9 (q249 c4) ∷
   rw 8 (q250 c4) ∷
   rw⁻ 7 (q251 c4) ∷
   rw 6 (q250 c4) ∷
   rw⁻ 5 (q252 c4) ∷
   rw⁻ 6 (q248 c4) ∷
   rw 4 (q253 c4) ∷
   rw⁻ 3 (q246 c4) ∷
   rw 4 (q254 c4) ∷
   rw⁻ 0 (q166 c4) ∷
   rw⁻ 1 (q155 c4) ∷ []) Eq.refl

private
  q255 : Ws → Eqn
  q255 c4 = wpE 284 c4
  q256 : Ws → Eqn
  q256 c4 = wpE 96 c4
  q257 : Ws → Eqn
  q257 c4 = wpE 285 c4
  q258 : Ws → Eqn
  q258 c4 = wlE 293 (lit c4)
  q259 : Ws → Eqn
  q259 c4 = wlE 246 (lit c4)
  q260 : Ws → Eqn
  q260 c4 = wpE 286 c4
  q261 : Ws → Eqn
  q261 c4 = sE 195 (lem-comm-CS24-TOFF013 c4)
  q262 : Ws → Eqn
  q262 c4 = wpE 97 c4
  q263 : Ws → Eqn
  q263 c4 = wpE 287 c4
  q264 : Ws → Eqn
  q264 c4 = wpE 90 c4

-- CXcb-box @13213442: 18 steps
lem-CXcb-box-at13213442 : Ws → ⟪ (ℓ "亃仩亃") ⟫ʷ ≈ ⟪ (ℓ "仩亰") ⟫ʷ
lem-CXcb-box-at13213442 c4 = derive (ℓ "亃仩亃") (ℓ "仩亰")
  (rw 1 (q166 c4) ∷
   rw 0 (q255 c4) ∷
   rw⁻ 2 (q256 c4) ∷
   rw⁻ 1 (q257 c4) ∷
   rw 4 (q258 c4) ∷
   rw 8 (q259 c4) ∷
   rw 7 (q260 c4) ∷
   rw 6 (q50 c4) ∷
   rw 5 (q260 c4) ∷
   rw 4 (q261 c4) ∷
   rw⁻ 5 (q258 c4) ∷
   rw⁻ 3 (q262 c4) ∷
   rw 2 (q255 c4) ∷
   rw 3 (q263 c4) ∷
   rw⁻ 4 (q264 c4) ∷
   rw⁻ 3 (q257 c4) ∷
   rw⁻ 0 (q166 c4) ∷
   rw⁻ 1 (q144 c4) ∷ []) Eq.refl

private
  q265 : Ws → Eqn
  q265 c4 = sE 244 (lem-VPQ-at13243142 c4)

-- QVQ @13243142: 3 steps
lem-QVQ-at13243142 : Ws → ⟪ (ℓ "二亡亠二") ⟫ʷ ≈ ⟪ (ℓ "亍亡亠亍") ⟫ʷ
lem-QVQ-at13243142 c4 = derive (ℓ "二亡亠二") (ℓ "亍亡亠亍")
  (rw⁻ 0 (q163 c4) ∷
   rw⁻ 1 (q265 c4) ∷
   rw 4 (q165 c4) ∷ []) Eq.refl

private
  q266 : Ws → Eqn
  q266 c4 = wlE 442 (lit c4)
  q267 : Ws → Eqn
  q267 c4 = sE 241 (lem-VPQ-at03102132 c4)

-- QVQ @03102132: 3 steps
lem-QVQ-at03102132 : Ws → ⟪ (ℓ "亰亓亐亰") ⟫ʷ ≈ ⟪ (ℓ "亲亓亐亲") ⟫ʷ
lem-QVQ-at03102132 c4 = derive (ℓ "亰亓亐亰") (ℓ "亲亓亐亲")
  (rw⁻ 0 (q266 c4) ∷
   rw⁻ 1 (q267 c4) ∷
   rw 4 (q115 c4) ∷ []) Eq.refl

private
  q268 : Ws → Eqn
  q268 c4 = sE 264 (lem-box-tQ-at3443 c4)
  q269 : Ws → Eqn
  q269 c4 = sE 281 (lem-tP-at3443 c4)

-- P-box @3443: 8 steps
lem-P-box-at3443 : Ws → ⟪ (ℓ "亡亼亡") ⟫ʷ ≈ ⟪ (ℓ "亼") ⟫ʷ
lem-P-box-at3443 c4 = derive (ℓ "亡亼亡") (ℓ "亼")
  (rw 1 (q268 c4) ∷
   rw⁻ 0 (q269 c4) ∷
   rw⁻ 1 (q78 c4) ∷
   rw⁻ 3 (q269 c4) ∷
   rw⁻ 4 (q79 c4) ∷
   rw⁻ 2 (q80 c4) ∷
   rw⁻ 3 (q81 c4) ∷
   rw⁻ 0 (q268 c4) ∷ []) Eq.refl

-- VPQ @3443: 14 steps
lem-VPQ-at3443 : Ws → ⟪ (ℓ "亍二亡亠") ⟫ʷ ≈ ⟪ (ℓ "亡亠亍二") ⟫ʷ
lem-VPQ-at3443 c4 = derive (ℓ "亍二亡亠") (ℓ "亡亠亍二")
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw 3 (q3 c4) ∷
   rw 2 (q4 c4) ∷
   rw 1 (q5 c4) ∷
   rw 0 (q6 c4) ∷
   rw 4 (q7 c4) ∷
   rw 3 (q269 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   rw 2 (q10 c4) ∷
   rw⁻ 3 (q11 c4) ∷
   rw 0 (q2 c4) ∷
   rw 2 (q1 c4) ∷ []) Eq.refl

private
  q270 : Ws → Eqn
  q270 c4 = wlE 457 (lit c4)
  q271 : Ws → Eqn
  q271 c4 = sE 242 (lem-VPQ-at0410213243 c4)

-- QVQ @0410213243: 3 steps
lem-QVQ-at0410213243 : Ws → ⟪ (ℓ "亰亗五亰") ⟫ʷ ≈ ⟪ (ℓ "亳亗五亳") ⟫ʷ
lem-QVQ-at0410213243 c4 = derive (ℓ "亰亗五亰") (ℓ "亳亗五亳")
  (rw⁻ 0 (q270 c4) ∷
   rw⁻ 1 (q271 c4) ∷
   rw 4 (q115 c4) ∷ []) Eq.refl

private
  q272 : Ws → Eqn
  q272 c4 = wlE 468 (lit c4)
  q273 : Ws → Eqn
  q273 c4 = wpE 316 c4
  q274 : Ws → Eqn
  q274 c4 = eqn (ℓ "丷丣") (ℓ "丣丷") (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S • S • S))
  q275 : Ws → Eqn
  q275 c4 = sE 215 (lem-comm-TOFF412-CSd03 c4)
  q276 : Ws → Eqn
  q276 c4 = eqn (ℓ "丷丢") (ℓ "丢丷") (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S))
  q277 : Ws → Eqn
  q277 c4 = wlE 469 (lit c4)
  q278 : Ws → Eqn
  q278 c4 = wlE 456 (lit c4)
  q279 : Ws → Eqn
  q279 c4 = sE 272 (lem-tP-at043043 c4)
  q280 : Ws → Eqn
  q280 c4 = eqn (ℓ "么丢") (ℓ "丢么") (c₃ ((CS • CS • CS) ↑) (S ↑))
  q281 : Ws → Eqn
  q281 c4 = sE 200 (lem-comm-CSd12-TOFF403 c4)
  q282 : Ws → Eqn
  q282 c4 = eqn (ℓ "么丣") (ℓ "丣么") (c₃ ((CS • CS • CS) ↑) ((S • S • S) ↑))

-- VPQ @043043: 14 steps
lem-VPQ-at043043 : Ws → ⟪ (ℓ "享亨亣亠") ⟫ʷ ≈ ⟪ (ℓ "亣亠享亨") ⟫ʷ
lem-VPQ-at043043 c4 = derive (ℓ "享亨亣亠") (ℓ "亣亠享亨")
  (rw⁻ 0 (q272 c4) ∷
   rw⁻ 4 (q273 c4) ∷
   rw⁻ 3 (q274 c4) ∷
   rw 2 (q275 c4) ∷
   rw⁻ 1 (q276 c4) ∷
   rw⁻ 0 (q277 c4) ∷
   rw 4 (q278 c4) ∷
   rw 3 (q279 c4) ∷
   rw⁻ 4 (q278 c4) ∷
   rw 1 (q280 c4) ∷
   rw 2 (q281 c4) ∷
   rw 3 (q282 c4) ∷
   rw 0 (q273 c4) ∷
   rw 2 (q272 c4) ∷ []) Eq.refl

private
  q283 : Ws → Eqn
  q283 c4 = sE 253 (lem-box-tQ-at043043 c4)
  q284 : Ws → Eqn
  q284 c4 = wpE 330 c4
  q285 : Ws → Eqn
  q285 c4 = wlE 475 (lit c4)
  q286 : Ws → Eqn
  q286 c4 = wlE 207 (lit c4)
  q287 : Ws → Eqn
  q287 c4 = wpE 312 c4
  q288 : Ws → Eqn
  q288 c4 = wpE 313 c4
  q289 : Ws → Eqn
  q289 c4 = wpE 314 c4
  q290 : Ws → Eqn
  q290 c4 = wlE 476 (lit c4)

-- CXbc-box @043043: 17 steps
lem-CXbc-box-at043043 : Ws → ⟪ (ℓ "乜侓乜") ⟫ʷ ≈ ⟪ (ℓ "侓交") ⟫ʷ
lem-CXbc-box-at043043 c4 = derive (ℓ "乜侓乜") (ℓ "侓交")
  (rw 1 (q283 c4) ∷
   rw 0 (q284 c4) ∷
   rw⁻ 1 (q206 c4) ∷
   rw 3 (q285 c4) ∷
   rw 2 (q284 c4) ∷
   rw 5 (q286 c4) ∷
   rw⁻ 9 (q287 c4) ∷
   rw 8 (q72 c4) ∷
   rw⁻ 7 (q288 c4) ∷
   rw 6 (q72 c4) ∷
   rw⁻ 5 (q289 c4) ∷
   rw⁻ 6 (q286 c4) ∷
   rw⁻ 4 (q98 c4) ∷
   rw⁻ 3 (q206 c4) ∷
   rw 4 (q207 c4) ∷
   rw⁻ 0 (q283 c4) ∷
   rw⁻ 1 (q290 c4) ∷ []) Eq.refl

private
  q291 : Ws → Eqn
  q291 c4 = wpE 331 c4
  q292 : Ws → Eqn
  q292 c4 = wpE 332 c4
  q293 : Ws → Eqn
  q293 c4 = wpE 333 c4
  q294 : Ws → Eqn
  q294 c4 = wlE 477 (lit c4)
  q295 : Ws → Eqn
  q295 c4 = wlE 478 (lit c4)
  q296 : Ws → Eqn
  q296 c4 = wpE 334 c4
  q297 : Ws → Eqn
  q297 c4 = sE 197 (lem-comm-CSd03-TOFF412 c4)
  q298 : Ws → Eqn
  q298 c4 = sE 190 (lem-comm-CS03-TOFF412 c4)
  q299 : Ws → Eqn
  q299 c4 = wpE 335 c4
  q300 : Ws → Eqn
  q300 c4 = wpE 336 c4
  q301 : Ws → Eqn
  q301 c4 = wlE 479 (lit c4)

-- CXcb-box @043043: 18 steps
lem-CXcb-box-at043043 : Ws → ⟪ (ℓ "丳侓丳") ⟫ʷ ≈ ⟪ (ℓ "侓亐") ⟫ʷ
lem-CXcb-box-at043043 c4 = derive (ℓ "丳侓丳") (ℓ "侓亐")
  (rw 1 (q283 c4) ∷
   rw 0 (q291 c4) ∷
   rw⁻ 2 (q292 c4) ∷
   rw⁻ 1 (q293 c4) ∷
   rw 4 (q294 c4) ∷
   rw 8 (q295 c4) ∷
   rw 7 (q296 c4) ∷
   rw 6 (q297 c4) ∷
   rw 5 (q296 c4) ∷
   rw 4 (q298 c4) ∷
   rw⁻ 5 (q294 c4) ∷
   rw 3 (q299 c4) ∷
   rw 2 (q291 c4) ∷
   rw 3 (q300 c4) ∷
   rw 4 (q142 c4) ∷
   rw⁻ 3 (q293 c4) ∷
   rw⁻ 0 (q283 c4) ∷
   rw⁻ 1 (q301 c4) ∷ []) Eq.refl

private
  q302 : Ws → Eqn
  q302 c4 = sE 243 (lem-VPQ-at04203243 c4)

-- QVQ @04203243: 3 steps
lem-QVQ-at04203243 : Ws → ⟪ (ℓ "亰亗五亰") ⟫ʷ ≈ ⟪ (ℓ "亳亗五亳") ⟫ʷ
lem-QVQ-at04203243 c4 = derive (ℓ "亰亗五亰") (ℓ "亳亗五亳")
  (rw⁻ 0 (q270 c4) ∷
   rw⁻ 1 (q302 c4) ∷
   rw 4 (q115 c4) ∷ []) Eq.refl

private
  q303 : Ws → Eqn
  q303 c4 = sE 252 (lem-box-tQ-at0330 c4)
  q304 : Ws → Eqn
  q304 c4 = sE 271 (lem-tP-at0330 c4)
  q305 : Ws → Eqn
  q305 c4 = wpE 344 c4
  q306 : Ws → Eqn
  q306 c4 = wpE 345 c4
  q307 : Ws → Eqn
  q307 c4 = sE 207 (lem-comm-CZ04-TOFF312 c4)
  q308 : Ws → Eqn
  q308 c4 = wpE 346 c4

-- P-box @0330: 8 steps
lem-P-box-at0330 : Ws → ⟪ (ℓ "亢佬亢") ⟫ʷ ≈ ⟪ (ℓ "佬") ⟫ʷ
lem-P-box-at0330 c4 = derive (ℓ "亢佬亢") (ℓ "佬")
  (rw 1 (q303 c4) ∷
   rw⁻ 0 (q304 c4) ∷
   rw⁻ 1 (q305 c4) ∷
   rw⁻ 3 (q304 c4) ∷
   rw⁻ 4 (q306 c4) ∷
   rw 2 (q307 c4) ∷
   rw⁻ 3 (q308 c4) ∷
   rw⁻ 0 (q303 c4) ∷ []) Eq.refl

private
  q309 : Ws → Eqn
  q309 c4 = wlE 488 (lit c4)
  q310 : Ws → Eqn
  q310 c4 = wpE 347 c4
  q311 : Ws → Eqn
  q311 c4 = wpE 348 c4
  q312 : Ws → Eqn
  q312 c4 = sE 214 (lem-comm-TOFF312-CSd04 c4)
  q313 : Ws → Eqn
  q313 c4 = wpE 349 c4
  q314 : Ws → Eqn
  q314 c4 = wpE 350 c4
  q315 : Ws → Eqn
  q315 c4 = wlE 441 (lit c4)
  q316 : Ws → Eqn
  q316 c4 = eqn (ℓ "么东") (ℓ "东么") (c₃ ((CS • CS • CS) ↑) (S))
  q317 : Ws → Eqn
  q317 c4 = sE 222 (lem-comm-CSd12-TOFF304 c4)
  q318 : Ws → Eqn
  q318 c4 = eqn (ℓ "么丝") (ℓ "丝么") (c₃ ((CS • CS • CS) ↑) (S • S • S))

-- VPQ @0330: 14 steps
lem-VPQ-at0330 : Ws → ⟪ (ℓ "产交亢亠") ⟫ʷ ≈ ⟪ (ℓ "亢亠产交") ⟫ʷ
lem-VPQ-at0330 c4 = derive (ℓ "产交亢亠") (ℓ "亢亠产交")
  (rw⁻ 0 (q309 c4) ∷
   rw⁻ 4 (q310 c4) ∷
   rw⁻ 3 (q311 c4) ∷
   rw 2 (q312 c4) ∷
   rw⁻ 1 (q313 c4) ∷
   rw⁻ 0 (q314 c4) ∷
   rw 4 (q315 c4) ∷
   rw 3 (q304 c4) ∷
   rw⁻ 4 (q315 c4) ∷
   rw 1 (q316 c4) ∷
   rw 2 (q317 c4) ∷
   rw 3 (q318 c4) ∷
   rw 0 (q310 c4) ∷
   rw 2 (q309 c4) ∷ []) Eq.refl

private
  q319 : Ws → Eqn
  q319 c4 = sE 228 (lem-comm-TOFF304-CSd12 c4)
  q320 : Ws → Eqn
  q320 c4 = sE 270 (lem-tP-at0314203142 c4)
  q321 : Ws → Eqn
  q321 c4 = sE 221 (lem-comm-CSd04-TOFF312 c4)

-- VPQ @0314203142: 14 steps
lem-VPQ-at0314203142 : Ws → ⟪ (ℓ "亢亠产交") ⟫ʷ ≈ ⟪ (ℓ "产交亢亠") ⟫ʷ
lem-VPQ-at0314203142 c4 = derive (ℓ "亢亠产交") (ℓ "产交亢亠")
  (rw⁻ 0 (q310 c4) ∷
   rw⁻ 4 (q309 c4) ∷
   rw⁻ 3 (q318 c4) ∷
   rw 2 (q319 c4) ∷
   rw⁻ 1 (q316 c4) ∷
   rw 0 (q314 c4) ∷
   rw 4 (q315 c4) ∷
   rw 3 (q320 c4) ∷
   rw⁻ 4 (q315 c4) ∷
   rw 1 (q313 c4) ∷
   rw 2 (q321 c4) ∷
   rw 3 (q311 c4) ∷
   rw 0 (q309 c4) ∷
   rw 2 (q310 c4) ∷ []) Eq.refl

private
  q322 : Ws → Eqn
  q322 c4 = sE 251 (lem-box-tQ-at0310243142 c4)
  q323 : Ws → Eqn
  q323 c4 = sE 269 (lem-tP-at0310243142 c4)
  q324 : Ws → Eqn
  q324 c4 = wlE 504 (lit c4)
  q325 : Ws → Eqn
  q325 c4 = wlE 505 (lit c4)
  q326 : Ws → Eqn
  q326 c4 = sE 226 (lem-comm-CZ12-TOFF304 c4)
  q327 : Ws → Eqn
  q327 c4 = wlE 506 (lit c4)

-- P-box @0310243142: 8 steps
lem-P-box-at0310243142 : Ws → ⟪ (ℓ "产佨产") ⟫ʷ ≈ ⟪ (ℓ "佨") ⟫ʷ
lem-P-box-at0310243142 c4 = derive (ℓ "产佨产") (ℓ "佨")
  (rw 1 (q322 c4) ∷
   rw⁻ 0 (q323 c4) ∷
   rw⁻ 1 (q324 c4) ∷
   rw⁻ 3 (q323 c4) ∷
   rw⁻ 4 (q325 c4) ∷
   rw 2 (q326 c4) ∷
   rw⁻ 3 (q327 c4) ∷
   rw⁻ 0 (q322 c4) ∷ []) Eq.refl

-- VPQ @0310243142: 14 steps
lem-VPQ-at0310243142 : Ws → ⟪ (ℓ "亢亠产交") ⟫ʷ ≈ ⟪ (ℓ "产交亢亠") ⟫ʷ
lem-VPQ-at0310243142 c4 = derive (ℓ "亢亠产交") (ℓ "产交亢亠")
  (rw⁻ 0 (q310 c4) ∷
   rw⁻ 4 (q309 c4) ∷
   rw⁻ 3 (q318 c4) ∷
   rw 2 (q319 c4) ∷
   rw⁻ 1 (q316 c4) ∷
   rw 0 (q314 c4) ∷
   rw 4 (q315 c4) ∷
   rw 3 (q323 c4) ∷
   rw⁻ 4 (q315 c4) ∷
   rw 1 (q313 c4) ∷
   rw 2 (q321 c4) ∷
   rw 3 (q311 c4) ∷
   rw 0 (q309 c4) ∷
   rw 2 (q310 c4) ∷ []) Eq.refl

private
  q328 : Ws → Eqn
  q328 c4 = wlE 509 (lit c4)
  q329 : Ws → Eqn
  q329 c4 = sE 231 (lem-CXbc-box-at04203243 c4)
  q330 : Ws → Eqn
  q330 c4 = wlE 483 (lit c4)
  q331 : Ws → Eqn
  q331 c4 = sE 236 (lem-CXcb-box-at04203243 c4)
  q332 : Ws → Eqn
  q332 c4 = wlE 444 (lit c4)
  q333 : Ws → Eqn
  q333 c4 = wlE 481 (lit c4)
  q334 : Ws → Eqn
  q334 c4 = wlE 510 (lit c4)
  q335 : Ws → Eqn
  q335 c4 = wlE 230 (lit c4)

-- SWbc-box @04203243: 11 steps
lem-SWbc-box-at04203243 : Ws → ⟪ (ℓ "串侒串") ⟫ʷ ≈ ⟪ (ℓ "侒") ⟫ʷ
lem-SWbc-box-at04203243 c4 = derive (ℓ "串侒串") (ℓ "侒")
  (rw⁻ 0 (q328 c4) ∷
   rw⁻ 4 (q328 c4) ∷
   rw 2 (q329 c4) ∷
   rw 3 (q330 c4) ∷
   rw 1 (q331 c4) ∷
   rw 4 (q332 c4) ∷
   rw 3 (q333 c4) ∷
   rw 2 (q333 c4) ∷
   rw 3 (q334 c4) ∷
   rw 0 (q329 c4) ∷
   rw 1 (q335 c4) ∷ []) Eq.refl

private
  q336 : Ws → Eqn
  q336 c4 = sE 230 (lem-CXbc-box-at032032 c4)
  q337 : Ws → Eqn
  q337 c4 = wpE 381 c4
  q338 : Ws → Eqn
  q338 c4 = sE 235 (lem-CXcb-box-at032032 c4)
  q339 : Ws → Eqn
  q339 c4 = wpE 308 c4
  q340 : Ws → Eqn
  q340 c4 = wpE 382 c4
  q341 : Ws → Eqn
  q341 c4 = wpE 383 c4
  q342 : Ws → Eqn
  q342 c4 = wpE 161 c4

-- SWbc-box @032032: 11 steps
lem-SWbc-box-at032032 : Ws → ⟪ (ℓ "串佪串") ⟫ʷ ≈ ⟪ (ℓ "佪") ⟫ʷ
lem-SWbc-box-at032032 c4 = derive (ℓ "串佪串") (ℓ "佪")
  (rw⁻ 0 (q328 c4) ∷
   rw⁻ 4 (q328 c4) ∷
   rw 2 (q336 c4) ∷
   rw 3 (q337 c4) ∷
   rw 1 (q338 c4) ∷
   rw 4 (q339 c4) ∷
   rw 3 (q340 c4) ∷
   rw 2 (q340 c4) ∷
   rw 3 (q341 c4) ∷
   rw 0 (q336 c4) ∷
   rw 1 (q342 c4) ∷ []) Eq.refl

private
  q343 : Ws → Eqn
  q343 c4 = wlE 532 (lit c4)
  q344 : Ws → Eqn
  q344 c4 = sE 227 (lem-comm-CZ12-TOFF403 c4)
  q345 : Ws → Eqn
  q345 c4 = wlE 533 (lit c4)

-- t-cP @043043: 5 steps
lem-t-cP-at043043 : Ws → ⟪ (ℓ "享亨亣亨亣") ⟫ʷ ≈ ⟪ (ℓ "亨亣亨亣享") ⟫ʷ
lem-t-cP-at043043 c4 = derive (ℓ "享亨亣亨亣") (ℓ "亨亣亨亣享")
  (rw⁻ 0 (q343 c4) ∷
   rw 2 (q344 c4) ∷
   rw 1 (q279 c4) ∷
   rw⁻ 2 (q345 c4) ∷
   rw 3 (q279 c4) ∷ []) Eq.refl

private
  q346 : Ws → Eqn
  q346 c4 = wlE 534 (lit c4)
  q347 : Ws → Eqn
  q347 c4 = wlE 535 (lit c4)
  q348 : Ws → Eqn
  q348 c4 = wpE 380 c4

-- CXbc-box @0330: 17 steps
lem-CXbc-box-at0330 : Ws → ⟪ (ℓ "乜佬乜") ⟫ʷ ≈ ⟪ (ℓ "佬亨") ⟫ʷ
lem-CXbc-box-at0330 c4 = derive (ℓ "乜佬乜") (ℓ "佬亨")
  (rw 1 (q303 c4) ∷
   rw 0 (q346 c4) ∷
   rw⁻ 1 (q206 c4) ∷
   rw 3 (q347 c4) ∷
   rw 2 (q346 c4) ∷
   rw 5 (q70 c4) ∷
   rw⁻ 9 (q71 c4) ∷
   rw 8 (q72 c4) ∷
   rw⁻ 7 (q73 c4) ∷
   rw 6 (q72 c4) ∷
   rw⁻ 5 (q74 c4) ∷
   rw⁻ 6 (q70 c4) ∷
   rw⁻ 4 (q98 c4) ∷
   rw⁻ 3 (q206 c4) ∷
   rw 4 (q207 c4) ∷
   rw⁻ 0 (q303 c4) ∷
   rw⁻ 1 (q348 c4) ∷ []) Eq.refl

private
  q349 : Ws → Eqn
  q349 c4 = wlE 536 (lit c4)
  q350 : Ws → Eqn
  q350 c4 = wpE 388 c4
  q351 : Ws → Eqn
  q351 c4 = wpE 341 c4
  q352 : Ws → Eqn
  q352 c4 = wlE 499 (lit c4)
  q353 : Ws → Eqn
  q353 c4 = wlE 537 (lit c4)
  q354 : Ws → Eqn
  q354 c4 = sE 217 (lem-comm-CS04-TOFF312 c4)
  q355 : Ws → Eqn
  q355 c4 = wlE 525 (lit c4)
  q356 : Ws → Eqn
  q356 c4 = wlE 538 (lit c4)
  q357 : Ws → Eqn
  q357 c4 = wpE 378 c4

-- CXcb-box @0330: 18 steps
lem-CXcb-box-at0330 : Ws → ⟪ (ℓ "丳佬丳") ⟫ʷ ≈ ⟪ (ℓ "佬五") ⟫ʷ
lem-CXcb-box-at0330 c4 = derive (ℓ "丳佬丳") (ℓ "佬五")
  (rw 1 (q303 c4) ∷
   rw 0 (q349 c4) ∷
   rw⁻ 2 (q350 c4) ∷
   rw⁻ 1 (q293 c4) ∷
   rw 4 (q351 c4) ∷
   rw 8 (q352 c4) ∷
   rw 7 (q353 c4) ∷
   rw 6 (q321 c4) ∷
   rw 5 (q353 c4) ∷
   rw 4 (q354 c4) ∷
   rw⁻ 5 (q351 c4) ∷
   rw 3 (q355 c4) ∷
   rw 2 (q349 c4) ∷
   rw 3 (q356 c4) ∷
   rw 4 (q88 c4) ∷
   rw⁻ 3 (q293 c4) ∷
   rw⁻ 0 (q303 c4) ∷
   rw⁻ 1 (q357 c4) ∷ []) Eq.refl

private
  q358 : Ws → Eqn
  q358 c4 = sE 263 (lem-box-tQ-at243243 c4)
  q359 : Ws → Eqn
  q359 c4 = wpE 422 c4
  q360 : Ws → Eqn
  q360 c4 = wpE 301 c4
  q361 : Ws → Eqn
  q361 c4 = wpE 48 c4
  q362 : Ws → Eqn
  q362 c4 = wlE 560 (lit c4)
  q363 : Ws → Eqn
  q363 c4 = sE 224 (lem-comm-CSd14-CCZ023 c4)
  q364 : Ws → Eqn
  q364 c4 = sE 219 (lem-comm-CS14-CCZ023 c4)
  q365 : Ws → Eqn
  q365 c4 = wpE 47 c4
  q366 : Ws → Eqn
  q366 c4 = wpE 423 c4
  q367 : Ws → Eqn
  q367 c4 = wpE 424 c4

-- CSdu-box-2 @243243: 17 steps
lem-CSdu-box-2-at243243 : Ws → ⟪ (ℓ "举仄") ⟫ʷ ≈ ⟪ (ℓ "仄举") ⟫ʷ
lem-CSdu-box-2-at243243 c4 = derive (ℓ "举仄") (ℓ "仄举")
  (rw 1 (q358 c4) ∷
   rw 0 (q359 c4) ∷
   rw 3 (q360 c4) ∷
   rw⁻ 7 (q361 c4) ∷
   rw⁻ 6 (q362 c4) ∷
   rw 5 (q363 c4) ∷
   rw⁻ 4 (q362 c4) ∷
   rw 3 (q364 c4) ∷
   rw⁻ 4 (q360 c4) ∷
   rw 2 (q363 c4) ∷
   rw⁻ 1 (q365 c4) ∷
   rw 4 (q41 c4) ∷
   rw 3 (q366 c4) ∷
   rw 2 (q359 c4) ∷
   rw 3 (q367 c4) ∷
   rw⁻ 3 (q365 c4) ∷
   rw⁻ 0 (q358 c4) ∷ []) Eq.refl

private
  q368 : Ws → Eqn
  q368 c4 = wpE 425 c4
  q369 : Ws → Eqn
  q369 c4 = wlE 561 (lit c4)
  q370 : Ws → Eqn
  q370 c4 = wpE 426 c4
  q371 : Ws → Eqn
  q371 c4 = wpE 427 c4

-- Su-box @243243: 17 steps
lem-Su-box-at243243 : Ws → ⟪ (ℓ "上仄") ⟫ʷ ≈ ⟪ (ℓ "仄上") ⟫ʷ
lem-Su-box-at243243 c4 = derive (ℓ "上仄") (ℓ "仄上")
  (rw 1 (q358 c4) ∷
   rw 0 (q368 c4) ∷
   rw 3 (q360 c4) ∷
   rw⁻ 7 (q361 c4) ∷
   rw⁻ 6 (q362 c4) ∷
   rw 5 (q363 c4) ∷
   rw⁻ 4 (q362 c4) ∷
   rw 3 (q364 c4) ∷
   rw⁻ 4 (q360 c4) ∷
   rw 2 (q364 c4) ∷
   rw⁻ 1 (q369 c4) ∷
   rw 4 (q41 c4) ∷
   rw 3 (q370 c4) ∷
   rw 2 (q368 c4) ∷
   rw 3 (q371 c4) ∷
   rw⁻ 3 (q369 c4) ∷
   rw⁻ 0 (q358 c4) ∷ []) Eq.refl

private
  q372 : Ws → Eqn
  q372 c4 = sE 257 (lem-box-tQ-at122441 c4)
  q373 : Ws → Eqn
  q373 c4 = wpE 431 c4
  q374 : Ws → Eqn
  q374 c4 = wpE 296 c4
  q375 : Ws → Eqn
  q375 c4 = wpE 77 c4
  q376 : Ws → Eqn
  q376 c4 = sE 204 (lem-comm-CSd24-CCZ013 c4)
  q377 : Ws → Eqn
  q377 c4 = sE 194 (lem-comm-CS24-CCZ013 c4)
  q378 : Ws → Eqn
  q378 c4 = wpE 76 c4
  q379 : Ws → Eqn
  q379 c4 = wpE 432 c4
  q380 : Ws → Eqn
  q380 c4 = wpE 433 c4

-- CSdu-box-2 @122441: 17 steps
lem-CSdu-box-2-at122441 : Ws → ⟪ (ℓ "举仞") ⟫ʷ ≈ ⟪ (ℓ "仞举") ⟫ʷ
lem-CSdu-box-2-at122441 c4 = derive (ℓ "举仞") (ℓ "仞举")
  (rw 1 (q372 c4) ∷
   rw 0 (q373 c4) ∷
   rw 3 (q374 c4) ∷
   rw⁻ 7 (q375 c4) ∷
   rw⁻ 6 (q332 c4) ∷
   rw 5 (q376 c4) ∷
   rw⁻ 4 (q332 c4) ∷
   rw 3 (q377 c4) ∷
   rw⁻ 4 (q374 c4) ∷
   rw 2 (q376 c4) ∷
   rw⁻ 1 (q378 c4) ∷
   rw 4 (q54 c4) ∷
   rw 3 (q379 c4) ∷
   rw 2 (q373 c4) ∷
   rw 3 (q380 c4) ∷
   rw⁻ 3 (q378 c4) ∷
   rw⁻ 0 (q372 c4) ∷ []) Eq.refl

private
  q381 : Ws → Eqn
  q381 c4 = wpE 434 c4
  q382 : Ws → Eqn
  q382 c4 = wlE 562 (lit c4)
  q383 : Ws → Eqn
  q383 c4 = wpE 435 c4
  q384 : Ws → Eqn
  q384 c4 = wpE 436 c4

-- Su-box @122441: 17 steps
lem-Su-box-at122441 : Ws → ⟪ (ℓ "上仞") ⟫ʷ ≈ ⟪ (ℓ "仞上") ⟫ʷ
lem-Su-box-at122441 c4 = derive (ℓ "上仞") (ℓ "仞上")
  (rw 1 (q372 c4) ∷
   rw 0 (q381 c4) ∷
   rw 3 (q374 c4) ∷
   rw⁻ 7 (q375 c4) ∷
   rw⁻ 6 (q332 c4) ∷
   rw 5 (q376 c4) ∷
   rw⁻ 4 (q332 c4) ∷
   rw 3 (q377 c4) ∷
   rw⁻ 4 (q374 c4) ∷
   rw 2 (q377 c4) ∷
   rw⁻ 1 (q382 c4) ∷
   rw 4 (q54 c4) ∷
   rw 3 (q383 c4) ∷
   rw 2 (q381 c4) ∷
   rw 3 (q384 c4) ∷
   rw⁻ 3 (q382 c4) ∷
   rw⁻ 0 (q372 c4) ∷ []) Eq.refl

private
  q385 : Ws → Eqn
  q385 c4 = sE 248 (lem-box-tQ-at0210243143 c4)
  q386 : Ws → Eqn
  q386 c4 = wpE 449 c4
  q387 : Ws → Eqn
  q387 c4 = wpE 450 c4
  q388 : Ws → Eqn
  q388 c4 = wlE 173 (lit c4)
  q389 : Ws → Eqn
  q389 c4 = wlE 482 (lit c4)
  q390 : Ws → Eqn
  q390 c4 = sE 220 (lem-comm-CSd04-CCZ123 c4)
  q391 : Ws → Eqn
  q391 c4 = sE 216 (lem-comm-CS04-CCZ123 c4)
  q392 : Ws → Eqn
  q392 c4 = wlE 172 (lit c4)
  q393 : Ws → Eqn
  q393 c4 = wpE 451 c4
  q394 : Ws → Eqn
  q394 c4 = wpE 452 c4

-- CSdu-box-2 @0210243143: 17 steps
lem-CSdu-box-2-at0210243143 : Ws → ⟪ (ℓ "乪伱") ⟫ʷ ≈ ⟪ (ℓ "伱乪") ⟫ʷ
lem-CSdu-box-2-at0210243143 c4 = derive (ℓ "乪伱") (ℓ "伱乪")
  (rw 1 (q385 c4) ∷
   rw 0 (q386 c4) ∷
   rw 3 (q387 c4) ∷
   rw⁻ 7 (q388 c4) ∷
   rw⁻ 6 (q389 c4) ∷
   rw 5 (q390 c4) ∷
   rw⁻ 4 (q389 c4) ∷
   rw 3 (q391 c4) ∷
   rw⁻ 4 (q387 c4) ∷
   rw 2 (q390 c4) ∷
   rw⁻ 1 (q392 c4) ∷
   rw 4 (q28 c4) ∷
   rw 3 (q393 c4) ∷
   rw 2 (q386 c4) ∷
   rw 3 (q394 c4) ∷
   rw⁻ 3 (q392 c4) ∷
   rw⁻ 0 (q385 c4) ∷ []) Eq.refl

private
  q395 : Ws → Eqn
  q395 c4 = wpE 453 c4
  q396 : Ws → Eqn
  q396 c4 = wlE 582 (lit c4)
  q397 : Ws → Eqn
  q397 c4 = wpE 454 c4
  q398 : Ws → Eqn
  q398 c4 = wpE 455 c4

-- Su-box @0210243143: 17 steps
lem-Su-box-at0210243143 : Ws → ⟪ (ℓ "世伱") ⟫ʷ ≈ ⟪ (ℓ "伱世") ⟫ʷ
lem-Su-box-at0210243143 c4 = derive (ℓ "世伱") (ℓ "伱世")
  (rw 1 (q385 c4) ∷
   rw 0 (q395 c4) ∷
   rw 3 (q387 c4) ∷
   rw⁻ 7 (q388 c4) ∷
   rw⁻ 6 (q389 c4) ∷
   rw 5 (q390 c4) ∷
   rw⁻ 4 (q389 c4) ∷
   rw 3 (q391 c4) ∷
   rw⁻ 4 (q387 c4) ∷
   rw 2 (q391 c4) ∷
   rw⁻ 1 (q396 c4) ∷
   rw 4 (q28 c4) ∷
   rw 3 (q397 c4) ∷
   rw 2 (q395 c4) ∷
   rw 3 (q398 c4) ∷
   rw⁻ 3 (q396 c4) ∷
   rw⁻ 0 (q385 c4) ∷ []) Eq.refl

private
  q399 : Ws → Eqn
  q399 c4 = wpE 480 c4
  q400 : Ws → Eqn
  q400 c4 = wpE 481 c4

-- CSu-box-2 @243243: 17 steps
lem-CSu-box-2-at243243 : Ws → ⟪ (ℓ "丽仄") ⟫ʷ ≈ ⟪ (ℓ "仄丽") ⟫ʷ
lem-CSu-box-2-at243243 c4 = derive (ℓ "丽仄") (ℓ "仄丽")
  (rw 1 (q358 c4) ∷
   rw 0 (q399 c4) ∷
   rw 3 (q360 c4) ∷
   rw⁻ 7 (q361 c4) ∷
   rw⁻ 6 (q362 c4) ∷
   rw 5 (q363 c4) ∷
   rw⁻ 4 (q362 c4) ∷
   rw 3 (q364 c4) ∷
   rw⁻ 4 (q360 c4) ∷
   rw 2 (q364 c4) ∷
   rw⁻ 1 (q361 c4) ∷
   rw 4 (q41 c4) ∷
   rw 3 (q370 c4) ∷
   rw 2 (q399 c4) ∷
   rw 3 (q400 c4) ∷
   rw⁻ 3 (q361 c4) ∷
   rw⁻ 0 (q358 c4) ∷ []) Eq.refl

private
  q401 : Ws → Eqn
  q401 c4 = wpE 487 c4
  q402 : Ws → Eqn
  q402 c4 = wpE 488 c4

-- CSu-box-2 @122441: 17 steps
lem-CSu-box-2-at122441 : Ws → ⟪ (ℓ "丽仞") ⟫ʷ ≈ ⟪ (ℓ "仞丽") ⟫ʷ
lem-CSu-box-2-at122441 c4 = derive (ℓ "丽仞") (ℓ "仞丽")
  (rw 1 (q372 c4) ∷
   rw 0 (q401 c4) ∷
   rw 3 (q374 c4) ∷
   rw⁻ 7 (q375 c4) ∷
   rw⁻ 6 (q332 c4) ∷
   rw 5 (q376 c4) ∷
   rw⁻ 4 (q332 c4) ∷
   rw 3 (q377 c4) ∷
   rw⁻ 4 (q374 c4) ∷
   rw 2 (q377 c4) ∷
   rw⁻ 1 (q375 c4) ∷
   rw 4 (q54 c4) ∷
   rw 3 (q383 c4) ∷
   rw 2 (q401 c4) ∷
   rw 3 (q402 c4) ∷
   rw⁻ 3 (q375 c4) ∷
   rw⁻ 0 (q372 c4) ∷ []) Eq.refl

private
  q403 : Ws → Eqn
  q403 c4 = sE 249 (lem-box-tQ-at0214203143 c4)
  q404 : Ws → Eqn
  q404 c4 = wpE 497 c4
  q405 : Ws → Eqn
  q405 c4 = wlE 612 (lit c4)
  q406 : Ws → Eqn
  q406 c4 = wpE 498 c4
  q407 : Ws → Eqn
  q407 c4 = wpE 320 c4
  q408 : Ws → Eqn
  q408 c4 = wlE 492 (lit c4)
  q409 : Ws → Eqn
  q409 c4 = sE 20 (lem-comm-CX40-CCZ123 c4)
  q410 : Ws → Eqn
  q410 c4 = wlE 495 (lit c4)
  q411 : Ws → Eqn
  q411 c4 = wlE 490 (lit c4)
  q412 : Ws → Eqn
  q412 c4 = wlE 613 (lit c4)
  q413 : Ws → Eqn
  q413 c4 = wlE 614 (lit c4)
  q414 : Ws → Eqn
  q414 c4 = wpE 499 c4

-- CXbc-box @0214203143: 17 steps
lem-CXbc-box-at0214203143 : Ws → ⟪ (ℓ "丬佔丬") ⟫ʷ ≈ ⟪ (ℓ "佔亠") ⟫ʷ
lem-CXbc-box-at0214203143 c4 = derive (ℓ "丬佔丬") (ℓ "佔亠")
  (rw 1 (q403 c4) ∷
   rw 0 (q404 c4) ∷
   rw⁻ 1 (q405 c4) ∷
   rw 3 (q406 c4) ∷
   rw 2 (q404 c4) ∷
   rw 5 (q407 c4) ∷
   rw⁻ 9 (q408 c4) ∷
   rw 8 (q409 c4) ∷
   rw⁻ 7 (q410 c4) ∷
   rw 6 (q409 c4) ∷
   rw⁻ 5 (q411 c4) ∷
   rw⁻ 6 (q407 c4) ∷
   rw 4 (q412 c4) ∷
   rw⁻ 3 (q405 c4) ∷
   rw 4 (q413 c4) ∷
   rw⁻ 0 (q403 c4) ∷
   rw⁻ 1 (q414 c4) ∷ []) Eq.refl

private
  q415 : Ws → Eqn
  q415 c4 = wpE 500 c4
  q416 : Ws → Eqn
  q416 c4 = wlE 615 (lit c4)
  q417 : Ws → Eqn
  q417 c4 = wlE 616 (lit c4)
  q418 : Ws → Eqn
  q418 c4 = wlE 617 (lit c4)
  q419 : Ws → Eqn
  q419 c4 = wpE 501 c4
  q420 : Ws → Eqn
  q420 c4 = wpE 502 c4
  q421 : Ws → Eqn
  q421 c4 = sE 223 (lem-comm-CSd13-TOFF204 c4)
  q422 : Ws → Eqn
  q422 c4 = sE 218 (lem-comm-CS13-TOFF204 c4)
  q423 : Ws → Eqn
  q423 c4 = wpE 503 c4
  q424 : Ws → Eqn
  q424 c4 = wpE 504 c4
  q425 : Ws → Eqn
  q425 c4 = wlE 618 (lit c4)
  q426 : Ws → Eqn
  q426 c4 = wpE 505 c4

-- CXcb-box @0214203143: 18 steps
lem-CXcb-box-at0214203143 : Ws → ⟪ (ℓ "乄佔乄") ⟫ʷ ≈ ⟪ (ℓ "佔京") ⟫ʷ
lem-CXcb-box-at0214203143 c4 = derive (ℓ "乄佔乄") (ℓ "佔京")
  (rw 1 (q403 c4) ∷
   rw 0 (q415 c4) ∷
   rw⁻ 2 (q416 c4) ∷
   rw⁻ 1 (q417 c4) ∷
   rw 4 (q418 c4) ∷
   rw 8 (q419 c4) ∷
   rw 7 (q420 c4) ∷
   rw 6 (q421 c4) ∷
   rw 5 (q420 c4) ∷
   rw 4 (q422 c4) ∷
   rw⁻ 5 (q418 c4) ∷
   rw⁻ 3 (q423 c4) ∷
   rw 2 (q415 c4) ∷
   rw 3 (q424 c4) ∷
   rw⁻ 4 (q425 c4) ∷
   rw⁻ 3 (q417 c4) ∷
   rw⁻ 0 (q403 c4) ∷
   rw⁻ 1 (q426 c4) ∷ []) Eq.refl

private
  q427 : Ws → Eqn
  q427 c4 = sE 250 (lem-box-tQ-at0214213043 c4)
  q428 : Ws → Eqn
  q428 c4 = sE 268 (lem-tP-at0214213043 c4)
  q429 : Ws → Eqn
  q429 c4 = wlE 626 (lit c4)
  q430 : Ws → Eqn
  q430 c4 = wlE 627 (lit c4)
  q431 : Ws → Eqn
  q431 c4 = sE 225 (lem-comm-CZ03-TOFF214 c4)
  q432 : Ws → Eqn
  q432 c4 = wlE 628 (lit c4)

-- P-box @0214213043: 8 steps
lem-P-box-at0214213043 : Ws → ⟪ (ℓ "亚佝亚") ⟫ʷ ≈ ⟪ (ℓ "佝") ⟫ʷ
lem-P-box-at0214213043 c4 = derive (ℓ "亚佝亚") (ℓ "佝")
  (rw 1 (q427 c4) ∷
   rw⁻ 0 (q428 c4) ∷
   rw⁻ 1 (q429 c4) ∷
   rw⁻ 3 (q428 c4) ∷
   rw⁻ 4 (q430 c4) ∷
   rw 2 (q431 c4) ∷
   rw⁻ 3 (q432 c4) ∷
   rw⁻ 0 (q427 c4) ∷ []) Eq.refl
