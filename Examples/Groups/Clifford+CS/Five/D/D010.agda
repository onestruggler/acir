{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD010 ; pickᴰ)

module Examples.Groups.Clifford+CS.Five.D.D010 (Sᴰ : SD010) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS13-TOFF024 ; lem-comm-CS14-TOFF023 ; lem-comm-CS24-TOFF013 ; lem-comm-CSd04-TOFF213 ; lem-comm-CSd12-TOFF034 ; lem-comm-CSd13-TOFF024 ; lem-comm-CSd14-TOFF023 ; lem-comm-CSd23-TOFF014 ; lem-comm-CSd24-TOFF013 ; lem-comm-CX04-CCZ123 ; lem-comm-CX13-CCZ024 ; lem-comm-CX14-CCZ023 ; lem-comm-CX21-CCZ034 ; lem-comm-CX23-CCZ014 ; lem-comm-CX24-CCZ013 ; lem-comm-CX31-CCZ024 ; lem-comm-CX32-CCZ014 ; lem-comm-CX42-CCZ013 ; lem-comm-CZ04-TOFF213 ; lem-comm-CZ14-TOFF023 ; lem-comm-TOFF013-CSd24 ; lem-comm-TOFF014-CSd23 ; lem-comm-TOFF024-CSd13 ; lem-comm-TOFF204-CSd13)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS02-TOFF314 ; lem-comm-CS03-TOFF214 ; lem-comm-CS04-CCZ123 ; lem-comm-CS04-TOFF213 ; lem-comm-CS04-TOFF312 ; lem-comm-CS12-TOFF304 ; lem-comm-CS13-TOFF204 ; lem-comm-CS23-TOFF014 ; lem-comm-CSd02-TOFF314 ; lem-comm-CSd03-TOFF214 ; lem-comm-CSd04-CCZ123 ; lem-comm-CSd04-TOFF312 ; lem-comm-CSd12-TOFF304 ; lem-comm-CSd13-TOFF204 ; lem-comm-CSd14-TOFF203 ; lem-comm-CSd14-TOFF302 ; lem-comm-CSd24-TOFF301 ; lem-comm-CX40-CCZ123 ; lem-comm-CX41-CCZ023 ; lem-comm-CZ13-TOFF024 ; lem-comm-CZ13-TOFF204 ; lem-comm-CZ14-TOFF203 ; lem-comm-CZ14-TOFF302 ; lem-comm-CZ23-TOFF014 ; lem-comm-TOFF213-CSd04 ; lem-comm-TOFF214-CSd03 ; lem-comm-TOFF314-CSd02)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF023-CSd14 ; lem-comm-TOFF203-CSd14)

-- The lemmas of other derivation modules (DSig).
private
  lem-CXbc-box-at0213243140 : Ws → St 181
  lem-CXbc-box-at0213243140 = pickᴰ 0 Sᴰ
  lem-CXcb-box-at0213243140 : Ws → St 182
  lem-CXcb-box-at0213243140 = pickᴰ 1 Sᴰ
  lem-VPQ-at0210213443 : Ws → St 183
  lem-VPQ-at0210213443 = pickᴰ 2 Sᴰ
  lem-VPQ-at0220 : Ws → St 184
  lem-VPQ-at0220 = pickᴰ 3 Sᴰ
  lem-VPQ-at032032 : Ws → St 185
  lem-VPQ-at032032 = pickᴰ 4 Sᴰ
  lem-VPQ-at14233241 : Ws → St 186
  lem-VPQ-at14233241 = pickᴰ 5 Sᴰ
  lem-box-tQ-at0210233441 : Ws → St 187
  lem-box-tQ-at0210233441 = pickᴰ 6 Sᴰ
  lem-box-tQ-at0210243143 : Ws → St 147
  lem-box-tQ-at0210243143 = pickᴰ 7 Sᴰ
  lem-box-tQ-at0214203143 : Ws → St 148
  lem-box-tQ-at0214203143 = pickᴰ 8 Sᴰ
  lem-box-tQ-at0214213043 : Ws → St 149
  lem-box-tQ-at0214213043 = pickᴰ 9 Sᴰ
  lem-box-tQ-at022330 : Ws → St 188
  lem-box-tQ-at022330 = pickᴰ 10 Sᴰ
  lem-box-tQ-at0312213440 : Ws → St 189
  lem-box-tQ-at0312213440 = pickᴰ 11 Sᴰ
  lem-box-tQ-at0312243140 : Ws → St 190
  lem-box-tQ-at0312243140 = pickᴰ 12 Sᴰ
  lem-box-tQ-at0314203142 : Ws → St 191
  lem-box-tQ-at0314203142 = pickᴰ 13 Sᴰ
  lem-box-tQ-at0314213042 : Ws → St 192
  lem-box-tQ-at0314213042 = pickᴰ 14 Sᴰ
  lem-box-tQ-at122331 : Ws → St 154
  lem-box-tQ-at122331 = pickᴰ 15 Sᴰ
  lem-box-tQ-at12233441 : Ws → St 193
  lem-box-tQ-at12233441 = pickᴰ 16 Sᴰ
  lem-box-tQ-at122441 : Ws → St 156
  lem-box-tQ-at122441 = pickᴰ 17 Sᴰ
  lem-box-tQ-at132132 : Ws → St 157
  lem-box-tQ-at132132 = pickᴰ 18 Sᴰ
  lem-box-tQ-at1331 : Ws → St 159
  lem-box-tQ-at1331 = pickᴰ 19 Sᴰ
  lem-box-tQ-at14213243 : Ws → St 194
  lem-box-tQ-at14213243 = pickᴰ 20 Sᴰ
  lem-box-tQ-at143143 : Ws → St 195
  lem-box-tQ-at143143 = pickᴰ 21 Sᴰ
  lem-box-tQ-at1441 : Ws → St 196
  lem-box-tQ-at1441 = pickᴰ 22 Sᴰ
  lem-box-tQ-at2332 : Ws → St 161
  lem-box-tQ-at2332 = pickᴰ 23 Sᴰ
  lem-box-tQ-at243243 : Ws → St 162
  lem-box-tQ-at243243 = pickᴰ 24 Sᴰ
  lem-tP-at0210233441 : Ws → St 197
  lem-tP-at0210233441 = pickᴰ 25 Sᴰ
  lem-tP-at0210243143 : Ws → St 166
  lem-tP-at0210243143 = pickᴰ 26 Sᴰ
  lem-tP-at0213203441 : Ws → St 198
  lem-tP-at0213203441 = pickᴰ 27 Sᴰ
  lem-tP-at0214213043 : Ws → St 167
  lem-tP-at0214213043 = pickᴰ 28 Sᴰ
  lem-tP-at0312243140 : Ws → St 199
  lem-tP-at0312243140 = pickᴰ 29 Sᴰ
  lem-tP-at0314213042 : Ws → St 200
  lem-tP-at0314213042 = pickᴰ 30 Sᴰ
  lem-tP-at12213443 : Ws → St 201
  lem-tP-at12213443 = pickᴰ 31 Sᴰ
  lem-tP-at12233441 : Ws → St 202
  lem-tP-at12233441 = pickᴰ 32 Sᴰ
  lem-tP-at122441 : Ws → St 174
  lem-tP-at122441 = pickᴰ 33 Sᴰ
  lem-tP-at143143 : Ws → St 203
  lem-tP-at143143 = pickᴰ 34 Sᴰ
  lem-tP-at233442 : Ws → St 204
  lem-tP-at233442 = pickᴰ 35 Sᴰ
  lem-tP-at243243 : Ws → St 179
  lem-tP-at243243 = pickᴰ 36 Sᴰ
  lem-CXbc-box-at0220 : Ws → St 205
  lem-CXbc-box-at0220 = pickᴰ 37 Sᴰ
  lem-CXbc-box-at03102132 : Ws → St 206
  lem-CXbc-box-at03102132 = pickᴰ 38 Sᴰ
  lem-CXcb-box-at0220 : Ws → St 207
  lem-CXcb-box-at0220 = pickᴰ 39 Sᴰ
  lem-CXcb-box-at03102132 : Ws → St 208
  lem-CXcb-box-at03102132 = pickᴰ 40 Sᴰ
  lem-VPQ-at0213243140 : Ws → St 209
  lem-VPQ-at0213243140 = pickᴰ 41 Sᴰ
  lem-box-tQ-at0213213440 : Ws → St 210
  lem-box-tQ-at0213213440 = pickᴰ 42 Sᴰ
  lem-box-tQ-at02233440 : Ws → St 211
  lem-box-tQ-at02233440 = pickᴰ 43 Sᴰ
  lem-box-tQ-at022440 : Ws → St 212
  lem-box-tQ-at022440 = pickᴰ 44 Sᴰ
  lem-tP-at0214203143 : Ws → St 213
  lem-tP-at0214203143 = pickᴰ 45 Sᴰ
  lem-tP-at022330 : Ws → St 214
  lem-tP-at022330 = pickᴰ 46 Sᴰ
  lem-tP-at022440 : Ws → St 215
  lem-tP-at022440 = pickᴰ 47 Sᴰ
  lem-tP-at14213243 : Ws → St 216
  lem-tP-at14213243 = pickᴰ 48 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = eqn (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) (Toff214 ∷ CCZ124 ∷ []) (wl 629 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) (Toff203 ∷ CCZ023 ∷ []) (wl 630 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (CS03⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS03⁻ ∷ []) (wl 631 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (Toff214 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff214 ∷ []) (lem-comm-TOFF214-CSd03 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (CS03⁻ ∷ S2 ∷ []) (S2 ∷ CS03⁻ ∷ []) (wl 632 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CS03⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS03⁻ ∷ []) (wp 514 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (S2⁻ ∷ S2 ∷ []) [] (wl 179 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (Toff214 ∷ Toff203 ∷ []) (Toff203 ∷ Toff214 ∷ []) (lem-tP-at0214213043 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CS14⁻ ∷ S2 ∷ []) (S2 ∷ CS14⁻ ∷ []) (wl 633 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (CS14⁻ ∷ Toff203 ∷ []) (Toff203 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF203 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (CS14⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS14⁻ ∷ []) (wl 634 (lit c4))

-- VPQ @0214213043: 14 steps
lem-VPQ-at0214213043 : Ws → ⟪ (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) ⟫ʷ
lem-VPQ-at0214213043 c4 = derive (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ [])
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
  q12 c4 = eqn (Toff203 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Toff203 ∷ []) (lem-comm-TOFF203-CSd14 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (Toff203 ∷ Toff214 ∷ []) (Toff214 ∷ Toff203 ∷ []) (lem-tP-at0210233441 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (CS03⁻ ∷ Toff214 ∷ []) (Toff214 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF214 (lit c4))

-- VPQ @0210233441: 14 steps
lem-VPQ-at0210233441 : Ws → ⟪ (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at0210233441 c4 = derive (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ [])
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
  q15 c4 = eqn (Bx0-2431 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at122441 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (CX43 ∷ Toff024 ∷ []) (Toff024 ∷ CX43 ∷ []) (wp 519 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (CCZ013 ∷ CX43 ∷ CCZ014 ∷ []) (CX43 ∷ CCZ013 ∷ []) (wp 392 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CCZ014 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp 520 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CCZ124 ∷ []) (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ []) (wl 644 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (CCZ013 ∷ CS12 ∷ []) (CS12 ∷ CCZ013 ∷ []) (wl 645 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (CX24 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ013 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ013 ∷ []) (wp 521 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CCZ013 ∷ CS14 ∷ []) (CS14 ∷ CCZ013 ∷ []) (wp 299 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ013 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ013 ∷ []) (wp 394 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CX43 ∷ CCZ014 ∷ CCZ014 ∷ []) (CX43 ∷ []) (wp 395 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (CCZ124 ∷ []) (CX43 ∷ CCZ124 ∷ CX43 ∷ []) (wl 646 (lit c4))

-- CXbc-box @122441: 17 steps
lem-CXbc-box-at122441 : Ws → ⟪ (CX43 ∷ Bx0-2431 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at122441 c4 = derive (CX43 ∷ Bx0-2431 ∷ CX43 ∷ []) (Bx0-2431 ∷ CCZ124 ∷ [])
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
  q27 c4 = eqn (CX34 ∷ Toff024 ∷ []) (Toff024 ∷ CX34 ∷ Toff023 ∷ []) (wp 522 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (CCZ013 ∷ Toff023 ∷ CCZ123 ∷ []) (Toff023 ∷ CCZ013 ∷ []) (wl 647 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (CCZ013 ∷ CX34 ∷ []) (CX34 ∷ CCZ013 ∷ []) (wp 523 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (CCZ123 ∷ []) (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) (wl 233 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (CS12 ∷ Toff024 ∷ []) (Toff024 ∷ CS12 ∷ []) (wp 524 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (CX23 ∷ Toff024 ∷ []) (Toff024 ∷ CX23 ∷ []) (wp 525 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (CS13⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF024 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (CS13 ∷ Toff024 ∷ []) (Toff024 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF024 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (Toff023 ∷ Toff024 ∷ []) (Toff024 ∷ Toff023 ∷ []) (wp 72 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (CX34 ∷ Toff023 ∷ Toff023 ∷ []) (CX34 ∷ []) (wp 526 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CCZ013 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ013 ∷ []) (wl 327 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (CCZ123 ∷ []) (CX34 ∷ CCZ123 ∷ CX34 ∷ []) (wl 648 (lit c4))

-- CXcb-box @122441: 18 steps
lem-CXcb-box-at122441 : Ws → ⟪ (CX34 ∷ Bx0-2431 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at122441 c4 = derive (CX34 ∷ Bx0-2431 ∷ CX34 ∷ []) (Bx0-2431 ∷ CCZ123 ∷ [])
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
  q39 c4 = eqn (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) (Toff023 ∷ CCZ023 ∷ []) (wl 201 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (Toff014 ∷ CCZ014 ∷ []) (wp 50 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (S0⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))
  q42 : Ws → Eqn
  q42 c4 = eqn (Toff023 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Toff023 ∷ []) (lem-comm-TOFF023-CSd14 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (S0 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))
  q44 : Ws → Eqn
  q44 c4 = eqn (CS14⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS14⁻ ∷ []) (wl 202 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (S0⁻ ∷ S0 ∷ []) [] (wl 159 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (Toff023 ∷ Toff014 ∷ []) (Toff014 ∷ Toff023 ∷ []) (lem-tP-at12233441 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (S0 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S0 ∷ []) (c₁ (S) ((CS • CS • CS) ↑))
  q48 : Ws → Eqn
  q48 c4 = eqn (CS23⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF014 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (S0⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) ((CS • CS • CS) ↑))

-- VPQ @12233441: 14 steps
lem-VPQ-at12233441 : Ws → ⟪ (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at12233441 c4 = derive (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ [])
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
  q50 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (CS24 ∷ Toff204 ∷ []) (Toff204 ∷ CS24 ∷ CS04 ∷ CCZ024 ∷ []) (wp 534 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (CCZ024 ∷ []) (CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ []) (wp 450 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (CCZ123 ∷ CS24 ∷ []) (CS24 ∷ CCZ123 ∷ []) (wl 173 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (CCZ123 ∷ CX20 ∷ []) (CX20 ∷ CCZ123 ∷ []) (wl 482 (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (CS04⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-CCZ123 (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (CS04 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS04 ∷ []) (lem-comm-CS04-CCZ123 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (CCZ024 ∷ Toff204 ∷ []) (Toff204 ∷ CZ04 ∷ CCZ024 ∷ []) (wp 28 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (CS04 ∷ Toff204 ∷ []) (Toff204 ∷ CS04 ∷ []) (wp 454 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (CS24 ∷ CS04 ∷ CCZ024 ∷ CS04 ∷ CZ04 ∷ CCZ024 ∷ []) (CS24 ∷ []) (wp 535 c4)

-- CSu-box-2 @0210243143: 17 steps
lem-CSu-box-2-at0210243143 : Ws → ⟪ (CS24 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS24 ∷ []) ⟫ʷ
lem-CSu-box-2-at0210243143 c4 = derive (CS24 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS24 ∷ [])
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
  q60 c4 = eqn (Bx0-4123 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at14213243 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (CX12 ∷ Toff014 ∷ []) (Toff014 ∷ CX12 ∷ []) (wp 541 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (CCZ023 ∷ CX12 ∷ CCZ013 ∷ []) (CX12 ∷ CCZ023 ∷ []) (wl 668 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (CCZ013 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ013 ∷ CCZ134 ∷ []) (wp 542 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl 617 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (CCZ023 ∷ CS34 ∷ []) (CS34 ∷ CCZ023 ∷ []) (wp 543 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (CX41 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (CCZ023 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ023 ∷ []) (wl 669 (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (CCZ023 ∷ CS13 ∷ []) (CS13 ∷ CCZ023 ∷ []) (wl 670 (lit c4))
  q69 : Ws → Eqn
  q69 c4 = eqn (CCZ013 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ013 ∷ []) (wl 671 (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (CX12 ∷ CCZ013 ∷ CCZ013 ∷ []) (CX12 ∷ []) (wl 672 (lit c4))
  q71 : Ws → Eqn
  q71 c4 = eqn (CCZ134 ∷ []) (CX12 ∷ CCZ134 ∷ CX12 ∷ []) (wl 673 (lit c4))

-- CXbc-box @14213243: 17 steps
lem-CXbc-box-at14213243 : Ws → ⟪ (CX12 ∷ Bx0-4123 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at14213243 c4 = derive (CX12 ∷ Bx0-4123 ∷ CX12 ∷ []) (Bx0-4123 ∷ CCZ134 ∷ [])
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
  q72 c4 = eqn (CX21 ∷ Toff014 ∷ []) (Toff014 ∷ CX21 ∷ Toff024 ∷ []) (wp 544 c4)
  q73 : Ws → Eqn
  q73 c4 = eqn (CCZ023 ∷ Toff024 ∷ CCZ234 ∷ []) (Toff024 ∷ CCZ023 ∷ []) (wp 545 c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (CCZ023 ∷ CX21 ∷ []) (CX21 ∷ CCZ023 ∷ []) (wl 674 (lit c4))
  q75 : Ws → Eqn
  q75 c4 = eqn (CCZ234 ∷ []) (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) (wl 675 (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (CS34 ∷ Toff014 ∷ []) (Toff014 ∷ CS34 ∷ []) (wp 546 c4)
  q77 : Ws → Eqn
  q77 c4 = eqn (CX42 ∷ Toff014 ∷ []) (Toff014 ∷ CX42 ∷ []) (wp 547 c4)
  q78 : Ws → Eqn
  q78 c4 = eqn (CS23 ∷ Toff014 ∷ []) (Toff014 ∷ CS23 ∷ []) (lem-comm-CS23-TOFF014 (lit c4))
  q79 : Ws → Eqn
  q79 c4 = eqn (Toff014 ∷ Toff024 ∷ []) (Toff024 ∷ Toff014 ∷ []) (wp 548 c4)
  q80 : Ws → Eqn
  q80 c4 = eqn (CX21 ∷ Toff024 ∷ Toff024 ∷ []) (CX21 ∷ []) (wp 549 c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (CCZ023 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ023 ∷ []) (wp 550 c4)
  q82 : Ws → Eqn
  q82 c4 = eqn (CCZ234 ∷ []) (CX21 ∷ CCZ234 ∷ CX21 ∷ []) (wl 676 (lit c4))

-- CXcb-box @14213243: 18 steps
lem-CXcb-box-at14213243 : Ws → ⟪ (CX21 ∷ Bx0-4123 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXcb-box-at14213243 c4 = derive (CX21 ∷ Bx0-4123 ∷ CX21 ∷ []) (Bx0-4123 ∷ CCZ234 ∷ [])
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
  q83 c4 = eqn (Bx0-4213 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at143143 c4)
  q84 : Ws → Eqn
  q84 c4 = eqn (Toff024 ∷ Toff013 ∷ []) (Toff013 ∷ Toff024 ∷ []) (lem-tP-at143143 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (CCZ013 ∷ CZ13 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ013 ∷ []) (wl 682 (lit c4))
  q86 : Ws → Eqn
  q86 c4 = eqn (CCZ013 ∷ CZ13 ∷ []) (Toff013 ∷ CCZ013 ∷ Toff013 ∷ []) (wl 683 (lit c4))
  q87 : Ws → Eqn
  q87 c4 = eqn (CZ13 ∷ Toff024 ∷ []) (Toff024 ∷ CZ13 ∷ []) (lem-comm-CZ13-TOFF024 (lit c4))
  q88 : Ws → Eqn
  q88 c4 = eqn (CCZ013 ∷ []) (CZ13 ∷ CCZ013 ∷ CZ13 ∷ []) (wl 684 (lit c4))

-- P-box @143143: 8 steps
lem-P-box-at143143 : Ws → ⟪ (Toff013 ∷ Bx0-4213 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-P-box-at143143 c4 = derive (Toff013 ∷ Bx0-4213 ∷ Toff013 ∷ []) (Bx0-4213 ∷ [])
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
  q89 c4 = eqn (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (Toff024 ∷ CCZ024 ∷ []) (wp 79 c4)
  q90 : Ws → Eqn
  q90 c4 = eqn (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (Toff013 ∷ CCZ013 ∷ []) (wl 227 (lit c4))
  q91 : Ws → Eqn
  q91 c4 = eqn (S0⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q92 : Ws → Eqn
  q92 c4 = eqn (Toff024 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Toff024 ∷ []) (lem-comm-TOFF024-CSd13 (lit c4))
  q93 : Ws → Eqn
  q93 c4 = eqn (S0 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q94 : Ws → Eqn
  q94 c4 = eqn (CS13⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS13⁻ ∷ []) (wl 228 (lit c4))
  q95 : Ws → Eqn
  q95 c4 = eqn (S0 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑))
  q96 : Ws → Eqn
  q96 c4 = eqn (CS24⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 (lit c4))
  q97 : Ws → Eqn
  q97 c4 = eqn (S0⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑))

-- VPQ @143143: 14 steps
lem-VPQ-at143143 : Ws → ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at143143 c4 = derive (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ [])
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
  q98 c4 = eqn (Toff013 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4))
  q99 : Ws → Eqn
  q99 c4 = eqn (Toff013 ∷ Toff024 ∷ []) (Toff024 ∷ Toff013 ∷ []) (lem-tP-at233442 c4)

-- VPQ @233442: 14 steps
lem-VPQ-at233442 : Ws → ⟪ (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ
lem-VPQ-at233442 c4 = derive (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ [])
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
  q100 c4 = eqn (CX41 ∷ Toff204 ∷ []) (Toff204 ∷ CX41 ∷ []) (wp 502 c4)
  q101 : Ws → Eqn
  q101 c4 = eqn (CCZ123 ∷ CX41 ∷ CCZ234 ∷ []) (CX41 ∷ CCZ123 ∷ []) (wl 694 (lit c4))
  q102 : Ws → Eqn
  q102 c4 = eqn (CCZ234 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ234 ∷ CCZ034 ∷ []) (wp 559 c4)
  q103 : Ws → Eqn
  q103 c4 = eqn (CCZ034 ∷ []) (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (wp 352 c4)
  q104 : Ws → Eqn
  q104 c4 = eqn (CCZ123 ∷ CS03 ∷ []) (CS03 ∷ CCZ123 ∷ []) (wl 490 (lit c4))
  q105 : Ws → Eqn
  q105 c4 = eqn (CX04 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4))
  q106 : Ws → Eqn
  q106 c4 = eqn (CCZ123 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ123 ∷ []) (wl 491 (lit c4))
  q107 : Ws → Eqn
  q107 c4 = eqn (CCZ123 ∷ CS34 ∷ []) (CS34 ∷ CCZ123 ∷ []) (wl 492 (lit c4))
  q108 : Ws → Eqn
  q108 c4 = eqn (CCZ123 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ123 ∷ []) (wl 508 (lit c4))
  q109 : Ws → Eqn
  q109 c4 = eqn (CX41 ∷ CCZ234 ∷ CCZ234 ∷ []) (CX41 ∷ []) (wl 695 (lit c4))
  q110 : Ws → Eqn
  q110 c4 = eqn (CCZ034 ∷ []) (CX41 ∷ CCZ034 ∷ CX41 ∷ []) (wp 560 c4)

-- CXbc-box @0210243143: 17 steps
lem-CXbc-box-at0210243143 : Ws → ⟪ (CX41 ∷ Bx2-0413 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXbc-box-at0210243143 c4 = derive (CX41 ∷ Bx2-0413 ∷ CX41 ∷ []) (Bx2-0413 ∷ CCZ034 ∷ [])
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
  q111 c4 = eqn (CX14 ∷ Toff204 ∷ []) (Toff204 ∷ CX14 ∷ Toff201 ∷ []) (wp 561 c4)
  q112 : Ws → Eqn
  q112 c4 = eqn (CCZ123 ∷ Toff201 ∷ CCZ013 ∷ []) (Toff201 ∷ CCZ123 ∷ []) (wl 696 (lit c4))
  q113 : Ws → Eqn
  q113 c4 = eqn (CCZ123 ∷ CX14 ∷ []) (CX14 ∷ CCZ123 ∷ []) (wl 424 (lit c4))
  q114 : Ws → Eqn
  q114 c4 = eqn (CCZ013 ∷ []) (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl 184 (lit c4))
  q115 : Ws → Eqn
  q115 c4 = eqn (CS03 ∷ Toff204 ∷ []) (Toff204 ∷ CS03 ∷ []) (wp 562 c4)
  q116 : Ws → Eqn
  q116 c4 = eqn (CX01 ∷ Toff204 ∷ []) (Toff204 ∷ CX01 ∷ []) (wp 497 c4)
  q117 : Ws → Eqn
  q117 c4 = eqn (CS13⁻ ∷ Toff204 ∷ []) (Toff204 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF204 (lit c4))
  q118 : Ws → Eqn
  q118 c4 = eqn (CS13 ∷ Toff204 ∷ []) (Toff204 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF204 (lit c4))
  q119 : Ws → Eqn
  q119 c4 = eqn (Toff201 ∷ Toff204 ∷ []) (Toff204 ∷ Toff201 ∷ []) (wp 563 c4)
  q120 : Ws → Eqn
  q120 c4 = eqn (CX14 ∷ Toff201 ∷ Toff201 ∷ []) (CX14 ∷ []) (wp 564 c4)
  q121 : Ws → Eqn
  q121 c4 = eqn (CCZ013 ∷ []) (CX14 ∷ CCZ013 ∷ CX14 ∷ []) (wp 565 c4)

-- CXcb-box @0210243143: 18 steps
lem-CXcb-box-at0210243143 : Ws → ⟪ (CX14 ∷ Bx2-0413 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXcb-box-at0210243143 c4 = derive (CX14 ∷ Bx2-0413 ∷ CX14 ∷ []) (Bx2-0413 ∷ CCZ013 ∷ [])
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
  q122 c4 = eqn (Toff234 ∷ Toff234 ∷ []) [] (wl 420 (lit c4))
  q123 : Ws → Eqn
  q123 c4 = eqn (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) (lem-VPQ-at0210213443 c4)
  q124 : Ws → Eqn
  q124 c4 = eqn (CCZ234 ∷ CCZ234 ∷ []) [] (wl 305 (lit c4))

-- QVQ @0210213443: 3 steps
lem-QVQ-at0210213443 : Ws → ⟪ (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ []) ⟫ʷ
lem-QVQ-at0210213443 c4 = derive (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ [])
  (rw⁻ 0 (q122 c4) ∷
   rw⁻ 1 (q123 c4) ∷
   rw 4 (q124 c4) ∷ []) Eq.refl

private
  q125 : Ws → Eqn
  q125 c4 = eqn (Bx0-1423 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at243243 c4)
  q126 : Ws → Eqn
  q126 c4 = eqn (CCZ023 ∷ CX42 ∷ CCZ034 ∷ []) (CX42 ∷ CCZ023 ∷ []) (wp 572 c4)
  q127 : Ws → Eqn
  q127 c4 = eqn (CCZ034 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ034 ∷ CCZ134 ∷ []) (wp 573 c4)
  q128 : Ws → Eqn
  q128 c4 = eqn (CCZ134 ∷ []) (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl 698 (lit c4))
  q129 : Ws → Eqn
  q129 c4 = eqn (CX14 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4))
  q130 : Ws → Eqn
  q130 c4 = eqn (CCZ023 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ023 ∷ []) (wp 574 c4)
  q131 : Ws → Eqn
  q131 c4 = eqn (CCZ023 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ023 ∷ []) (wp 575 c4)
  q132 : Ws → Eqn
  q132 c4 = eqn (CX42 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX42 ∷ []) (wp 576 c4)
  q133 : Ws → Eqn
  q133 c4 = eqn (CCZ134 ∷ []) (CX42 ∷ CCZ134 ∷ CX42 ∷ []) (wl 312 (lit c4))

-- CXbc-box @243243: 17 steps
lem-CXbc-box-at243243 : Ws → ⟪ (CX42 ∷ Bx0-1423 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at243243 c4 = derive (CX42 ∷ Bx0-1423 ∷ CX42 ∷ []) (Bx0-1423 ∷ CCZ134 ∷ [])
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
  q134 c4 = eqn (CX24 ∷ Toff014 ∷ []) (Toff014 ∷ CX24 ∷ Toff012 ∷ []) (wp 577 c4)
  q135 : Ws → Eqn
  q135 c4 = eqn (CCZ023 ∷ Toff012 ∷ CCZ123 ∷ []) (Toff012 ∷ CCZ023 ∷ []) (wl 699 (lit c4))
  q136 : Ws → Eqn
  q136 c4 = eqn (CCZ023 ∷ CX24 ∷ []) (CX24 ∷ CCZ023 ∷ []) (wp 578 c4)
  q137 : Ws → Eqn
  q137 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl 207 (lit c4))
  q138 : Ws → Eqn
  q138 c4 = eqn (CS13 ∷ Toff014 ∷ []) (Toff014 ∷ CS13 ∷ []) (wp 579 c4)
  q139 : Ws → Eqn
  q139 c4 = eqn (Toff012 ∷ Toff014 ∷ []) (Toff014 ∷ Toff012 ∷ []) (wp 580 c4)
  q140 : Ws → Eqn
  q140 c4 = eqn (CX24 ∷ Toff012 ∷ Toff012 ∷ []) (CX24 ∷ []) (wp 581 c4)
  q141 : Ws → Eqn
  q141 c4 = eqn (CCZ023 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ023 ∷ []) (wl 613 (lit c4))
  q142 : Ws → Eqn
  q142 c4 = eqn (CCZ123 ∷ []) (CX24 ∷ CCZ123 ∷ CX24 ∷ []) (wl 315 (lit c4))

-- CXcb-box @243243: 18 steps
lem-CXcb-box-at243243 : Ws → ⟪ (CX24 ∷ Bx0-1423 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at243243 c4 = derive (CX24 ∷ Bx0-1423 ∷ CX24 ∷ []) (Bx0-1423 ∷ CCZ123 ∷ [])
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
  q143 c4 = eqn (Bx0-4231 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at1441 c4)
  q144 : Ws → Eqn
  q144 c4 = eqn (CCZ013 ∷ CX23 ∷ CCZ012 ∷ []) (CX23 ∷ CCZ013 ∷ []) (wl 701 (lit c4))
  q145 : Ws → Eqn
  q145 c4 = eqn (CCZ012 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ012 ∷ CCZ124 ∷ []) (wp 587 c4)
  q146 : Ws → Eqn
  q146 c4 = eqn (CCZ124 ∷ []) (CS12 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ []) (wl 702 (lit c4))
  q147 : Ws → Eqn
  q147 c4 = eqn (CX42 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4))
  q148 : Ws → Eqn
  q148 c4 = eqn (CCZ013 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ013 ∷ []) (wl 703 (lit c4))
  q149 : Ws → Eqn
  q149 c4 = eqn (CCZ012 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ012 ∷ []) (wl 704 (lit c4))
  q150 : Ws → Eqn
  q150 c4 = eqn (CX23 ∷ CCZ012 ∷ CCZ012 ∷ []) (CX23 ∷ []) (wl 705 (lit c4))
  q151 : Ws → Eqn
  q151 c4 = eqn (CCZ124 ∷ []) (CX23 ∷ CCZ124 ∷ CX23 ∷ []) (wl 257 (lit c4))

-- CXbc-box @1441: 17 steps
lem-CXbc-box-at1441 : Ws → ⟪ (CX23 ∷ Bx0-4231 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at1441 c4 = derive (CX23 ∷ Bx0-4231 ∷ CX23 ∷ []) (Bx0-4231 ∷ CCZ124 ∷ [])
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
  q152 c4 = eqn (CX32 ∷ Toff024 ∷ []) (Toff024 ∷ CX32 ∷ Toff034 ∷ []) (wp 588 c4)
  q153 : Ws → Eqn
  q153 c4 = eqn (CCZ013 ∷ Toff034 ∷ CCZ134 ∷ []) (Toff034 ∷ CCZ013 ∷ []) (wp 589 c4)
  q154 : Ws → Eqn
  q154 c4 = eqn (CCZ013 ∷ CX32 ∷ []) (CX32 ∷ CCZ013 ∷ []) (wl 706 (lit c4))
  q155 : Ws → Eqn
  q155 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) (wl 707 (lit c4))
  q156 : Ws → Eqn
  q156 c4 = eqn (CS14 ∷ Toff024 ∷ []) (Toff024 ∷ CS14 ∷ []) (wp 590 c4)
  q157 : Ws → Eqn
  q157 c4 = eqn (Toff024 ∷ Toff034 ∷ []) (Toff034 ∷ Toff024 ∷ []) (wp 591 c4)
  q158 : Ws → Eqn
  q158 c4 = eqn (CX32 ∷ Toff034 ∷ Toff034 ∷ []) (CX32 ∷ []) (wp 592 c4)
  q159 : Ws → Eqn
  q159 c4 = eqn (CCZ013 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ013 ∷ []) (wp 593 c4)
  q160 : Ws → Eqn
  q160 c4 = eqn (CCZ134 ∷ []) (CX32 ∷ CCZ134 ∷ CX32 ∷ []) (wl 254 (lit c4))

-- CXcb-box @1441: 18 steps
lem-CXcb-box-at1441 : Ws → ⟪ (CX32 ∷ Bx0-4231 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at1441 c4 = derive (CX32 ∷ Bx0-4231 ∷ CX32 ∷ []) (Bx0-4231 ∷ CCZ134 ∷ [])
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
  q161 c4 = eqn (Toff012 ∷ Toff012 ∷ []) [] (wl 162 (lit c4))
  q162 : Ws → Eqn
  q162 c4 = eqn (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (lem-VPQ-at14233241 c4)
  q163 : Ws → Eqn
  q163 c4 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wl 341 (lit c4))

-- QVQ @14233241: 3 steps
lem-QVQ-at14233241 : Ws → ⟪ (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ []) ⟫ʷ
lem-QVQ-at14233241 c4 = derive (CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ012 ∷ []) (Toff012 ∷ Toff034 ∷ CCZ034 ∷ Toff012 ∷ [])
  (rw⁻ 0 (q161 c4) ∷
   rw⁻ 1 (q162 c4) ∷
   rw 4 (q163 c4) ∷ []) Eq.refl

private
  q164 : Ws → Eqn
  q164 c4 = eqn (CS12⁻ ∷ S0 ∷ Toff012 ∷ S0⁻ ∷ []) (Toff012 ∷ CCZ012 ∷ []) (wl 158 (lit c4))
  q165 : Ws → Eqn
  q165 c4 = eqn (CS34⁻ ∷ S0 ∷ Toff034 ∷ S0⁻ ∷ []) (Toff034 ∷ CCZ034 ∷ []) (wp 5 c4)
  q166 : Ws → Eqn
  q166 c4 = eqn (S0⁻ ∷ CS34⁻ ∷ []) (CS34⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) ((CS • CS • CS) ↑ ↑))
  q167 : Ws → Eqn
  q167 c4 = eqn (Toff012 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS))
  q168 : Ws → Eqn
  q168 c4 = eqn (S0 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ S0 ∷ []) (c₁ (S) ((CS • CS • CS) ↑ ↑))
  q169 : Ws → Eqn
  q169 c4 = eqn (CS12⁻ ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (CS • CS • CS))
  q170 : Ws → Eqn
  q170 c4 = eqn (Toff012 ∷ Toff034 ∷ []) (Toff034 ∷ Toff012 ∷ []) (lem-tP-at12213443 c4)
  q171 : Ws → Eqn
  q171 c4 = eqn (S0 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ S0 ∷ []) (c₁ (S) (CS • CS • CS))
  q172 : Ws → Eqn
  q172 c4 = eqn (CS12⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF034 (lit c4))
  q173 : Ws → Eqn
  q173 c4 = eqn (S0⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (CS • CS • CS))

-- VPQ @12213443: 14 steps
lem-VPQ-at12213443 : Ws → ⟪ (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ
lem-VPQ-at12213443 c4 = derive (Toff012 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ []) (Toff034 ∷ CCZ034 ∷ Toff012 ∷ CCZ012 ∷ [])
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
  q174 c4 = eqn (Bx3-4102 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at0314213042 c4)
  q175 : Ws → Eqn
  q175 c4 = eqn (CX10 ∷ Toff314 ∷ []) (Toff314 ∷ CX10 ∷ []) (wp 662 c4)
  q176 : Ws → Eqn
  q176 c4 = eqn (CCZ023 ∷ CX10 ∷ CCZ123 ∷ []) (CX10 ∷ CCZ023 ∷ []) (wl 751 (lit c4))
  q177 : Ws → Eqn
  q177 c4 = eqn (CCZ123 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl 752 (lit c4))
  q178 : Ws → Eqn
  q178 c4 = eqn (CCZ124 ∷ []) (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl 334 (lit c4))
  q179 : Ws → Eqn
  q179 c4 = eqn (CCZ023 ∷ CS24 ∷ []) (CS24 ∷ CCZ023 ∷ []) (wp 513 c4)
  q180 : Ws → Eqn
  q180 c4 = eqn (CCZ023 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ023 ∷ []) (wl 620 (lit c4))
  q181 : Ws → Eqn
  q181 c4 = eqn (CCZ023 ∷ CS12 ∷ []) (CS12 ∷ CCZ023 ∷ []) (wl 621 (lit c4))
  q182 : Ws → Eqn
  q182 c4 = eqn (CX10 ∷ CCZ123 ∷ CCZ123 ∷ []) (CX10 ∷ []) (wl 753 (lit c4))
  q183 : Ws → Eqn
  q183 c4 = eqn (CCZ124 ∷ []) (CX10 ∷ CCZ124 ∷ CX10 ∷ []) (wp 663 c4)

-- CXbc-box @0314213042: 17 steps
lem-CXbc-box-at0314213042 : Ws → ⟪ (CX10 ∷ Bx3-4102 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at0314213042 c4 = derive (CX10 ∷ Bx3-4102 ∷ CX10 ∷ []) (Bx3-4102 ∷ CCZ124 ∷ [])
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
  q184 c4 = eqn (CX01 ∷ Toff314 ∷ []) (Toff314 ∷ CX01 ∷ Toff304 ∷ []) (wp 664 c4)
  q185 : Ws → Eqn
  q185 c4 = eqn (CCZ023 ∷ Toff304 ∷ CCZ024 ∷ []) (Toff304 ∷ CCZ023 ∷ []) (wp 665 c4)
  q186 : Ws → Eqn
  q186 c4 = eqn (CCZ023 ∷ CX01 ∷ []) (CX01 ∷ CCZ023 ∷ []) (wl 560 (lit c4))
  q187 : Ws → Eqn
  q187 c4 = eqn (CCZ024 ∷ []) (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) (wp 496 c4)
  q188 : Ws → Eqn
  q188 c4 = eqn (CS24 ∷ Toff314 ∷ []) (Toff314 ∷ CS24 ∷ []) (wl 754 (lit c4))
  q189 : Ws → Eqn
  q189 c4 = eqn (CX40 ∷ Toff314 ∷ []) (Toff314 ∷ CX40 ∷ []) (wp 666 c4)
  q190 : Ws → Eqn
  q190 c4 = eqn (CS02⁻ ∷ Toff314 ∷ []) (Toff314 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF314 (lit c4))
  q191 : Ws → Eqn
  q191 c4 = eqn (CS02 ∷ Toff314 ∷ []) (Toff314 ∷ CS02 ∷ []) (lem-comm-CS02-TOFF314 (lit c4))
  q192 : Ws → Eqn
  q192 c4 = eqn (Toff304 ∷ Toff314 ∷ []) (Toff314 ∷ Toff304 ∷ []) (wp 667 c4)
  q193 : Ws → Eqn
  q193 c4 = eqn (CX01 ∷ Toff304 ∷ Toff304 ∷ []) (CX01 ∷ []) (wp 668 c4)
  q194 : Ws → Eqn
  q194 c4 = eqn (CCZ023 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ023 ∷ []) (wp 669 c4)
  q195 : Ws → Eqn
  q195 c4 = eqn (CCZ024 ∷ []) (CX01 ∷ CCZ024 ∷ CX01 ∷ []) (wp 670 c4)

-- CXcb-box @0314213042: 18 steps
lem-CXcb-box-at0314213042 : Ws → ⟪ (CX01 ∷ Bx3-4102 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXcb-box-at0314213042 c4 = derive (CX01 ∷ Bx3-4102 ∷ CX01 ∷ []) (Bx3-4102 ∷ CCZ024 ∷ [])
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
  q196 c4 = eqn (Toff203 ∷ Toff214 ∷ []) (Toff214 ∷ Toff203 ∷ []) (lem-tP-at0213203441 c4)

-- VPQ @0213203441: 14 steps
lem-VPQ-at0213203441 : Ws → ⟪ (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at0213203441 c4 = derive (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ [])
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
  q197 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-box-tQ-at0210233441 c4)
  q198 : Ws → Eqn
  q198 c4 = eqn (CCZ124 ∷ CZ14 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ124 ∷ []) (wl 766 (lit c4))
  q199 : Ws → Eqn
  q199 c4 = eqn (CCZ124 ∷ CZ14 ∷ []) (Toff214 ∷ CCZ124 ∷ Toff214 ∷ []) (wl 767 (lit c4))
  q200 : Ws → Eqn
  q200 c4 = eqn (CZ14 ∷ Toff203 ∷ []) (Toff203 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF203 (lit c4))
  q201 : Ws → Eqn
  q201 c4 = eqn (CCZ124 ∷ []) (CZ14 ∷ CCZ124 ∷ CZ14 ∷ []) (wl 768 (lit c4))

-- P-box @0210233441: 8 steps
lem-P-box-at0210233441 : Ws → ⟪ (Toff214 ∷ Bx2-0341 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-P-box-at0210233441 c4 = derive (Toff214 ∷ Bx2-0341 ∷ Toff214 ∷ []) (Bx2-0341 ∷ [])
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
  q202 c4 = eqn (Bx3-4012 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203142 c4)
  q203 : Ws → Eqn
  q203 c4 = eqn (CX01 ∷ Toff304 ∷ []) (Toff304 ∷ CX01 ∷ []) (wp 688 c4)
  q204 : Ws → Eqn
  q204 c4 = eqn (CCZ123 ∷ CX01 ∷ CCZ023 ∷ []) (CX01 ∷ CCZ123 ∷ []) (wl 612 (lit c4))
  q205 : Ws → Eqn
  q205 c4 = eqn (CCZ023 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ023 ∷ CCZ024 ∷ []) (wp 689 c4)
  q206 : Ws → Eqn
  q206 c4 = eqn (CX40 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4))
  q207 : Ws → Eqn
  q207 c4 = eqn (CCZ123 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ123 ∷ []) (wl 611 (lit c4))
  q208 : Ws → Eqn
  q208 c4 = eqn (CCZ123 ∷ CS02 ∷ []) (CS02 ∷ CCZ123 ∷ []) (wl 171 (lit c4))
  q209 : Ws → Eqn
  q209 c4 = eqn (CX01 ∷ CCZ023 ∷ CCZ023 ∷ []) (CX01 ∷ []) (wl 614 (lit c4))

-- CXbc-box @0314203142: 17 steps
lem-CXbc-box-at0314203142 : Ws → ⟪ (CX01 ∷ Bx3-4012 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXbc-box-at0314203142 c4 = derive (CX01 ∷ Bx3-4012 ∷ CX01 ∷ []) (Bx3-4012 ∷ CCZ024 ∷ [])
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
  q210 c4 = eqn (CX10 ∷ Toff304 ∷ []) (Toff304 ∷ CX10 ∷ Toff314 ∷ []) (wp 690 c4)
  q211 : Ws → Eqn
  q211 c4 = eqn (CCZ123 ∷ Toff314 ∷ CCZ124 ∷ []) (Toff314 ∷ CCZ123 ∷ []) (wl 769 (lit c4))
  q212 : Ws → Eqn
  q212 c4 = eqn (CCZ123 ∷ CX10 ∷ []) (CX10 ∷ CCZ123 ∷ []) (wl 616 (lit c4))
  q213 : Ws → Eqn
  q213 c4 = eqn (CS24 ∷ Toff304 ∷ []) (Toff304 ∷ CS24 ∷ []) (wp 691 c4)
  q214 : Ws → Eqn
  q214 c4 = eqn (CX41 ∷ Toff304 ∷ []) (Toff304 ∷ CX41 ∷ []) (wp 692 c4)
  q215 : Ws → Eqn
  q215 c4 = eqn (CS12⁻ ∷ Toff304 ∷ []) (Toff304 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF304 (lit c4))
  q216 : Ws → Eqn
  q216 c4 = eqn (CS12 ∷ Toff304 ∷ []) (Toff304 ∷ CS12 ∷ []) (lem-comm-CS12-TOFF304 (lit c4))
  q217 : Ws → Eqn
  q217 c4 = eqn (CX10 ∷ Toff314 ∷ Toff314 ∷ []) (CX10 ∷ []) (wp 693 c4)
  q218 : Ws → Eqn
  q218 c4 = eqn (CCZ123 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ123 ∷ []) (wl 770 (lit c4))

-- CXcb-box @0314203142: 18 steps
lem-CXcb-box-at0314203142 : Ws → ⟪ (CX10 ∷ Bx3-4012 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at0314203142 c4 = derive (CX10 ∷ Bx3-4012 ∷ CX10 ∷ []) (Bx3-4012 ∷ CCZ124 ∷ [])
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
  q219 c4 = eqn (CS14⁻ ∷ S3 ∷ Toff314 ∷ S3⁻ ∷ []) (Toff314 ∷ CCZ134 ∷ []) (wl 783 (lit c4))
  q220 : Ws → Eqn
  q220 c4 = eqn (CS02⁻ ∷ S3 ∷ Toff302 ∷ S3⁻ ∷ []) (Toff302 ∷ CCZ023 ∷ []) (wl 784 (lit c4))
  q221 : Ws → Eqn
  q221 c4 = eqn (CS02⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S • S • S))
  q222 : Ws → Eqn
  q222 c4 = eqn (Toff314 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Toff314 ∷ []) (lem-comm-TOFF314-CSd02 (lit c4))
  q223 : Ws → Eqn
  q223 c4 = eqn (CS02⁻ ∷ S3 ∷ []) (S3 ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S))
  q224 : Ws → Eqn
  q224 c4 = eqn (CS02⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS02⁻ ∷ []) (wp 703 c4)
  q225 : Ws → Eqn
  q225 c4 = eqn (S3⁻ ∷ S3 ∷ []) [] (wl 441 (lit c4))
  q226 : Ws → Eqn
  q226 c4 = eqn (Toff314 ∷ Toff302 ∷ []) (Toff302 ∷ Toff314 ∷ []) (lem-tP-at0314213042 c4)
  q227 : Ws → Eqn
  q227 c4 = eqn (CS14⁻ ∷ S3 ∷ []) (S3 ∷ CS14⁻ ∷ []) (wl 785 (lit c4))
  q228 : Ws → Eqn
  q228 c4 = eqn (CS14⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF302 (lit c4))
  q229 : Ws → Eqn
  q229 c4 = eqn (CS14⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS14⁻ ∷ []) (wl 786 (lit c4))

-- VPQ @0314213042: 14 steps
lem-VPQ-at0314213042 : Ws → ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) ⟫ʷ
lem-VPQ-at0314213042 c4 = derive (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ [])
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
  q230 c4 = eqn (CCZ134 ∷ Toff314 ∷ CZ14 ∷ []) (Toff314 ∷ CCZ134 ∷ []) (wl 803 (lit c4))
  q231 : Ws → Eqn
  q231 c4 = eqn (CZ14 ∷ Toff302 ∷ []) (Toff302 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF302 (lit c4))
  q232 : Ws → Eqn
  q232 c4 = eqn (CCZ134 ∷ Toff314 ∷ []) (Toff314 ∷ CZ14 ∷ CCZ134 ∷ []) (wl 804 (lit c4))

-- t-cP @0314213042: 5 steps
lem-t-cP-at0314213042 : Ws → ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff314 ∷ []) ⟫ʷ
lem-t-cP-at0314213042 c4 = derive (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff314 ∷ [])
  (rw⁻ 0 (q230 c4) ∷
   rw 2 (q231 c4) ∷
   rw 1 (q226 c4) ∷
   rw⁻ 2 (q232 c4) ∷
   rw 3 (q226 c4) ∷ []) Eq.refl

private
  q233 : Ws → Eqn
  q233 c4 = eqn (Bx2-4103 ∷ []) (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (lem-box-tQ-at0214213043 c4)
  q234 : Ws → Eqn
  q234 c4 = eqn (CX10 ∷ Toff214 ∷ []) (Toff214 ∷ CX10 ∷ []) (wp 707 c4)
  q235 : Ws → Eqn
  q235 c4 = eqn (CCZ123 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ123 ∷ CCZ134 ∷ []) (wl 805 (lit c4))
  q236 : Ws → Eqn
  q236 c4 = eqn (CCZ134 ∷ []) (CX10 ∷ CCZ134 ∷ CX10 ∷ []) (wp 505 c4)

-- CXbc-box @0214213043: 17 steps
lem-CXbc-box-at0214213043 : Ws → ⟪ (CX10 ∷ Bx2-4103 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at0214213043 c4 = derive (CX10 ∷ Bx2-4103 ∷ CX10 ∷ []) (Bx2-4103 ∷ CCZ134 ∷ [])
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
  q237 c4 = eqn (CX01 ∷ Toff214 ∷ []) (Toff214 ∷ CX01 ∷ Toff204 ∷ []) (wp 708 c4)
  q238 : Ws → Eqn
  q238 c4 = eqn (CCZ023 ∷ Toff204 ∷ CCZ034 ∷ []) (Toff204 ∷ CCZ023 ∷ []) (wp 709 c4)
  q239 : Ws → Eqn
  q239 c4 = eqn (CCZ034 ∷ []) (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (wp 320 c4)
  q240 : Ws → Eqn
  q240 c4 = eqn (CS34 ∷ Toff214 ∷ []) (Toff214 ∷ CS34 ∷ []) (wl 761 (lit c4))
  q241 : Ws → Eqn
  q241 c4 = eqn (CX40 ∷ Toff214 ∷ []) (Toff214 ∷ CX40 ∷ []) (wp 710 c4)
  q242 : Ws → Eqn
  q242 c4 = eqn (CS03 ∷ Toff214 ∷ []) (Toff214 ∷ CS03 ∷ []) (lem-comm-CS03-TOFF214 (lit c4))
  q243 : Ws → Eqn
  q243 c4 = eqn (Toff204 ∷ Toff214 ∷ []) (Toff214 ∷ Toff204 ∷ []) (wp 503 c4)
  q244 : Ws → Eqn
  q244 c4 = eqn (CX01 ∷ Toff204 ∷ Toff204 ∷ []) (CX01 ∷ []) (wp 711 c4)
  q245 : Ws → Eqn
  q245 c4 = eqn (CCZ034 ∷ []) (CX01 ∷ CCZ034 ∷ CX01 ∷ []) (wp 499 c4)

-- CXcb-box @0214213043: 18 steps
lem-CXcb-box-at0214213043 : Ws → ⟪ (CX01 ∷ Bx2-4103 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXcb-box-at0214213043 c4 = derive (CX01 ∷ Bx2-4103 ∷ CX01 ∷ []) (Bx2-4103 ∷ CCZ034 ∷ [])
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
  q246 c4 = eqn (Toff014 ∷ Toff023 ∷ []) (Toff023 ∷ Toff014 ∷ []) (lem-tP-at243243 c4)
  q247 : Ws → Eqn
  q247 c4 = eqn (CCZ023 ∷ CZ23 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ023 ∷ []) (wl 825 (lit c4))
  q248 : Ws → Eqn
  q248 c4 = eqn (CCZ023 ∷ CZ23 ∷ []) (Toff023 ∷ CCZ023 ∷ Toff023 ∷ []) (wl 826 (lit c4))
  q249 : Ws → Eqn
  q249 c4 = eqn (CZ23 ∷ Toff014 ∷ []) (Toff014 ∷ CZ23 ∷ []) (lem-comm-CZ23-TOFF014 (lit c4))
  q250 : Ws → Eqn
  q250 c4 = eqn (CCZ023 ∷ []) (CZ23 ∷ CCZ023 ∷ CZ23 ∷ []) (wl 827 (lit c4))

-- P-box @243243: 8 steps
lem-P-box-at243243 : Ws → ⟪ (Toff023 ∷ Bx0-1423 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-P-box-at243243 c4 = derive (Toff023 ∷ Bx0-1423 ∷ Toff023 ∷ []) (Bx0-1423 ∷ [])
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
  q251 c4 = eqn (Bx0-3214 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at1331 c4)
  q252 : Ws → Eqn
  q252 c4 = eqn (CX21 ∷ Toff023 ∷ []) (Toff023 ∷ CX21 ∷ []) (wl 828 (lit c4))
  q253 : Ws → Eqn
  q253 c4 = eqn (CCZ014 ∷ CX21 ∷ CCZ024 ∷ []) (CX21 ∷ CCZ014 ∷ []) (wp 720 c4)
  q254 : Ws → Eqn
  q254 c4 = eqn (CCZ024 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp 721 c4)
  q255 : Ws → Eqn
  q255 c4 = eqn (CCZ234 ∷ []) (CS24 ∷ CX32 ∷ CS24⁻ ∷ CX32 ∷ CS34 ∷ []) (wl 829 (lit c4))
  q256 : Ws → Eqn
  q256 c4 = eqn (CCZ014 ∷ CS34 ∷ []) (CS34 ∷ CCZ014 ∷ []) (wp 64 c4)
  q257 : Ws → Eqn
  q257 c4 = eqn (CX32 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 (lit c4))
  q258 : Ws → Eqn
  q258 c4 = eqn (CCZ014 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ014 ∷ []) (wp 722 c4)
  q259 : Ws → Eqn
  q259 c4 = eqn (CCZ014 ∷ CS24 ∷ []) (CS24 ∷ CCZ014 ∷ []) (wp 62 c4)
  q260 : Ws → Eqn
  q260 c4 = eqn (CCZ014 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ014 ∷ []) (wp 38 c4)
  q261 : Ws → Eqn
  q261 c4 = eqn (CX21 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX21 ∷ []) (wp 723 c4)

-- CXbc-box @1331: 17 steps
lem-CXbc-box-at1331 : Ws → ⟪ (CX21 ∷ Bx0-3214 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXbc-box-at1331 c4 = derive (CX21 ∷ Bx0-3214 ∷ CX21 ∷ []) (Bx0-3214 ∷ CCZ234 ∷ [])
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
  q262 c4 = eqn (CX12 ∷ Toff023 ∷ []) (Toff023 ∷ CX12 ∷ Toff013 ∷ []) (wl 830 (lit c4))
  q263 : Ws → Eqn
  q263 c4 = eqn (CCZ014 ∷ Toff013 ∷ CCZ134 ∷ []) (Toff013 ∷ CCZ014 ∷ []) (wp 724 c4)
  q264 : Ws → Eqn
  q264 c4 = eqn (CCZ014 ∷ CX12 ∷ []) (CX12 ∷ CCZ014 ∷ []) (wp 54 c4)
  q265 : Ws → Eqn
  q265 c4 = eqn (CCZ134 ∷ []) (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (wl 831 (lit c4))
  q266 : Ws → Eqn
  q266 c4 = eqn (CS34 ∷ Toff023 ∷ []) (Toff023 ∷ CS34 ∷ []) (wp 725 c4)
  q267 : Ws → Eqn
  q267 c4 = eqn (CX31 ∷ Toff023 ∷ []) (Toff023 ∷ CX31 ∷ []) (wl 832 (lit c4))
  q268 : Ws → Eqn
  q268 c4 = eqn (CS14⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF023 (lit c4))
  q269 : Ws → Eqn
  q269 c4 = eqn (CS14 ∷ Toff023 ∷ []) (Toff023 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF023 (lit c4))
  q270 : Ws → Eqn
  q270 c4 = eqn (Toff013 ∷ Toff023 ∷ []) (Toff023 ∷ Toff013 ∷ []) (wl 833 (lit c4))
  q271 : Ws → Eqn
  q271 c4 = eqn (CX12 ∷ Toff013 ∷ Toff013 ∷ []) (CX12 ∷ []) (wl 834 (lit c4))
  q272 : Ws → Eqn
  q272 c4 = eqn (CCZ014 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ014 ∷ []) (wp 272 c4)

-- CXcb-box @1331: 18 steps
lem-CXcb-box-at1331 : Ws → ⟪ (CX12 ∷ Bx0-3214 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at1331 c4 = derive (CX12 ∷ Bx0-3214 ∷ CX12 ∷ []) (Bx0-3214 ∷ CCZ134 ∷ [])
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
  q273 c4 = eqn (Toff324 ∷ Toff324 ∷ []) [] (wl 442 (lit c4))
  q274 : Ws → Eqn
  q274 c4 = eqn (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (lem-VPQ-at032032 c4)

-- QVQ @032032: 3 steps
lem-QVQ-at032032 : Ws → ⟪ (CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ
lem-QVQ-at032032 c4 = derive (CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ234 ∷ []) (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ [])
  (rw⁻ 0 (q273 c4) ∷
   rw⁻ 1 (q274 c4) ∷
   rw 4 (q124 c4) ∷ []) Eq.refl

private
  q275 : Ws → Eqn
  q275 c4 = eqn (Bx3-2410 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at0312243140 c4)
  q276 : Ws → Eqn
  q276 c4 = eqn (CX41 ∷ Toff324 ∷ []) (Toff324 ∷ CX41 ∷ []) (wl 848 (lit c4))
  q277 : Ws → Eqn
  q277 c4 = eqn (CCZ013 ∷ CX41 ∷ CCZ034 ∷ []) (CX41 ∷ CCZ013 ∷ []) (wp 182 c4)
  q278 : Ws → Eqn
  q278 c4 = eqn (CCZ034 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp 726 c4)
  q279 : Ws → Eqn
  q279 c4 = eqn (CCZ024 ∷ []) (CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ []) (wp 75 c4)
  q280 : Ws → Eqn
  q280 c4 = eqn (CCZ013 ∷ CS02 ∷ []) (CS02 ∷ CCZ013 ∷ []) (wl 225 (lit c4))
  q281 : Ws → Eqn
  q281 c4 = eqn (CCZ013 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ013 ∷ []) (wp 76 c4)
  q282 : Ws → Eqn
  q282 c4 = eqn (CCZ013 ∷ CS04 ∷ []) (CS04 ∷ CCZ013 ∷ []) (wp 77 c4)
  q283 : Ws → Eqn
  q283 c4 = eqn (CCZ013 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ013 ∷ []) (wp 186 c4)
  q284 : Ws → Eqn
  q284 c4 = eqn (CX41 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX41 ∷ []) (wp 187 c4)
  q285 : Ws → Eqn
  q285 c4 = eqn (CCZ024 ∷ []) (CX41 ∷ CCZ024 ∷ CX41 ∷ []) (wp 727 c4)

-- CXbc-box @0312243140: 17 steps
lem-CXbc-box-at0312243140 : Ws → ⟪ (CX41 ∷ Bx3-2410 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXbc-box-at0312243140 c4 = derive (CX41 ∷ Bx3-2410 ∷ CX41 ∷ []) (Bx3-2410 ∷ CCZ024 ∷ [])
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
  q286 c4 = eqn (CX14 ∷ Toff324 ∷ []) (Toff324 ∷ CX14 ∷ Toff312 ∷ []) (wl 849 (lit c4))
  q287 : Ws → Eqn
  q287 c4 = eqn (CCZ013 ∷ Toff312 ∷ CCZ012 ∷ []) (Toff312 ∷ CCZ013 ∷ []) (wl 850 (lit c4))
  q288 : Ws → Eqn
  q288 c4 = eqn (CCZ013 ∷ CX14 ∷ []) (CX14 ∷ CCZ013 ∷ []) (wp 189 c4)
  q289 : Ws → Eqn
  q289 c4 = eqn (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wl 270 (lit c4))
  q290 : Ws → Eqn
  q290 c4 = eqn (CS02 ∷ Toff324 ∷ []) (Toff324 ∷ CS02 ∷ []) (wp 298 c4)
  q291 : Ws → Eqn
  q291 c4 = eqn (CX21 ∷ Toff324 ∷ []) (Toff324 ∷ CX21 ∷ []) (wl 851 (lit c4))
  q292 : Ws → Eqn
  q292 c4 = eqn (CS01⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI))
  q293 : Ws → Eqn
  q293 c4 = eqn (CS01 ∷ Toff324 ∷ []) (Toff324 ∷ CS01 ∷ []) (c₂ (CS) (K ↑ • CCZ • K ↑ • iI))
  q294 : Ws → Eqn
  q294 c4 = eqn (Toff312 ∷ Toff324 ∷ []) (Toff324 ∷ Toff312 ∷ []) (wl 852 (lit c4))
  q295 : Ws → Eqn
  q295 c4 = eqn (CX14 ∷ Toff312 ∷ Toff312 ∷ []) (CX14 ∷ []) (wl 853 (lit c4))
  q296 : Ws → Eqn
  q296 c4 = eqn (CCZ012 ∷ []) (CX14 ∷ CCZ012 ∷ CX14 ∷ []) (wp 728 c4)

-- CXcb-box @0312243140: 18 steps
lem-CXcb-box-at0312243140 : Ws → ⟪ (CX14 ∷ Bx3-2410 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXcb-box-at0312243140 c4 = derive (CX14 ∷ Bx3-2410 ∷ CX14 ∷ []) (Bx3-2410 ∷ CCZ012 ∷ [])
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
  q297 c4 = eqn (Bx3-2140 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at0312213440 c4)
  q298 : Ws → Eqn
  q298 c4 = eqn (CX14 ∷ Toff312 ∷ []) (Toff312 ∷ CX14 ∷ []) (wl 858 (lit c4))
  q299 : Ws → Eqn
  q299 c4 = eqn (CCZ034 ∷ CX14 ∷ CCZ013 ∷ []) (CX14 ∷ CCZ034 ∷ []) (wp 735 c4)
  q300 : Ws → Eqn
  q300 c4 = eqn (CCZ013 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ013 ∷ CCZ012 ∷ []) (wl 859 (lit c4))
  q301 : Ws → Eqn
  q301 c4 = eqn (CCZ034 ∷ CS02 ∷ []) (CS02 ∷ CCZ034 ∷ []) (wp 3 c4)
  q302 : Ws → Eqn
  q302 c4 = eqn (CX21 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4))
  q303 : Ws → Eqn
  q303 c4 = eqn (CCZ034 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ034 ∷ []) (wp 120 c4)
  q304 : Ws → Eqn
  q304 c4 = eqn (CCZ034 ∷ CS01 ∷ []) (CS01 ∷ CCZ034 ∷ []) (wp 1 c4)
  q305 : Ws → Eqn
  q305 c4 = eqn (CX14 ∷ CCZ013 ∷ CCZ013 ∷ []) (CX14 ∷ []) (wp 736 c4)

-- CXbc-box @0312213440: 17 steps
lem-CXbc-box-at0312213440 : Ws → ⟪ (CX14 ∷ Bx3-2140 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXbc-box-at0312213440 c4 = derive (CX14 ∷ Bx3-2140 ∷ CX14 ∷ []) (Bx3-2140 ∷ CCZ012 ∷ [])
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
  q306 c4 = eqn (CX41 ∷ Toff312 ∷ []) (Toff312 ∷ CX41 ∷ Toff324 ∷ []) (wl 860 (lit c4))
  q307 : Ws → Eqn
  q307 c4 = eqn (CCZ034 ∷ Toff324 ∷ CCZ024 ∷ []) (Toff324 ∷ CCZ034 ∷ []) (wp 737 c4)
  q308 : Ws → Eqn
  q308 c4 = eqn (CCZ034 ∷ CX41 ∷ []) (CX41 ∷ CCZ034 ∷ []) (wp 357 c4)
  q309 : Ws → Eqn
  q309 c4 = eqn (CS02 ∷ Toff312 ∷ []) (Toff312 ∷ CS02 ∷ []) (wl 861 (lit c4))
  q310 : Ws → Eqn
  q310 c4 = eqn (CX24 ∷ Toff312 ∷ []) (Toff312 ∷ CX24 ∷ []) (wl 862 (lit c4))
  q311 : Ws → Eqn
  q311 c4 = eqn (CS04⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF312 (lit c4))
  q312 : Ws → Eqn
  q312 c4 = eqn (CS04 ∷ Toff312 ∷ []) (Toff312 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF312 (lit c4))
  q313 : Ws → Eqn
  q313 c4 = eqn (CX41 ∷ Toff324 ∷ Toff324 ∷ []) (CX41 ∷ []) (wl 863 (lit c4))
  q314 : Ws → Eqn
  q314 c4 = eqn (CCZ024 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ024 ∷ []) (wp 109 c4)

-- CXcb-box @0312213440: 18 steps
lem-CXcb-box-at0312213440 : Ws → ⟪ (CX41 ∷ Bx3-2140 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXcb-box-at0312213440 c4 = derive (CX41 ∷ Bx3-2140 ∷ CX41 ∷ []) (Bx3-2140 ∷ CCZ024 ∷ [])
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
  q315 c4 = eqn (Toff324 ∷ Toff301 ∷ []) (Toff301 ∷ Toff324 ∷ []) (lem-tP-at0312243140 c4)
  q316 : Ws → Eqn
  q316 c4 = eqn (CCZ013 ∷ CZ01 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ013 ∷ []) (wl 866 (lit c4))
  q317 : Ws → Eqn
  q317 c4 = eqn (CCZ013 ∷ CZ01 ∷ []) (Toff301 ∷ CCZ013 ∷ Toff301 ∷ []) (wl 867 (lit c4))
  q318 : Ws → Eqn
  q318 c4 = eqn (CZ01 ∷ Toff324 ∷ []) (Toff324 ∷ CZ01 ∷ []) (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI))
  q319 : Ws → Eqn
  q319 c4 = eqn (CCZ013 ∷ []) (CZ01 ∷ CCZ013 ∷ CZ01 ∷ []) (wl 868 (lit c4))

-- P-box @0312243140: 8 steps
lem-P-box-at0312243140 : Ws → ⟪ (Toff301 ∷ Bx3-2410 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2410 ∷ []) ⟫ʷ
lem-P-box-at0312243140 c4 = derive (Toff301 ∷ Bx3-2410 ∷ Toff301 ∷ []) (Bx3-2410 ∷ [])
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
  q320 c4 = eqn (CS24⁻ ∷ S3 ∷ Toff324 ∷ S3⁻ ∷ []) (Toff324 ∷ CCZ234 ∷ []) (wl 438 (lit c4))
  q321 : Ws → Eqn
  q321 c4 = eqn (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) (Toff301 ∷ CCZ013 ∷ []) (wl 437 (lit c4))
  q322 : Ws → Eqn
  q322 c4 = eqn (CS01⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((S • S • S) ↑))
  q323 : Ws → Eqn
  q323 c4 = eqn (CS01⁻ ∷ S3 ∷ []) (S3 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S ↑))
  q324 : Ws → Eqn
  q324 c4 = eqn (CS01⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q325 : Ws → Eqn
  q325 c4 = eqn (CS24⁻ ∷ S3 ∷ []) (S3 ∷ CS24⁻ ∷ []) (wl 440 (lit c4))
  q326 : Ws → Eqn
  q326 c4 = eqn (CS24⁻ ∷ Toff301 ∷ []) (Toff301 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF301 (lit c4))
  q327 : Ws → Eqn
  q327 c4 = eqn (CS24⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS24⁻ ∷ []) (wl 439 (lit c4))

-- VPQ @0312243140: 14 steps
lem-VPQ-at0312243140 : Ws → ⟪ (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) ⟫ʷ
lem-VPQ-at0312243140 c4 = derive (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ [])
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
  q328 c4 = eqn (Bx0-3124 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at132132 c4)
  q329 : Ws → Eqn
  q329 c4 = eqn (CX12 ∷ Toff013 ∷ []) (Toff013 ∷ CX12 ∷ []) (wl 872 (lit c4))
  q330 : Ws → Eqn
  q330 c4 = eqn (CCZ024 ∷ CX12 ∷ CCZ014 ∷ []) (CX12 ∷ CCZ024 ∷ []) (wp 744 c4)
  q331 : Ws → Eqn
  q331 c4 = eqn (CCZ014 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ014 ∷ CCZ134 ∷ []) (wp 745 c4)
  q332 : Ws → Eqn
  q332 c4 = eqn (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) (wp 36 c4)
  q333 : Ws → Eqn
  q333 c4 = eqn (CX31 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4))
  q334 : Ws → Eqn
  q334 c4 = eqn (CCZ024 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ024 ∷ []) (wp 746 c4)
  q335 : Ws → Eqn
  q335 c4 = eqn (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) (wp 34 c4)
  q336 : Ws → Eqn
  q336 c4 = eqn (CX12 ∷ CCZ014 ∷ CCZ014 ∷ []) (CX12 ∷ []) (wp 747 c4)

-- CXbc-box @132132: 17 steps
lem-CXbc-box-at132132 : Ws → ⟪ (CX12 ∷ Bx0-3124 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at132132 c4 = derive (CX12 ∷ Bx0-3124 ∷ CX12 ∷ []) (Bx0-3124 ∷ CCZ134 ∷ [])
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
  q337 c4 = eqn (CX21 ∷ Toff013 ∷ []) (Toff013 ∷ CX21 ∷ Toff023 ∷ []) (wl 873 (lit c4))
  q338 : Ws → Eqn
  q338 c4 = eqn (CCZ024 ∷ Toff023 ∷ CCZ234 ∷ []) (Toff023 ∷ CCZ024 ∷ []) (wp 748 c4)
  q339 : Ws → Eqn
  q339 c4 = eqn (CCZ024 ∷ CX21 ∷ []) (CX21 ∷ CCZ024 ∷ []) (wp 749 c4)
  q340 : Ws → Eqn
  q340 c4 = eqn (CS34 ∷ Toff013 ∷ []) (Toff013 ∷ CS34 ∷ []) (wp 95 c4)
  q341 : Ws → Eqn
  q341 c4 = eqn (CX32 ∷ Toff013 ∷ []) (Toff013 ∷ CX32 ∷ []) (wl 874 (lit c4))
  q342 : Ws → Eqn
  q342 c4 = eqn (CS24 ∷ Toff013 ∷ []) (Toff013 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF013 (lit c4))
  q343 : Ws → Eqn
  q343 c4 = eqn (CX21 ∷ Toff023 ∷ Toff023 ∷ []) (CX21 ∷ []) (wl 875 (lit c4))
  q344 : Ws → Eqn
  q344 c4 = eqn (CCZ024 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ024 ∷ []) (wp 90 c4)

-- CXcb-box @132132: 18 steps
lem-CXcb-box-at132132 : Ws → ⟪ (CX21 ∷ Bx0-3124 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXcb-box-at132132 c4 = derive (CX21 ∷ Bx0-3124 ∷ CX21 ∷ []) (Bx0-3124 ∷ CCZ234 ∷ [])
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
  q345 c4 = eqn (Toff204 ∷ Toff213 ∷ []) (Toff213 ∷ Toff204 ∷ []) (lem-tP-at0210243143 c4)
  q346 : Ws → Eqn
  q346 c4 = eqn (CCZ123 ∷ CZ13 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ123 ∷ []) (wl 912 (lit c4))
  q347 : Ws → Eqn
  q347 c4 = eqn (CCZ123 ∷ CZ13 ∷ []) (Toff213 ∷ CCZ123 ∷ Toff213 ∷ []) (wl 913 (lit c4))
  q348 : Ws → Eqn
  q348 c4 = eqn (CZ13 ∷ Toff204 ∷ []) (Toff204 ∷ CZ13 ∷ []) (lem-comm-CZ13-TOFF204 (lit c4))
  q349 : Ws → Eqn
  q349 c4 = eqn (CCZ123 ∷ []) (CZ13 ∷ CCZ123 ∷ CZ13 ∷ []) (wl 914 (lit c4))

-- P-box @0210243143: 8 steps
lem-P-box-at0210243143 : Ws → ⟪ (Toff213 ∷ Bx2-0413 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-P-box-at0210243143 c4 = derive (Toff213 ∷ Bx2-0413 ∷ Toff213 ∷ []) (Bx2-0413 ∷ [])
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
  q350 c4 = eqn (Bx2-1304 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at022330 c4)
  q351 : Ws → Eqn
  q351 c4 = eqn (CX30 ∷ Toff213 ∷ []) (Toff213 ∷ CX30 ∷ []) (wl 917 (lit c4))
  q352 : Ws → Eqn
  q352 c4 = eqn (CCZ024 ∷ CX30 ∷ CCZ234 ∷ []) (CX30 ∷ CCZ024 ∷ []) (wp 757 c4)
  q353 : Ws → Eqn
  q353 c4 = eqn (CCZ234 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ234 ∷ CCZ134 ∷ []) (wl 918 (lit c4))
  q354 : Ws → Eqn
  q354 c4 = eqn (CCZ134 ∷ []) (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl 166 (lit c4))
  q355 : Ws → Eqn
  q355 c4 = eqn (CX13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4))
  q356 : Ws → Eqn
  q356 c4 = eqn (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) (wp 35 c4)
  q357 : Ws → Eqn
  q357 c4 = eqn (CX30 ∷ CCZ234 ∷ CCZ234 ∷ []) (CX30 ∷ []) (wp 758 c4)
  q358 : Ws → Eqn
  q358 c4 = eqn (CCZ134 ∷ []) (CX30 ∷ CCZ134 ∷ CX30 ∷ []) (wp 759 c4)

-- CXbc-box @022330: 17 steps
lem-CXbc-box-at022330 : Ws → ⟪ (CX30 ∷ Bx2-1304 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at022330 c4 = derive (CX30 ∷ Bx2-1304 ∷ CX30 ∷ []) (Bx2-1304 ∷ CCZ134 ∷ [])
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
  q359 c4 = eqn (CX03 ∷ Toff213 ∷ []) (Toff213 ∷ CX03 ∷ Toff201 ∷ []) (wl 919 (lit c4))
  q360 : Ws → Eqn
  q360 c4 = eqn (CCZ024 ∷ Toff201 ∷ CCZ014 ∷ []) (Toff201 ∷ CCZ024 ∷ []) (wp 760 c4)
  q361 : Ws → Eqn
  q361 c4 = eqn (CCZ024 ∷ CX03 ∷ []) (CX03 ∷ CCZ024 ∷ []) (wp 756 c4)
  q362 : Ws → Eqn
  q362 c4 = eqn (CCZ014 ∷ []) (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (wp 341 c4)
  q363 : Ws → Eqn
  q363 c4 = eqn (CS14 ∷ Toff213 ∷ []) (Toff213 ∷ CS14 ∷ []) (wl 195 (lit c4))
  q364 : Ws → Eqn
  q364 c4 = eqn (CX10 ∷ Toff213 ∷ []) (Toff213 ∷ CX10 ∷ []) (wl 920 (lit c4))
  q365 : Ws → Eqn
  q365 c4 = eqn (CS04⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 (lit c4))
  q366 : Ws → Eqn
  q366 c4 = eqn (CS04 ∷ Toff213 ∷ []) (Toff213 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF213 (lit c4))
  q367 : Ws → Eqn
  q367 c4 = eqn (Toff201 ∷ Toff213 ∷ []) (Toff213 ∷ Toff201 ∷ []) (wl 921 (lit c4))
  q368 : Ws → Eqn
  q368 c4 = eqn (CX03 ∷ Toff201 ∷ Toff201 ∷ []) (CX03 ∷ []) (wl 922 (lit c4))
  q369 : Ws → Eqn
  q369 c4 = eqn (CCZ014 ∷ []) (CX03 ∷ CCZ014 ∷ CX03 ∷ []) (wp 761 c4)

-- CXcb-box @022330: 18 steps
lem-CXcb-box-at022330 : Ws → ⟪ (CX03 ∷ Bx2-1304 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at022330 c4 = derive (CX03 ∷ Bx2-1304 ∷ CX03 ∷ []) (Bx2-1304 ∷ CCZ014 ∷ [])
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
  q370 c4 = eqn (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) (lem-VPQ-at0220 c4)

-- QVQ @0220: 3 steps
lem-QVQ-at0220 : Ws → ⟪ (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ []) ⟫ʷ
lem-QVQ-at0220 c4 = derive (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ [])
  (rw⁻ 0 (q122 c4) ∷
   rw⁻ 1 (q370 c4) ∷
   rw 4 (q124 c4) ∷ []) Eq.refl

private
  q371 : Ws → Eqn
  q371 c4 = eqn (CX41 ∷ CX14 ∷ CX41 ∷ []) (Sw14 ∷ []) (wl 300 (lit c4))
  q372 : Ws → Eqn
  q372 c4 = eqn (CX41 ∷ Bx2-3410 ∷ CX41 ∷ []) (Bx2-3410 ∷ CCZ034 ∷ []) (lem-CXbc-box-at0213243140 c4)
  q373 : Ws → Eqn
  q373 c4 = eqn (CCZ034 ∷ CX14 ∷ []) (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) (wp 566 c4)
  q374 : Ws → Eqn
  q374 c4 = eqn (CX14 ∷ Bx2-3410 ∷ CX14 ∷ []) (Bx2-3410 ∷ CCZ013 ∷ []) (lem-CXcb-box-at0213243140 c4)
  q375 : Ws → Eqn
  q375 c4 = eqn (CCZ013 ∷ CX41 ∷ []) (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) (wp 567 c4)
  q376 : Ws → Eqn
  q376 c4 = eqn (CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ []) (CCZ034 ∷ []) (wp 568 c4)
  q377 : Ws → Eqn
  q377 c4 = eqn (CCZ034 ∷ CCZ034 ∷ []) [] (wp 7 c4)

-- SWbc-box @0213243140: 11 steps
lem-SWbc-box-at0213243140 : Ws → ⟪ (Sw14 ∷ Bx2-3410 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ []) ⟫ʷ
lem-SWbc-box-at0213243140 c4 = derive (Sw14 ∷ Bx2-3410 ∷ Sw14 ∷ []) (Bx2-3410 ∷ [])
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
  q378 c4 = eqn (Bx2-3140 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at0213213440 c4)
  q379 : Ws → Eqn
  q379 c4 = eqn (CX14 ∷ Toff213 ∷ []) (Toff213 ∷ CX14 ∷ []) (wl 944 (lit c4))
  q380 : Ws → Eqn
  q380 c4 = eqn (CCZ024 ∷ CX14 ∷ CCZ012 ∷ []) (CX14 ∷ CCZ024 ∷ []) (wp 282 c4)
  q381 : Ws → Eqn
  q381 c4 = eqn (CCZ012 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ012 ∷ CCZ013 ∷ []) (wl 945 (lit c4))
  q382 : Ws → Eqn
  q382 c4 = eqn (CCZ013 ∷ []) (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl 323 (lit c4))
  q383 : Ws → Eqn
  q383 c4 = eqn (CCZ024 ∷ CS03 ∷ []) (CS03 ∷ CCZ024 ∷ []) (wp 21 c4)
  q384 : Ws → Eqn
  q384 c4 = eqn (CCZ024 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ024 ∷ []) (wp 179 c4)
  q385 : Ws → Eqn
  q385 c4 = eqn (CCZ024 ∷ CS01 ∷ []) (CS01 ∷ CCZ024 ∷ []) (wp 39 c4)
  q386 : Ws → Eqn
  q386 c4 = eqn (CCZ012 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ012 ∷ []) (wp 142 c4)
  q387 : Ws → Eqn
  q387 c4 = eqn (CX14 ∷ CCZ012 ∷ CCZ012 ∷ []) (CX14 ∷ []) (wp 283 c4)

-- CXbc-box @0213213440: 17 steps
lem-CXbc-box-at0213213440 : Ws → ⟪ (CX14 ∷ Bx2-3140 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXbc-box-at0213213440 c4 = derive (CX14 ∷ Bx2-3140 ∷ CX14 ∷ []) (Bx2-3140 ∷ CCZ013 ∷ [])
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
  q388 c4 = eqn (CX41 ∷ Toff213 ∷ []) (Toff213 ∷ CX41 ∷ Toff234 ∷ []) (wl 946 (lit c4))
  q389 : Ws → Eqn
  q389 c4 = eqn (CCZ024 ∷ Toff234 ∷ CCZ034 ∷ []) (Toff234 ∷ CCZ024 ∷ []) (wp 768 c4)
  q390 : Ws → Eqn
  q390 c4 = eqn (CCZ024 ∷ CX41 ∷ []) (CX41 ∷ CCZ024 ∷ []) (wp 285 c4)
  q391 : Ws → Eqn
  q391 c4 = eqn (CCZ034 ∷ []) (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) (wp 115 c4)
  q392 : Ws → Eqn
  q392 c4 = eqn (CS03 ∷ Toff213 ∷ []) (Toff213 ∷ CS03 ∷ []) (wl 196 (lit c4))
  q393 : Ws → Eqn
  q393 c4 = eqn (CX34 ∷ Toff213 ∷ []) (Toff213 ∷ CX34 ∷ []) (wl 947 (lit c4))
  q394 : Ws → Eqn
  q394 c4 = eqn (Toff213 ∷ Toff234 ∷ []) (Toff234 ∷ Toff213 ∷ []) (wl 942 (lit c4))
  q395 : Ws → Eqn
  q395 c4 = eqn (CX41 ∷ Toff234 ∷ Toff234 ∷ []) (CX41 ∷ []) (wl 948 (lit c4))

-- CXcb-box @0213213440: 18 steps
lem-CXcb-box-at0213213440 : Ws → ⟪ (CX41 ∷ Bx2-3140 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXcb-box-at0213213440 c4 = derive (CX41 ∷ Bx2-3140 ∷ CX41 ∷ []) (Bx2-3140 ∷ CCZ034 ∷ [])
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
  q396 c4 = eqn (Toff201 ∷ Toff201 ∷ []) [] (wl 421 (lit c4))
  q397 : Ws → Eqn
  q397 c4 = eqn (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) (lem-VPQ-at0213243140 c4)

-- QVQ @0213243140: 3 steps
lem-QVQ-at0213243140 : Ws → ⟪ (CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ []) ⟫ʷ
lem-QVQ-at0213243140 c4 = derive (CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ012 ∷ []) (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ [])
  (rw⁻ 0 (q396 c4) ∷
   rw⁻ 1 (q397 c4) ∷
   rw 4 (q163 c4) ∷ []) Eq.refl

private
  q398 : Ws → Eqn
  q398 c4 = eqn (CX03 ∷ CX30 ∷ CX03 ∷ []) (Sw03 ∷ []) (wl 961 (lit c4))
  q399 : Ws → Eqn
  q399 c4 = eqn (CX03 ∷ Bx2-1034 ∷ CX03 ∷ []) (Bx2-1034 ∷ CCZ014 ∷ []) (lem-CXbc-box-at0220 c4)
  q400 : Ws → Eqn
  q400 c4 = eqn (CCZ014 ∷ CX30 ∷ []) (CX30 ∷ CCZ134 ∷ CCZ014 ∷ []) (wp 763 c4)
  q401 : Ws → Eqn
  q401 c4 = eqn (CX30 ∷ Bx2-1034 ∷ CX30 ∷ []) (Bx2-1034 ∷ CCZ134 ∷ []) (lem-CXcb-box-at0220 c4)
  q402 : Ws → Eqn
  q402 c4 = eqn (CCZ014 ∷ CX03 ∷ []) (CX03 ∷ CCZ014 ∷ []) (wp 778 c4)
  q403 : Ws → Eqn
  q403 c4 = eqn (CCZ134 ∷ CX03 ∷ []) (CX03 ∷ CCZ014 ∷ CCZ134 ∷ []) (wp 762 c4)
  q404 : Ws → Eqn
  q404 c4 = eqn (CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ []) (CCZ014 ∷ []) (wp 779 c4)
  q405 : Ws → Eqn
  q405 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp 161 c4)

-- SWbc-box @0220: 11 steps
lem-SWbc-box-at0220 : Ws → ⟪ (Sw03 ∷ Bx2-1034 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-SWbc-box-at0220 c4 = derive (Sw03 ∷ Bx2-1034 ∷ Sw03 ∷ []) (Bx2-1034 ∷ [])
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
  q406 c4 = eqn (Toff213 ∷ Toff204 ∷ []) (Toff204 ∷ Toff213 ∷ []) (lem-tP-at022330 c4)
  q407 : Ws → Eqn
  q407 c4 = eqn (CCZ024 ∷ CZ04 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ024 ∷ []) (wp 780 c4)
  q408 : Ws → Eqn
  q408 c4 = eqn (CCZ024 ∷ CZ04 ∷ []) (Toff204 ∷ CCZ024 ∷ Toff204 ∷ []) (wp 781 c4)
  q409 : Ws → Eqn
  q409 c4 = eqn (CZ04 ∷ Toff213 ∷ []) (Toff213 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF213 (lit c4))
  q410 : Ws → Eqn
  q410 c4 = eqn (CCZ024 ∷ []) (CZ04 ∷ CCZ024 ∷ CZ04 ∷ []) (wp 782 c4)

-- P-box @022330: 8 steps
lem-P-box-at022330 : Ws → ⟪ (Toff204 ∷ Bx2-1304 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-P-box-at022330 c4 = derive (Toff204 ∷ Bx2-1304 ∷ Toff204 ∷ []) (Bx2-1304 ∷ [])
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
  q411 c4 = eqn (CS13⁻ ∷ S2 ∷ Toff213 ∷ S2⁻ ∷ []) (Toff213 ∷ CCZ123 ∷ []) (wl 176 (lit c4))
  q412 : Ws → Eqn
  q412 c4 = eqn (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) (Toff204 ∷ CCZ024 ∷ []) (wp 15 c4)
  q413 : Ws → Eqn
  q413 c4 = eqn (CS04⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS04⁻ ∷ []) (wp 18 c4)
  q414 : Ws → Eqn
  q414 c4 = eqn (Toff213 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Toff213 ∷ []) (lem-comm-TOFF213-CSd04 (lit c4))
  q415 : Ws → Eqn
  q415 c4 = eqn (CS04⁻ ∷ S2 ∷ []) (S2 ∷ CS04⁻ ∷ []) (wp 17 c4)
  q416 : Ws → Eqn
  q416 c4 = eqn (CS04⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS04⁻ ∷ []) (wp 16 c4)
  q417 : Ws → Eqn
  q417 c4 = eqn (CS13⁻ ∷ S2 ∷ []) (S2 ∷ CS13⁻ ∷ []) (wl 178 (lit c4))
  q418 : Ws → Eqn
  q418 c4 = eqn (CS13⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS13⁻ ∷ []) (wl 177 (lit c4))

-- VPQ @022330: 14 steps
lem-VPQ-at022330 : Ws → ⟪ (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) ⟫ʷ
lem-VPQ-at022330 c4 = derive (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ [])
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
  q419 c4 = eqn (Bx0-2314 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at122331 c4)
  q420 : Ws → Eqn
  q420 c4 = eqn (CCZ014 ∷ CX31 ∷ CCZ034 ∷ []) (CX31 ∷ CCZ014 ∷ []) (wp 792 c4)
  q421 : Ws → Eqn
  q421 c4 = eqn (CCZ034 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ034 ∷ CCZ234 ∷ []) (wp 793 c4)
  q422 : Ws → Eqn
  q422 c4 = eqn (CCZ234 ∷ []) (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl 274 (lit c4))
  q423 : Ws → Eqn
  q423 c4 = eqn (CX23 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4))
  q424 : Ws → Eqn
  q424 c4 = eqn (CCZ014 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ014 ∷ []) (wp 63 c4)
  q425 : Ws → Eqn
  q425 c4 = eqn (CCZ014 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ014 ∷ []) (wp 124 c4)
  q426 : Ws → Eqn
  q426 c4 = eqn (CX31 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX31 ∷ []) (wp 794 c4)
  q427 : Ws → Eqn
  q427 c4 = eqn (CCZ234 ∷ []) (CX31 ∷ CCZ234 ∷ CX31 ∷ []) (wl 277 (lit c4))

-- CXbc-box @122331: 17 steps
lem-CXbc-box-at122331 : Ws → ⟪ (CX31 ∷ Bx0-2314 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXbc-box-at122331 c4 = derive (CX31 ∷ Bx0-2314 ∷ CX31 ∷ []) (Bx0-2314 ∷ CCZ234 ∷ [])
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
  q428 c4 = eqn (CX13 ∷ Toff023 ∷ []) (Toff023 ∷ CX13 ∷ Toff012 ∷ []) (wl 987 (lit c4))
  q429 : Ws → Eqn
  q429 c4 = eqn (CCZ014 ∷ Toff012 ∷ CCZ124 ∷ []) (Toff012 ∷ CCZ014 ∷ []) (wp 310 c4)
  q430 : Ws → Eqn
  q430 c4 = eqn (CCZ014 ∷ CX13 ∷ []) (CX13 ∷ CCZ014 ∷ []) (wp 795 c4)
  q431 : Ws → Eqn
  q431 c4 = eqn (CCZ124 ∷ []) (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (wl 271 (lit c4))
  q432 : Ws → Eqn
  q432 c4 = eqn (CS24 ∷ Toff023 ∷ []) (Toff023 ∷ CS24 ∷ []) (wp 70 c4)
  q433 : Ws → Eqn
  q433 c4 = eqn (Toff012 ∷ Toff023 ∷ []) (Toff023 ∷ Toff012 ∷ []) (wl 275 (lit c4))
  q434 : Ws → Eqn
  q434 c4 = eqn (CX13 ∷ Toff012 ∷ Toff012 ∷ []) (CX13 ∷ []) (wl 988 (lit c4))
  q435 : Ws → Eqn
  q435 c4 = eqn (CCZ014 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ014 ∷ []) (wp 66 c4)
  q436 : Ws → Eqn
  q436 c4 = eqn (CCZ124 ∷ []) (CX13 ∷ CCZ124 ∷ CX13 ∷ []) (wl 272 (lit c4))

-- CXcb-box @122331: 18 steps
lem-CXcb-box-at122331 : Ws → ⟪ (CX13 ∷ Bx0-2314 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at122331 c4 = derive (CX13 ∷ Bx0-2314 ∷ CX13 ∷ []) (Bx0-2314 ∷ CCZ124 ∷ [])
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
  q437 c4 = eqn (Toff014 ∷ Toff023 ∷ []) (Toff023 ∷ Toff014 ∷ []) (lem-tP-at14213243 c4)

-- P-box @14213243: 8 steps
lem-P-box-at14213243 : Ws → ⟪ (Toff023 ∷ Bx0-4123 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-P-box-at14213243 c4 = derive (Toff023 ∷ Bx0-4123 ∷ Toff023 ∷ []) (Bx0-4123 ∷ [])
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
  q438 c4 = eqn (Toff014 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Toff014 ∷ []) (lem-comm-TOFF014-CSd23 (lit c4))

-- VPQ @14213243: 14 steps
lem-VPQ-at14213243 : Ws → ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) ⟫ʷ
lem-VPQ-at14213243 c4 = derive (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ [])
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
  q439 c4 = eqn (Bx0-2341 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at12233441 c4)
  q440 : Ws → Eqn
  q440 c4 = eqn (CX34 ∷ Toff023 ∷ []) (Toff023 ∷ CX34 ∷ []) (wp 270 c4)
  q441 : Ws → Eqn
  q441 c4 = eqn (CCZ014 ∷ CX34 ∷ CCZ013 ∷ []) (CX34 ∷ CCZ014 ∷ []) (wp 807 c4)
  q442 : Ws → Eqn
  q442 c4 = eqn (CCZ013 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ013 ∷ CCZ123 ∷ []) (wl 1007 (lit c4))
  q443 : Ws → Eqn
  q443 c4 = eqn (CCZ014 ∷ CS12 ∷ []) (CS12 ∷ CCZ014 ∷ []) (wp 67 c4)
  q444 : Ws → Eqn
  q444 c4 = eqn (CCZ014 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ014 ∷ []) (wp 60 c4)
  q445 : Ws → Eqn
  q445 c4 = eqn (CCZ014 ∷ CS13 ∷ []) (CS13 ∷ CCZ014 ∷ []) (wp 53 c4)
  q446 : Ws → Eqn
  q446 c4 = eqn (CX34 ∷ CCZ013 ∷ CCZ013 ∷ []) (CX34 ∷ []) (wp 808 c4)

-- CXbc-box @12233441: 17 steps
lem-CXbc-box-at12233441 : Ws → ⟪ (CX34 ∷ Bx0-2341 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXbc-box-at12233441 c4 = derive (CX34 ∷ Bx0-2341 ∷ CX34 ∷ []) (Bx0-2341 ∷ CCZ123 ∷ [])
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
  q447 c4 = eqn (CX43 ∷ Toff023 ∷ []) (Toff023 ∷ CX43 ∷ Toff024 ∷ []) (wp 809 c4)
  q448 : Ws → Eqn
  q448 c4 = eqn (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (Toff024 ∷ CCZ014 ∷ []) (wp 71 c4)
  q449 : Ws → Eqn
  q449 c4 = eqn (CCZ014 ∷ CX43 ∷ []) (CX43 ∷ CCZ014 ∷ []) (wp 810 c4)
  q450 : Ws → Eqn
  q450 c4 = eqn (CS12 ∷ Toff023 ∷ []) (Toff023 ∷ CS12 ∷ []) (wl 221 (lit c4))
  q451 : Ws → Eqn
  q451 c4 = eqn (CX24 ∷ Toff023 ∷ []) (Toff023 ∷ CX24 ∷ []) (wp 263 c4)
  q452 : Ws → Eqn
  q452 c4 = eqn (CX43 ∷ Toff024 ∷ Toff024 ∷ []) (CX43 ∷ []) (wp 811 c4)

-- CXcb-box @12233441: 18 steps
lem-CXcb-box-at12233441 : Ws → ⟪ (CX43 ∷ Bx0-2341 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at12233441 c4 = derive (CX43 ∷ Bx0-2341 ∷ CX43 ∷ []) (Bx0-2341 ∷ CCZ124 ∷ [])
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
  q453 c4 = eqn (CCZ014 ∷ CZ14 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ014 ∷ []) (wp 158 c4)
  q454 : Ws → Eqn
  q454 c4 = eqn (CCZ014 ∷ CZ14 ∷ []) (Toff014 ∷ CCZ014 ∷ Toff014 ∷ []) (wp 159 c4)
  q455 : Ws → Eqn
  q455 c4 = eqn (CZ14 ∷ Toff023 ∷ []) (Toff023 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF023 (lit c4))
  q456 : Ws → Eqn
  q456 c4 = eqn (CCZ014 ∷ []) (CZ14 ∷ CCZ014 ∷ CZ14 ∷ []) (wp 160 c4)

-- P-box @12233441: 8 steps
lem-P-box-at12233441 : Ws → ⟪ (Toff014 ∷ Bx0-2341 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-P-box-at12233441 c4 = derive (Toff014 ∷ Bx0-2341 ∷ Toff014 ∷ []) (Bx0-2341 ∷ [])
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
  q457 c4 = eqn (Toff024 ∷ Toff013 ∷ []) (Toff013 ∷ Toff024 ∷ []) (lem-tP-at122441 c4)

-- P-box @122441: 8 steps
lem-P-box-at122441 : Ws → ⟪ (Toff013 ∷ Bx0-2431 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-P-box-at122441 c4 = derive (Toff013 ∷ Bx0-2431 ∷ Toff013 ∷ []) (Bx0-2431 ∷ [])
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
  q458 c4 = eqn (Bx0-1324 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at2332 c4)
  q459 : Ws → Eqn
  q459 c4 = eqn (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) (CX32 ∷ CCZ024 ∷ []) (wp 717 c4)
  q460 : Ws → Eqn
  q460 c4 = eqn (CCZ034 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ034 ∷ CCZ134 ∷ []) (wp 825 c4)
  q461 : Ws → Eqn
  q461 c4 = eqn (CX32 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX32 ∷ []) (wp 718 c4)

-- CXbc-box @2332: 17 steps
lem-CXbc-box-at2332 : Ws → ⟪ (CX32 ∷ Bx0-1324 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at2332 c4 = derive (CX32 ∷ Bx0-1324 ∷ CX32 ∷ []) (Bx0-1324 ∷ CCZ134 ∷ [])
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
  q462 c4 = eqn (CX23 ∷ Toff013 ∷ []) (Toff013 ∷ CX23 ∷ Toff012 ∷ []) (wl 1018 (lit c4))
  q463 : Ws → Eqn
  q463 c4 = eqn (CCZ024 ∷ Toff012 ∷ CCZ124 ∷ []) (Toff012 ∷ CCZ024 ∷ []) (wp 826 c4)
  q464 : Ws → Eqn
  q464 c4 = eqn (CCZ024 ∷ CX23 ∷ []) (CX23 ∷ CCZ024 ∷ []) (wp 82 c4)
  q465 : Ws → Eqn
  q465 c4 = eqn (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl 256 (lit c4))
  q466 : Ws → Eqn
  q466 c4 = eqn (CS14 ∷ Toff013 ∷ []) (Toff013 ∷ CS14 ∷ []) (wp 785 c4)
  q467 : Ws → Eqn
  q467 c4 = eqn (Toff012 ∷ Toff013 ∷ []) (Toff013 ∷ Toff012 ∷ []) (wl 252 (lit c4))
  q468 : Ws → Eqn
  q468 c4 = eqn (CX23 ∷ Toff012 ∷ Toff012 ∷ []) (CX23 ∷ []) (wl 1019 (lit c4))
  q469 : Ws → Eqn
  q469 c4 = eqn (CCZ024 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ024 ∷ []) (wp 827 c4)

-- CXcb-box @2332: 18 steps
lem-CXcb-box-at2332 : Ws → ⟪ (CX23 ∷ Bx0-1324 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at2332 c4 = derive (CX23 ∷ Bx0-1324 ∷ CX23 ∷ []) (Bx0-1324 ∷ CCZ124 ∷ [])
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
  q470 c4 = eqn (CX12 ∷ CX21 ∷ CX12 ∷ []) (Sw12 ∷ []) (wl 677 (lit c4))
  q471 : Ws → Eqn
  q471 c4 = eqn (CX12 ∷ Bx3-0124 ∷ CX12 ∷ []) (Bx3-0124 ∷ CCZ014 ∷ []) (lem-CXbc-box-at03102132 c4)
  q472 : Ws → Eqn
  q472 c4 = eqn (CCZ014 ∷ CX21 ∷ []) (CX21 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp 899 c4)
  q473 : Ws → Eqn
  q473 c4 = eqn (CX21 ∷ Bx3-0124 ∷ CX21 ∷ []) (Bx3-0124 ∷ CCZ024 ∷ []) (lem-CXcb-box-at03102132 c4)
  q474 : Ws → Eqn
  q474 c4 = eqn (CCZ024 ∷ CX12 ∷ []) (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp 653 c4)
  q475 : Ws → Eqn
  q475 c4 = eqn (CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ []) (CCZ014 ∷ []) (wp 900 c4)

-- SWbc-box @03102132: 11 steps
lem-SWbc-box-at03102132 : Ws → ⟪ (Sw12 ∷ Bx3-0124 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-SWbc-box-at03102132 c4 = derive (Sw12 ∷ Bx3-0124 ∷ Sw12 ∷ []) (Bx3-0124 ∷ [])
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
  q476 c4 = eqn (Bx2-4013 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0214203143 c4)
  q477 : Ws → Eqn
  q477 c4 = eqn (Toff204 ∷ Toff213 ∷ []) (Toff213 ∷ Toff204 ∷ []) (lem-tP-at0214203143 c4)

-- P-box @0214203143: 8 steps
lem-P-box-at0214203143 : Ws → ⟪ (Toff213 ∷ Bx2-4013 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-P-box-at0214203143 c4 = derive (Toff213 ∷ Bx2-4013 ∷ Toff213 ∷ []) (Bx2-4013 ∷ [])
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
  q478 c4 = eqn (Toff204 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Toff204 ∷ []) (lem-comm-TOFF204-CSd13 (lit c4))

-- VPQ @0214203143: 14 steps
lem-VPQ-at0214203143 : Ws → ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at0214203143 c4 = derive (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ [])
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
  q479 c4 = eqn (Bx2-1340 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at02233440 c4)
  q480 : Ws → Eqn
  q480 c4 = eqn (CCZ024 ∷ CX34 ∷ CCZ023 ∷ []) (CX34 ∷ CCZ024 ∷ []) (wp 911 c4)
  q481 : Ws → Eqn
  q481 c4 = eqn (CCZ023 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ023 ∷ CCZ013 ∷ []) (wl 1119 (lit c4))
  q482 : Ws → Eqn
  q482 c4 = eqn (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl 289 (lit c4))
  q483 : Ws → Eqn
  q483 c4 = eqn (CCZ024 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ024 ∷ []) (wp 32 c4)
  q484 : Ws → Eqn
  q484 c4 = eqn (CX34 ∷ CCZ023 ∷ CCZ023 ∷ []) (CX34 ∷ []) (wp 912 c4)
  q485 : Ws → Eqn
  q485 c4 = eqn (CCZ013 ∷ []) (CX34 ∷ CCZ013 ∷ CX34 ∷ []) (wp 913 c4)

-- CXbc-box @02233440: 17 steps
lem-CXbc-box-at02233440 : Ws → ⟪ (CX34 ∷ Bx2-1340 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXbc-box-at02233440 c4 = derive (CX34 ∷ Bx2-1340 ∷ CX34 ∷ []) (Bx2-1340 ∷ CCZ013 ∷ [])
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
  q486 c4 = eqn (CX43 ∷ Toff213 ∷ []) (Toff213 ∷ CX43 ∷ Toff214 ∷ []) (wl 1120 (lit c4))
  q487 : Ws → Eqn
  q487 c4 = eqn (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (Toff214 ∷ CCZ024 ∷ []) (wp 42 c4)
  q488 : Ws → Eqn
  q488 c4 = eqn (CCZ024 ∷ CX43 ∷ []) (CX43 ∷ CCZ024 ∷ []) (wp 914 c4)
  q489 : Ws → Eqn
  q489 c4 = eqn (CCZ014 ∷ []) (CS04 ∷ CX14 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ []) (wp 46 c4)
  q490 : Ws → Eqn
  q490 c4 = eqn (CS01 ∷ Toff213 ∷ []) (Toff213 ∷ CS01 ∷ []) (wl 193 (lit c4))
  q491 : Ws → Eqn
  q491 c4 = eqn (Toff213 ∷ Toff214 ∷ []) (Toff214 ∷ Toff213 ∷ []) (wl 197 (lit c4))
  q492 : Ws → Eqn
  q492 c4 = eqn (CX43 ∷ Toff214 ∷ Toff214 ∷ []) (CX43 ∷ []) (wl 1121 (lit c4))
  q493 : Ws → Eqn
  q493 c4 = eqn (CCZ014 ∷ []) (CX43 ∷ CCZ014 ∷ CX43 ∷ []) (wp 915 c4)

-- CXcb-box @02233440: 18 steps
lem-CXcb-box-at02233440 : Ws → ⟪ (CX43 ∷ Bx2-1340 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at02233440 c4 = derive (CX43 ∷ Bx2-1340 ∷ CX43 ∷ []) (Bx2-1340 ∷ CCZ014 ∷ [])
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
  q494 c4 = eqn (Toff214 ∷ Toff203 ∷ []) (Toff203 ∷ Toff214 ∷ []) (lem-tP-at022440 c4)

-- VPQ @022440: 14 steps
lem-VPQ-at022440 : Ws → ⟪ (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) ⟫ʷ
lem-VPQ-at022440 c4 = derive (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ [])
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
  q495 c4 = eqn (Bx2-1430 ∷ []) (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (lem-box-tQ-at022440 c4)
  q496 : Ws → Eqn
  q496 c4 = eqn (CX43 ∷ Toff214 ∷ []) (Toff214 ∷ CX43 ∷ []) (wl 1132 (lit c4))
  q497 : Ws → Eqn
  q497 c4 = eqn (CCZ023 ∷ CX43 ∷ CCZ024 ∷ []) (CX43 ∷ CCZ023 ∷ []) (wp 920 c4)
  q498 : Ws → Eqn
  q498 c4 = eqn (CCZ024 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp 921 c4)
  q499 : Ws → Eqn
  q499 c4 = eqn (CCZ023 ∷ CS01 ∷ []) (CS01 ∷ CCZ023 ∷ []) (wl 199 (lit c4))
  q500 : Ws → Eqn
  q500 c4 = eqn (CCZ023 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ023 ∷ []) (wp 47 c4)
  q501 : Ws → Eqn
  q501 c4 = eqn (CCZ023 ∷ CS04 ∷ []) (CS04 ∷ CCZ023 ∷ []) (wp 48 c4)
  q502 : Ws → Eqn
  q502 c4 = eqn (CX43 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX43 ∷ []) (wp 922 c4)

-- CXbc-box @022440: 17 steps
lem-CXbc-box-at022440 : Ws → ⟪ (CX43 ∷ Bx2-1430 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at022440 c4 = derive (CX43 ∷ Bx2-1430 ∷ CX43 ∷ []) (Bx2-1430 ∷ CCZ014 ∷ [])
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
