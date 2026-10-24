{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD205 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D205 (Sᴰ : SD205) where

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
  lem-comm-CCZ034-CS12 : Ws → St 1705
  lem-comm-CCZ034-CS12 = pickᴰ 0 Sᴰ
  lem-comm-CCZ034-CX12 : Ws → St 1285
  lem-comm-CCZ034-CX12 = pickᴰ 1 Sᴰ
  lem-comm-TOFF312-CX04 : Ws → St 2072
  lem-comm-TOFF312-CX04 = pickᴰ 2 Sᴰ
  lem-comm-CCZ034-CSd12 : Ws → St 2088
  lem-comm-CCZ034-CSd12 = pickᴰ 3 Sᴰ
  lem-box-cP-at0310243142 : Ws → St 996
  lem-box-cP-at0310243142 = pickᴰ 4 Sᴰ
  lem-box-perm-1324-at0310213442 : Ws → St 1311
  lem-box-perm-1324-at0310213442 = pickᴰ 5 Sᴰ
  lem-box-perm-1324-at0310243142 : Ws → St 1327
  lem-box-perm-1324-at0310243142 = pickᴰ 6 Sᴰ
  lem-box2-at0310243142 : Ws → St 1340
  lem-box2-at0310243142 = pickᴰ 7 Sᴰ
  lem-CKc-box-at0310213442 : Ws → St 2089
  lem-CKc-box-at0310213442 = pickᴰ 8 Sᴰ
  lem-CKc-box-at03103441 : Ws → St 2090
  lem-CKc-box-at03103441 = pickᴰ 9 Sᴰ
  lem-S2-SBOX⟨3·0·41·2⟩ : Ws → St 2091
  lem-S2-SBOX⟨3·0·41·2⟩ = pickᴰ 10 Sᴰ
  lem-S2-SBOX⟨3·1·42·0⟩ : Ws → St 2092
  lem-S2-SBOX⟨3·1·42·0⟩ = pickᴰ 11 Sᴰ
  lem-box-perm-1342-at03103441 : Ws → St 2093
  lem-box-perm-1342-at03103441 = pickᴰ 12 Sᴰ
  lem-box-perm-1423-at0310243142 : Ws → St 2094
  lem-box-perm-1423-at0310243142 = pickᴰ 13 Sᴰ
  lem-F0-at01143043 : Ws → St 2086
  lem-F0-at01143043 = pickᴰ 14 Sᴰ
  lem-F0-at14213243 : Ws → St 2087
  lem-F0-at14213243 = pickᴰ 15 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 2086 (lem-F0-at01143043 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 2087 (lem-F0-at14213243 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 2092 (lem-S2-SBOX⟨3·1·42·0⟩ c4)
  q4 : Ws → Eqn
  q4 c4 = wlE 1267 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = sE 996 (lem-box-cP-at0310243142 c4)
  q6 : Ws → Eqn
  q6 c4 = wlE 1225 (lit c4)
  q7 : Ws → Eqn
  q7 c4 = wlE 888 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = wpE 701 c4
  q9 : Ws → Eqn
  q9 c4 = wpE 108 c4
  q10 : Ws → Eqn
  q10 c4 = sE 1285 (lem-comm-CCZ034-CX12 c4)
  q11 : Ws → Eqn
  q11 c4 = wpE 107 c4
  q12 : Ws → Eqn
  q12 c4 = wpE 106 c4
  q13 : Ws → Eqn
  q13 c4 = wpE 700 c4
  q14 : Ws → Eqn
  q14 c4 = wpE 716 c4
  q15 : Ws → Eqn
  q15 c4 = wlE 779 (lit c4)
  q16 : Ws → Eqn
  q16 c4 = wpE 41 c4
  q17 : Ws → Eqn
  q17 c4 = wlE 499 (lit c4)
  q18 : Ws → Eqn
  q18 c4 = sE 2072 (lem-comm-TOFF312-CX04 c4)
  q19 : Ws → Eqn
  q19 c4 = wlE 778 (lit c4)
  q20 : Ws → Eqn
  q20 c4 = wlE 501 (lit c4)
  q21 : Ws → Eqn
  q21 c4 = wlE 780 (lit c4)
  q22 : Ws → Eqn
  q22 c4 = wpE 124 c4
  q23 : Ws → Eqn
  q23 c4 = wlE 861 (lit c4)
  q24 : Ws → Eqn
  q24 c4 = wpE 3 c4
  q25 : Ws → Eqn
  q25 c4 = wlE 1226 (lit c4)
  q26 : Ws → Eqn
  q26 c4 = wpE 2 c4
  q27 : Ws → Eqn
  q27 c4 = sE 2094 (lem-box-perm-1423-at0310243142 c4)
  q28 : Ws → Eqn
  q28 c4 = sE 2090 (lem-CKc-box-at03103441 c4)
  q29 : Ws → Eqn
  q29 c4 = sE 2093 (lem-box-perm-1342-at03103441 c4)
  q30 : Ws → Eqn
  q30 c4 = wlE 871 (lit c4)
  q31 : Ws → Eqn
  q31 c4 = wlE 256 (lit c4)
  q32 : Ws → Eqn
  q32 c4 = wlE 1268 (lit c4)
  q33 : Ws → Eqn
  q33 c4 = wpE 981 c4
  q34 : Ws → Eqn
  q34 c4 = sE 1327 (lem-box-perm-1324-at0310243142 c4)
  q35 : Ws → Eqn
  q35 c4 = sE 2089 (lem-CKc-box-at0310213442 c4)
  q36 : Ws → Eqn
  q36 c4 = sE 1311 (lem-box-perm-1324-at0310213442 c4)
  q37 : Ws → Eqn
  q37 c4 = wpE 1030 c4
  q38 : Ws → Eqn
  q38 c4 = wpE 161 c4
  q39 : Ws → Eqn
  q39 c4 = wpE 205 c4
  q40 : Ws → Eqn
  q40 c4 = wlE 341 (lit c4)
  q41 : Ws → Eqn
  q41 c4 = wlE 1269 (lit c4)

-- nf-rel-266@0: 163 steps
lem-nf-rel-266at0 : Ws → ⟪ (ℓ "亇侧侧亇丢亄侧侧亄丢俄亄侧侧亄丢亇侧侧亇丢") ⟫ʷ ≈ ⟪ (ℓ "亪亩亪丯亪丰二亄亨亄丢亇亨亇二丢佨") ⟫ʷ
lem-nf-rel-266at0 c4 = derive (ℓ "亇侧侧亇丢亄侧侧亄丢俄亄侧侧亄丢亇侧侧亇丢") (ℓ "亪亩亪丯亪丰二亄亨亄丢亇亨亇二丢佨")
  (rw 1 (q1 c4) ∷
   rw 2 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw 10 (q2 c4) ∷
   rw 12 (q1 c4) ∷
   rw 13 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw 1 (q3 c4) ∷
   rw 5 (q3 c4) ∷
   rw 10 (q3 c4) ∷
   rw 14 (q3 c4) ∷
   re 8 1 (ℓ "佨亪俑亪俕") ∷
   re 10 1 (ℓ "丯") ∷
   re 12 1 (ℓ "丰") ∷
   rw 0 (q4 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   rw 4 (q8 c4) ∷
   rw 5 (q9 c4) ∷
   rw 6 (q10 c4) ∷
   rw 7 (q11 c4) ∷
   rw 8 (q10 c4) ∷
   rw 9 (q12 c4) ∷
   rw 10 (q13 c4) ∷
   rw 4 (q7 c4) ∷
   rw 5 (q14 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw 5 (q15 c4) ∷
   rw 7 (q16 c4) ∷
   rw⁻ 6 (q17 c4) ∷
   rw 7 (q18 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw 9 (q18 c4) ∷
   rw⁻ 10 (q20 c4) ∷
   rw⁻ 6 (q16 c4) ∷
   rw 3 (q21 c4) ∷
   rw⁻ 3 (q7 c4) ∷
   rw 2 (q8 c4) ∷
   rw 3 (q9 c4) ∷
   rw 4 (q10 c4) ∷
   rw 5 (q11 c4) ∷
   rw 6 (q10 c4) ∷
   rw 7 (q12 c4) ∷
   rw 8 (q13 c4) ∷
   rw 2 (q7 c4) ∷
   rw⁻ 3 (q22 c4) ∷
   rw⁻ 4 (q5 c4) ∷
   rw 4 (q5 c4) ∷
   rw⁻ 7 (q23 c4) ∷
   rw 6 (q24 c4) ∷
   rw⁻ 5 (q23 c4) ∷
   rw 4 (q24 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw 5 (q5 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   rw 7 (q8 c4) ∷
   rw 8 (q9 c4) ∷
   rw 9 (q10 c4) ∷
   rw 10 (q11 c4) ∷
   rw 11 (q10 c4) ∷
   rw 12 (q12 c4) ∷
   rw 13 (q13 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q14 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   rw 8 (q15 c4) ∷
   rw 10 (q16 c4) ∷
   rw⁻ 9 (q17 c4) ∷
   rw 10 (q18 c4) ∷
   rw⁻ 11 (q19 c4) ∷
   rw 12 (q18 c4) ∷
   rw⁻ 13 (q20 c4) ∷
   rw⁻ 9 (q16 c4) ∷
   rw 6 (q21 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   rw 5 (q8 c4) ∷
   rw 6 (q9 c4) ∷
   rw 7 (q10 c4) ∷
   rw 8 (q11 c4) ∷
   rw 9 (q10 c4) ∷
   rw 10 (q12 c4) ∷
   rw 11 (q13 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 6 (q22 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw 7 (q5 c4) ∷
   rw⁻ 10 (q25 c4) ∷
   rw 9 (q26 c4) ∷
   rw⁻ 8 (q25 c4) ∷
   rw 7 (q26 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw 8 (q27 c4) ∷
   rw 8 (q28 c4) ∷
   rw 11 (q29 c4) ∷
   rw 11 (q5 c4) ∷
   rw⁻ 14 (q30 c4) ∷
   rw 14 (q31 c4) ∷
   rw 13 (q9 c4) ∷
   rw 14 (q10 c4) ∷
   rw 15 (q11 c4) ∷
   rw 16 (q10 c4) ∷
   rw 17 (q12 c4) ∷
   rw⁻ 13 (q31 c4) ∷
   rw⁻ 12 (q30 c4) ∷
   rw 12 (q31 c4) ∷
   rw 11 (q9 c4) ∷
   rw 12 (q10 c4) ∷
   rw 13 (q11 c4) ∷
   rw 14 (q10 c4) ∷
   rw 15 (q12 c4) ∷
   rw⁻ 11 (q31 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   rw 12 (q27 c4) ∷
   rw 12 (q28 c4) ∷
   rw 15 (q29 c4) ∷
   rw 15 (q5 c4) ∷
   rw⁻ 18 (q32 c4) ∷
   rw 17 (q33 c4) ∷
   rw⁻ 16 (q32 c4) ∷
   rw 15 (q33 c4) ∷
   rw⁻ 16 (q5 c4) ∷
   rw 16 (q34 c4) ∷
   rw 16 (q35 c4) ∷
   rw 19 (q36 c4) ∷
   rw 19 (q5 c4) ∷
   rw⁻ 22 (q30 c4) ∷
   rw 22 (q31 c4) ∷
   rw 21 (q9 c4) ∷
   rw 22 (q10 c4) ∷
   rw 23 (q11 c4) ∷
   rw 24 (q10 c4) ∷
   rw 25 (q12 c4) ∷
   rw⁻ 21 (q31 c4) ∷
   rw⁻ 20 (q30 c4) ∷
   rw 20 (q31 c4) ∷
   rw 19 (q9 c4) ∷
   rw 20 (q10 c4) ∷
   rw 21 (q11 c4) ∷
   rw 22 (q10 c4) ∷
   rw 23 (q12 c4) ∷
   rw⁻ 19 (q31 c4) ∷
   rw⁻ 20 (q5 c4) ∷
   rw 20 (q34 c4) ∷
   rw 20 (q35 c4) ∷
   rw 23 (q36 c4) ∷
   rw 23 (q5 c4) ∷
   rw⁻ 26 (q32 c4) ∷
   rw 25 (q33 c4) ∷
   rw⁻ 24 (q32 c4) ∷
   rw 23 (q33 c4) ∷
   rw⁻ 24 (q5 c4) ∷
   rw 3 (q37 c4) ∷
   rw 5 (q38 c4) ∷
   rw 8 (q39 c4) ∷
   rw 9 (q40 c4) ∷
   rw 10 (q41 c4) ∷
   rw 11 (q40 c4) ∷
   rw 12 (q39 c4) ∷
   rw 13 (q40 c4) ∷ []) Eq.refl

private
  q42 : Ws → Eqn
  q42 c4 = sE 2091 (lem-S2-SBOX⟨3·0·41·2⟩ c4)
  q43 : Ws → Eqn
  q43 c4 = wpE 1118 c4

-- nf-rel-267@0: 13 steps
lem-nf-rel-267at0 : Ws → ⟪ (ℓ "亄俄俄亄丢侧侧亄俄俄亄丢侧侧") ⟫ʷ ≈ ⟪ (ℓ "亜") ⟫ʷ
lem-nf-rel-267at0 c4 = derive (ℓ "亄俄俄亄丢侧侧亄俄俄亄丢侧侧") (ℓ "亜")
  (rw 1 (q2 c4) ∷
   rw 2 (q2 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw 8 (q2 c4) ∷
   rw 9 (q2 c4) ∷
   rw 12 (q1 c4) ∷
   rw 13 (q1 c4) ∷
   rw 1 (q42 c4) ∷
   rw 4 (q3 c4) ∷
   rw 6 (q42 c4) ∷
   rw 9 (q3 c4) ∷
   rw⁻ 0 (q43 c4) ∷ []) Eq.refl

private
  q44 : Ws → Eqn
  q44 c4 = wlE 503 (lit c4)
  q45 : Ws → Eqn
  q45 c4 = wlE 348 (lit c4)
  q46 : Ws → Eqn
  q46 c4 = sE 1705 (lem-comm-CCZ034-CS12 c4)
  q47 : Ws → Eqn
  q47 c4 = wpE 221 c4
  q48 : Ws → Eqn
  q48 c4 = sE 2088 (lem-comm-CCZ034-CSd12 c4)
  q49 : Ws → Eqn
  q49 c4 = sE 1340 (lem-box2-at0310243142 c4)
  q50 : Ws → Eqn
  q50 c4 = wpE 1121 c4
  q51 : Ws → Eqn
  q51 c4 = wpE 1122 c4
  q52 : Ws → Eqn
  q52 c4 = wpE 686 c4

-- nf-rel-268@0: 482 steps
lem-nf-rel-268at0 : Ws → ⟪ (ℓ "俄亄侧侧亄丢俄俄俄亄侧侧亄丢") ⟫ʷ ≈ ⟪ (ℓ "亪丯亪丰亄亨亄丢亪丯亪五丰二亄亨亄二丢") ⟫ʷ
lem-nf-rel-268at0 c4 = derive (ℓ "俄亄侧侧亄丢俄俄俄亄侧侧亄丢") (ℓ "亪丯亪丰亄亨亄丢亪丯亪五丰二亄亨亄二丢")
  (rw 0 (q2 c4) ∷
   rw 2 (q1 c4) ∷
   rw 3 (q1 c4) ∷
   rw 6 (q2 c4) ∷
   rw 7 (q2 c4) ∷
   rw 8 (q2 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw 2 (q3 c4) ∷
   rw 5 (q42 c4) ∷
   rw 8 (q3 c4) ∷
   re 0 1 (ℓ "佨亪俑亪俕") ∷
   re 2 1 (ℓ "丯") ∷
   re 4 1 (ℓ "丰") ∷
   re 10 1 (ℓ "佨亪俑亪俕") ∷
   re 12 1 (ℓ "丯") ∷
   re 14 1 (ℓ "丰") ∷
   rw 10 (q5 c4) ∷
   rw⁻ 13 (q6 c4) ∷
   rw⁻ 13 (q7 c4) ∷
   rw 12 (q8 c4) ∷
   rw 13 (q9 c4) ∷
   rw 14 (q10 c4) ∷
   rw 15 (q11 c4) ∷
   rw 16 (q10 c4) ∷
   rw 17 (q12 c4) ∷
   rw 18 (q13 c4) ∷
   rw 12 (q7 c4) ∷
   rw 13 (q14 c4) ∷
   rw⁻ 11 (q6 c4) ∷
   rw 13 (q15 c4) ∷
   rw 15 (q16 c4) ∷
   rw⁻ 14 (q17 c4) ∷
   rw 15 (q18 c4) ∷
   rw⁻ 16 (q19 c4) ∷
   rw 17 (q18 c4) ∷
   rw⁻ 18 (q20 c4) ∷
   rw⁻ 14 (q16 c4) ∷
   rw 11 (q21 c4) ∷
   rw⁻ 11 (q7 c4) ∷
   rw 10 (q8 c4) ∷
   rw 11 (q9 c4) ∷
   rw 12 (q10 c4) ∷
   rw 13 (q11 c4) ∷
   rw 14 (q10 c4) ∷
   rw 15 (q12 c4) ∷
   rw 16 (q13 c4) ∷
   rw 10 (q7 c4) ∷
   rw⁻ 11 (q22 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   rw 12 (q5 c4) ∷
   rw⁻ 15 (q23 c4) ∷
   rw 14 (q24 c4) ∷
   rw⁻ 13 (q23 c4) ∷
   rw 12 (q24 c4) ∷
   rw⁻ 13 (q5 c4) ∷
   rw 13 (q5 c4) ∷
   rw⁻ 16 (q6 c4) ∷
   rw⁻ 16 (q7 c4) ∷
   rw 15 (q8 c4) ∷
   rw 16 (q9 c4) ∷
   rw 17 (q10 c4) ∷
   rw 18 (q11 c4) ∷
   rw 19 (q10 c4) ∷
   rw 20 (q12 c4) ∷
   rw 21 (q13 c4) ∷
   rw 15 (q7 c4) ∷
   rw 16 (q14 c4) ∷
   rw⁻ 14 (q6 c4) ∷
   rw 16 (q15 c4) ∷
   rw 18 (q16 c4) ∷
   rw⁻ 17 (q17 c4) ∷
   rw 18 (q18 c4) ∷
   rw⁻ 19 (q19 c4) ∷
   rw 20 (q18 c4) ∷
   rw⁻ 21 (q20 c4) ∷
   rw⁻ 17 (q16 c4) ∷
   rw 14 (q21 c4) ∷
   rw⁻ 14 (q7 c4) ∷
   rw 13 (q8 c4) ∷
   rw 14 (q9 c4) ∷
   rw 15 (q10 c4) ∷
   rw 16 (q11 c4) ∷
   rw 17 (q10 c4) ∷
   rw 18 (q12 c4) ∷
   rw 19 (q13 c4) ∷
   rw 13 (q7 c4) ∷
   rw⁻ 14 (q22 c4) ∷
   rw⁻ 15 (q5 c4) ∷
   rw 15 (q5 c4) ∷
   rw⁻ 18 (q25 c4) ∷
   rw 17 (q26 c4) ∷
   rw⁻ 16 (q25 c4) ∷
   rw 15 (q26 c4) ∷
   rw⁻ 16 (q5 c4) ∷
   rw 16 (q27 c4) ∷
   rw 16 (q28 c4) ∷
   rw 19 (q29 c4) ∷
   rw 19 (q5 c4) ∷
   rw⁻ 22 (q30 c4) ∷
   rw 22 (q31 c4) ∷
   rw 21 (q9 c4) ∷
   rw 22 (q10 c4) ∷
   rw 23 (q11 c4) ∷
   rw 24 (q10 c4) ∷
   rw 25 (q12 c4) ∷
   rw⁻ 21 (q31 c4) ∷
   rw⁻ 20 (q30 c4) ∷
   rw 20 (q31 c4) ∷
   rw 19 (q9 c4) ∷
   rw 20 (q10 c4) ∷
   rw 21 (q11 c4) ∷
   rw 22 (q10 c4) ∷
   rw 23 (q12 c4) ∷
   rw⁻ 19 (q31 c4) ∷
   rw⁻ 20 (q5 c4) ∷
   rw 20 (q27 c4) ∷
   rw 20 (q28 c4) ∷
   rw 23 (q29 c4) ∷
   rw 23 (q5 c4) ∷
   rw⁻ 26 (q32 c4) ∷
   rw 25 (q33 c4) ∷
   rw⁻ 24 (q32 c4) ∷
   rw 23 (q33 c4) ∷
   rw⁻ 24 (q5 c4) ∷
   rw 0 (q5 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw⁻ 3 (q7 c4) ∷
   rw 2 (q8 c4) ∷
   rw 3 (q9 c4) ∷
   rw 4 (q10 c4) ∷
   rw 5 (q11 c4) ∷
   rw 6 (q10 c4) ∷
   rw 7 (q12 c4) ∷
   rw 8 (q13 c4) ∷
   rw 2 (q7 c4) ∷
   rw 3 (q14 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw 3 (q15 c4) ∷
   rw 5 (q16 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 5 (q18 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw 7 (q18 c4) ∷
   rw⁻ 8 (q20 c4) ∷
   rw⁻ 4 (q16 c4) ∷
   rw 1 (q21 c4) ∷
   rw⁻ 1 (q7 c4) ∷
   rw 0 (q8 c4) ∷
   rw 1 (q9 c4) ∷
   rw 2 (q10 c4) ∷
   rw 3 (q11 c4) ∷
   rw 4 (q10 c4) ∷
   rw 5 (q12 c4) ∷
   rw 6 (q13 c4) ∷
   rw 0 (q7 c4) ∷
   rw⁻ 1 (q22 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 5 (q23 c4) ∷
   rw 4 (q24 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   rw 2 (q24 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw 3 (q5 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   rw 5 (q8 c4) ∷
   rw 6 (q9 c4) ∷
   rw 7 (q10 c4) ∷
   rw 8 (q11 c4) ∷
   rw 9 (q10 c4) ∷
   rw 10 (q12 c4) ∷
   rw 11 (q13 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   rw 6 (q15 c4) ∷
   rw 8 (q16 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   rw 8 (q18 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw 10 (q18 c4) ∷
   rw⁻ 11 (q20 c4) ∷
   rw⁻ 7 (q16 c4) ∷
   rw 4 (q21 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw 3 (q8 c4) ∷
   rw 4 (q9 c4) ∷
   rw 5 (q10 c4) ∷
   rw 6 (q11 c4) ∷
   rw 7 (q10 c4) ∷
   rw 8 (q12 c4) ∷
   rw 9 (q13 c4) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 4 (q22 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw 5 (q5 c4) ∷
   rw⁻ 8 (q25 c4) ∷
   rw 7 (q26 c4) ∷
   rw⁻ 6 (q25 c4) ∷
   rw 5 (q26 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 6 (q27 c4) ∷
   rw 6 (q28 c4) ∷
   rw 9 (q29 c4) ∷
   rw 9 (q5 c4) ∷
   rw⁻ 12 (q30 c4) ∷
   rw 12 (q31 c4) ∷
   rw 11 (q9 c4) ∷
   rw 12 (q10 c4) ∷
   rw 13 (q11 c4) ∷
   rw 14 (q10 c4) ∷
   rw 15 (q12 c4) ∷
   rw⁻ 11 (q31 c4) ∷
   rw⁻ 10 (q30 c4) ∷
   rw 10 (q31 c4) ∷
   rw 9 (q9 c4) ∷
   rw 10 (q10 c4) ∷
   rw 11 (q11 c4) ∷
   rw 12 (q10 c4) ∷
   rw 13 (q12 c4) ∷
   rw⁻ 9 (q31 c4) ∷
   rw⁻ 10 (q5 c4) ∷
   rw 10 (q27 c4) ∷
   rw 10 (q28 c4) ∷
   rw 13 (q29 c4) ∷
   rw 13 (q5 c4) ∷
   rw⁻ 16 (q32 c4) ∷
   rw 15 (q33 c4) ∷
   rw⁻ 14 (q32 c4) ∷
   rw 13 (q33 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   rw 14 (q5 c4) ∷
   rw 18 (q16 c4) ∷
   rw⁻ 17 (q17 c4) ∷
   rw 18 (q18 c4) ∷
   rw⁻ 19 (q19 c4) ∷
   rw 20 (q18 c4) ∷
   rw⁻ 21 (q20 c4) ∷
   rw⁻ 17 (q16 c4) ∷
   rw⁻ 16 (q22 c4) ∷
   rw 16 (q16 c4) ∷
   rw⁻ 15 (q17 c4) ∷
   rw 16 (q18 c4) ∷
   rw⁻ 17 (q19 c4) ∷
   rw 18 (q18 c4) ∷
   rw⁻ 19 (q20 c4) ∷
   rw⁻ 15 (q16 c4) ∷
   rw⁻ 14 (q22 c4) ∷
   rw⁻ 15 (q5 c4) ∷
   rw 15 (q5 c4) ∷
   rw⁻ 18 (q6 c4) ∷
   rw⁻ 18 (q7 c4) ∷
   rw 17 (q8 c4) ∷
   rw 18 (q9 c4) ∷
   rw 19 (q10 c4) ∷
   rw 20 (q11 c4) ∷
   rw 21 (q10 c4) ∷
   rw 22 (q12 c4) ∷
   rw 23 (q13 c4) ∷
   rw 17 (q7 c4) ∷
   rw 18 (q14 c4) ∷
   rw⁻ 16 (q6 c4) ∷
   rw 18 (q15 c4) ∷
   rw 20 (q16 c4) ∷
   rw⁻ 19 (q17 c4) ∷
   rw 20 (q18 c4) ∷
   rw⁻ 21 (q19 c4) ∷
   rw 22 (q18 c4) ∷
   rw⁻ 23 (q20 c4) ∷
   rw⁻ 19 (q16 c4) ∷
   rw 16 (q21 c4) ∷
   rw⁻ 16 (q7 c4) ∷
   rw 15 (q8 c4) ∷
   rw 16 (q9 c4) ∷
   rw 17 (q10 c4) ∷
   rw 18 (q11 c4) ∷
   rw 19 (q10 c4) ∷
   rw 20 (q12 c4) ∷
   rw 21 (q13 c4) ∷
   rw 15 (q7 c4) ∷
   rw⁻ 16 (q22 c4) ∷
   rw⁻ 17 (q5 c4) ∷
   rw 17 (q5 c4) ∷
   rw 21 (q16 c4) ∷
   rw⁻ 20 (q17 c4) ∷
   rw 21 (q18 c4) ∷
   rw⁻ 22 (q19 c4) ∷
   rw 23 (q18 c4) ∷
   rw⁻ 24 (q20 c4) ∷
   rw⁻ 20 (q16 c4) ∷
   rw⁻ 19 (q22 c4) ∷
   rw 19 (q16 c4) ∷
   rw⁻ 18 (q17 c4) ∷
   rw 19 (q18 c4) ∷
   rw⁻ 20 (q19 c4) ∷
   rw 21 (q18 c4) ∷
   rw⁻ 22 (q20 c4) ∷
   rw⁻ 18 (q16 c4) ∷
   rw⁻ 17 (q22 c4) ∷
   rw⁻ 18 (q5 c4) ∷
   rw 18 (q5 c4) ∷
   rw⁻ 21 (q23 c4) ∷
   rw 20 (q24 c4) ∷
   rw⁻ 19 (q23 c4) ∷
   rw 18 (q24 c4) ∷
   rw⁻ 19 (q5 c4) ∷
   rw 19 (q5 c4) ∷
   rw⁻ 22 (q6 c4) ∷
   rw⁻ 22 (q7 c4) ∷
   rw 21 (q8 c4) ∷
   rw 22 (q9 c4) ∷
   rw 23 (q10 c4) ∷
   rw 24 (q11 c4) ∷
   rw 25 (q10 c4) ∷
   rw 26 (q12 c4) ∷
   rw 27 (q13 c4) ∷
   rw 21 (q7 c4) ∷
   rw 22 (q14 c4) ∷
   rw⁻ 20 (q6 c4) ∷
   rw 22 (q15 c4) ∷
   rw 24 (q16 c4) ∷
   rw⁻ 23 (q17 c4) ∷
   rw 24 (q18 c4) ∷
   rw⁻ 25 (q19 c4) ∷
   rw 26 (q18 c4) ∷
   rw⁻ 27 (q20 c4) ∷
   rw⁻ 23 (q16 c4) ∷
   rw 20 (q21 c4) ∷
   rw⁻ 20 (q7 c4) ∷
   rw 19 (q8 c4) ∷
   rw 20 (q9 c4) ∷
   rw 21 (q10 c4) ∷
   rw 22 (q11 c4) ∷
   rw 23 (q10 c4) ∷
   rw 24 (q12 c4) ∷
   rw 25 (q13 c4) ∷
   rw 19 (q7 c4) ∷
   rw⁻ 20 (q22 c4) ∷
   rw⁻ 21 (q5 c4) ∷
   rw 21 (q5 c4) ∷
   rw 25 (q16 c4) ∷
   rw⁻ 24 (q17 c4) ∷
   rw 25 (q18 c4) ∷
   rw⁻ 26 (q19 c4) ∷
   rw 27 (q18 c4) ∷
   rw⁻ 28 (q20 c4) ∷
   rw⁻ 24 (q16 c4) ∷
   rw⁻ 23 (q22 c4) ∷
   rw 23 (q16 c4) ∷
   rw⁻ 22 (q17 c4) ∷
   rw 23 (q18 c4) ∷
   rw⁻ 24 (q19 c4) ∷
   rw 25 (q18 c4) ∷
   rw⁻ 26 (q20 c4) ∷
   rw⁻ 22 (q16 c4) ∷
   rw⁻ 21 (q22 c4) ∷
   rw⁻ 22 (q5 c4) ∷
   rw 22 (q5 c4) ∷
   rw⁻ 25 (q25 c4) ∷
   rw 24 (q26 c4) ∷
   rw⁻ 23 (q25 c4) ∷
   rw 22 (q26 c4) ∷
   rw⁻ 23 (q5 c4) ∷
   rw 23 (q5 c4) ∷
   rw⁻ 26 (q44 c4) ∷
   rw 26 (q45 c4) ∷
   rw 25 (q46 c4) ∷
   rw 26 (q47 c4) ∷
   rw 27 (q48 c4) ∷
   rw 28 (q47 c4) ∷
   rw 29 (q24 c4) ∷
   rw⁻ 25 (q45 c4) ∷
   rw⁻ 24 (q44 c4) ∷
   rw 24 (q45 c4) ∷
   rw 23 (q46 c4) ∷
   rw 24 (q47 c4) ∷
   rw 25 (q48 c4) ∷
   rw 26 (q47 c4) ∷
   rw 27 (q24 c4) ∷
   rw⁻ 23 (q45 c4) ∷
   rw⁻ 24 (q5 c4) ∷
   rw 24 (q27 c4) ∷
   rw 24 (q28 c4) ∷
   rw 27 (q29 c4) ∷
   rw 27 (q5 c4) ∷
   rw⁻ 30 (q44 c4) ∷
   rw 30 (q45 c4) ∷
   rw 29 (q46 c4) ∷
   rw 30 (q47 c4) ∷
   rw 31 (q48 c4) ∷
   rw 32 (q47 c4) ∷
   rw 33 (q24 c4) ∷
   rw⁻ 29 (q45 c4) ∷
   rw⁻ 28 (q44 c4) ∷
   rw 28 (q45 c4) ∷
   rw 27 (q46 c4) ∷
   rw 28 (q47 c4) ∷
   rw 29 (q48 c4) ∷
   rw 30 (q47 c4) ∷
   rw 31 (q24 c4) ∷
   rw⁻ 27 (q45 c4) ∷
   rw⁻ 28 (q5 c4) ∷
   rw 28 (q5 c4) ∷
   rw⁻ 31 (q30 c4) ∷
   rw 31 (q31 c4) ∷
   rw 30 (q9 c4) ∷
   rw 31 (q10 c4) ∷
   rw 32 (q11 c4) ∷
   rw 33 (q10 c4) ∷
   rw 34 (q12 c4) ∷
   rw⁻ 30 (q31 c4) ∷
   rw⁻ 29 (q30 c4) ∷
   rw 29 (q31 c4) ∷
   rw 28 (q9 c4) ∷
   rw 29 (q10 c4) ∷
   rw 30 (q11 c4) ∷
   rw 31 (q10 c4) ∷
   rw 32 (q12 c4) ∷
   rw⁻ 28 (q31 c4) ∷
   rw⁻ 29 (q5 c4) ∷
   rw 29 (q5 c4) ∷
   rw⁻ 32 (q44 c4) ∷
   rw 32 (q45 c4) ∷
   rw 31 (q46 c4) ∷
   rw 32 (q47 c4) ∷
   rw 33 (q48 c4) ∷
   rw 34 (q47 c4) ∷
   rw 35 (q24 c4) ∷
   rw⁻ 31 (q45 c4) ∷
   rw⁻ 30 (q44 c4) ∷
   rw 30 (q45 c4) ∷
   rw 29 (q46 c4) ∷
   rw 30 (q47 c4) ∷
   rw 31 (q48 c4) ∷
   rw 32 (q47 c4) ∷
   rw 33 (q24 c4) ∷
   rw⁻ 29 (q45 c4) ∷
   rw⁻ 30 (q5 c4) ∷
   rw 30 (q27 c4) ∷
   rw 30 (q28 c4) ∷
   rw 33 (q29 c4) ∷
   rw 33 (q5 c4) ∷
   rw⁻ 36 (q44 c4) ∷
   rw 36 (q45 c4) ∷
   rw 35 (q46 c4) ∷
   rw 36 (q47 c4) ∷
   rw 37 (q48 c4) ∷
   rw 38 (q47 c4) ∷
   rw 39 (q24 c4) ∷
   rw⁻ 35 (q45 c4) ∷
   rw⁻ 34 (q44 c4) ∷
   rw 34 (q45 c4) ∷
   rw 33 (q46 c4) ∷
   rw 34 (q47 c4) ∷
   rw 35 (q48 c4) ∷
   rw 36 (q47 c4) ∷
   rw 37 (q24 c4) ∷
   rw⁻ 33 (q45 c4) ∷
   rw⁻ 34 (q5 c4) ∷
   rw 34 (q5 c4) ∷
   rw⁻ 37 (q32 c4) ∷
   rw 36 (q33 c4) ∷
   rw⁻ 35 (q32 c4) ∷
   rw 34 (q33 c4) ∷
   rw⁻ 35 (q5 c4) ∷
   rw 35 (q49 c4) ∷
   rw 1 (q37 c4) ∷
   rw 3 (q38 c4) ∷
   rw 4 (q50 c4) ∷
   rw 29 (q40 c4) ∷
   rw 5 (q39 c4) ∷
   rw 6 (q40 c4) ∷
   rw 7 (q51 c4) ∷
   rw 17 (q40 c4) ∷
   rw 8 (q52 c4) ∷
   rw 9 (q38 c4) ∷
   rw 9 (q37 c4) ∷
   rw 11 (q38 c4) ∷
   rw 15 (q40 c4) ∷
   rw 16 (q40 c4) ∷ []) Eq.refl
