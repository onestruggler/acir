{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD005 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D005 (Sᴰ : SD005) where

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
  lem-comm-CX02-CCZ134 : Ws → St 0
  lem-comm-CX02-CCZ134 = pickᴰ 0 Sᴰ
  lem-comm-CX04-CCZ123 : Ws → St 1
  lem-comm-CX04-CCZ123 = pickᴰ 1 Sᴰ
  lem-comm-CX12-CCZ034 : Ws → St 2
  lem-comm-CX12-CCZ034 = pickᴰ 2 Sᴰ
  lem-comm-CX13-CCZ024 : Ws → St 3
  lem-comm-CX13-CCZ024 = pickᴰ 3 Sᴰ
  lem-comm-CX14-CCZ023 : Ws → St 4
  lem-comm-CX14-CCZ023 = pickᴰ 4 Sᴰ
  lem-comm-CX21-CCZ034 : Ws → St 5
  lem-comm-CX21-CCZ034 = pickᴰ 5 Sᴰ
  lem-comm-CX23-CCZ014 : Ws → St 6
  lem-comm-CX23-CCZ014 = pickᴰ 6 Sᴰ
  lem-comm-CX24-CCZ013 : Ws → St 7
  lem-comm-CX24-CCZ013 = pickᴰ 7 Sᴰ
  lem-comm-CX31-CCZ024 : Ws → St 8
  lem-comm-CX31-CCZ024 = pickᴰ 8 Sᴰ
  lem-comm-CX32-CCZ014 : Ws → St 9
  lem-comm-CX32-CCZ014 = pickᴰ 9 Sᴰ
  lem-comm-CX42-CCZ013 : Ws → St 10
  lem-comm-CX42-CCZ013 = pickᴰ 10 Sᴰ
  lem-comm-SWAP13-BOX⟨0·42⟩ : Ws → St 13
  lem-comm-SWAP13-BOX⟨0·42⟩ = pickᴰ 11 Sᴰ
  lem-comm-SWAP14-BOX⟨0·23⟩ : Ws → St 14
  lem-comm-SWAP14-BOX⟨0·23⟩ = pickᴰ 12 Sᴰ
  lem-comm-CX03-CCZ124 : Ws → St 18
  lem-comm-CX03-CCZ124 = pickᴰ 13 Sᴰ
  lem-comm-CX30-CCZ124 : Ws → St 19
  lem-comm-CX30-CCZ124 = pickᴰ 14 Sᴰ
  lem-comm-CX40-CCZ123 : Ws → St 20
  lem-comm-CX40-CCZ123 = pickᴰ 15 Sᴰ
  lem-comm-CX41-CCZ023 : Ws → St 21
  lem-comm-CX41-CCZ023 = pickᴰ 16 Sᴰ
  lem-comm-SWAP12-BOX⟨3·04⟩ : Ws → St 23
  lem-comm-SWAP12-BOX⟨3·04⟩ = pickᴰ 17 Sᴰ
  lem-comm-SWAP12-BOX⟨3·40⟩ : Ws → St 43
  lem-comm-SWAP12-BOX⟨3·40⟩ = pickᴰ 18 Sᴰ
  lem-comm-SWAP14-BOX⟨2·03⟩ : Ws → St 24
  lem-comm-SWAP14-BOX⟨2·03⟩ = pickᴰ 19 Sᴰ
  lem-comm-SWAP23-BOX⟨0·41⟩ : Ws → St 27
  lem-comm-SWAP23-BOX⟨0·41⟩ = pickᴰ 20 Sᴰ
  lem-comm-SWAP24-BOX⟨0·13⟩ : Ws → St 28
  lem-comm-SWAP24-BOX⟨0·13⟩ = pickᴰ 21 Sᴰ
  lem-comm-CX20-CCZ134 : Ws → St 44
  lem-comm-CX20-CCZ134 = pickᴰ 22 Sᴰ
  lem-comm-SWAP02-BOX⟨3·41⟩ : Ws → St 45
  lem-comm-SWAP02-BOX⟨3·41⟩ = pickᴰ 23 Sᴰ
  lem-comm-SWAP03-BOX⟨4·21⟩ : Ws → St 46
  lem-comm-SWAP03-BOX⟨4·21⟩ = pickᴰ 24 Sᴰ
  lem-comm-SWAP04-BOX⟨3·21⟩ : Ws → St 47
  lem-comm-SWAP04-BOX⟨3·21⟩ = pickᴰ 25 Sᴰ
  lem-comm-SWAP12-BOX⟨4·03⟩ : Ws → St 48
  lem-comm-SWAP12-BOX⟨4·03⟩ = pickᴰ 26 Sᴰ
  lem-comm-SWAP13-BOX⟨2·04⟩ : Ws → St 49
  lem-comm-SWAP13-BOX⟨2·04⟩ = pickᴰ 27 Sᴰ
  lem-comm-SWAP14-BOX⟨3·02⟩ : Ws → St 50
  lem-comm-SWAP14-BOX⟨3·02⟩ = pickᴰ 28 Sᴰ
  lem-comm-SWAP12-BOX⟨4·30⟩ : Ws → St 51
  lem-comm-SWAP12-BOX⟨4·30⟩ = pickᴰ 29 Sᴰ
  lem-comm-SWAP13-BOX⟨4·20⟩ : Ws → St 52
  lem-comm-SWAP13-BOX⟨4·20⟩ = pickᴰ 30 Sᴰ
  lem-cQ-at021021 : Ws → St 29
  lem-cQ-at021021 = pickᴰ 31 Sᴰ
  lem-sym-ab-at0210243143 : Ws → St 53
  lem-sym-ab-at0210243143 = pickᴰ 32 Sᴰ
  lem-sym-ab-at032032 : Ws → St 54
  lem-sym-ab-at032032 = pickᴰ 33 Sᴰ
  lem-sym-ab-at1221 : Ws → St 55
  lem-sym-ab-at1221 = pickᴰ 34 Sᴰ
  lem-cQ-at0213243041 : Ws → St 56
  lem-cQ-at0213243041 = pickᴰ 35 Sᴰ
  lem-cQ-at0214233041 : Ws → St 57
  lem-cQ-at0214233041 = pickᴰ 36 Sᴰ
  lem-cQ-at0310213442 : Ws → St 58
  lem-cQ-at0310213442 = pickᴰ 37 Sᴰ
  lem-sym-ab-at021021 : Ws → St 59
  lem-sym-ab-at021021 = pickᴰ 38 Sᴰ
  lem-sym-ab-at0220 : Ws → St 60
  lem-sym-ab-at0220 = pickᴰ 39 Sᴰ
  lem-cQ-at03203442 : Ws → St 61
  lem-cQ-at03203442 = pickᴰ 40 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = wpE 196 c4
  q2 : Ws → Eqn
  q2 c4 = wpE 570 c4
  q3 : Ws → Eqn
  q3 c4 = wpE 194 c4
  q4 : Ws → Eqn
  q4 c4 = wpE 569 c4
  q5 : Ws → Eqn
  q5 c4 = sE 14 (lem-comm-SWAP14-BOX⟨0·23⟩ c4)
  q6 : Ws → Eqn
  q6 c4 = wlE 306 (lit c4)

-- nat-SWbc @12213443: 23 steps
lem-nat-SWbc-at12213443 : Ws → ⟪ (ℓ "乘仑乘") ⟫ʷ ≈ ⟪ (ℓ "仛") ⟫ʷ
lem-nat-SWbc-at12213443 c4 = derive (ℓ "乘仑乘") (ℓ "仛")
  (re 1 1 (ℓ "二亍仐亍二仐") ∷
   rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   re 3 1 (ℓ "亜亞仏亞亜仏") ∷
   rw⁻ 2 (q3 c4) ∷
   rw 3 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   rw 5 (q4 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   rw 7 (q5 c4) ∷
   rw 8 (q2 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   re 11 1 (ℓ "亜亞仏亞亜仏") ∷
   rw⁻ 10 (q3 c4) ∷
   rw 11 (q4 c4) ∷
   rw 12 (q5 c4) ∷
   rw 13 (q4 c4) ∷
   rw⁻ 14 (q3 c4) ∷
   rw 15 (q5 c4) ∷
   rw 16 (q6 c4) ∷
   re 2 6 (ℓ "仚") ∷
   re 5 6 (ℓ "仚") ∷
   re 0 6 (ℓ "仛") ∷ []) Eq.refl

private
  q7 : Ws → Eqn
  q7 c4 = wpE 596 c4
  q8 : Ws → Eqn
  q8 c4 = wpE 986 c4
  q9 : Ws → Eqn
  q9 c4 = wpE 594 c4
  q10 : Ws → Eqn
  q10 c4 = wpE 987 c4
  q11 : Ws → Eqn
  q11 c4 = sE 27 (lem-comm-SWAP23-BOX⟨0·41⟩ c4)
  q12 : Ws → Eqn
  q12 c4 = wlE 3 (lit c4)

-- nat-SWbc @14233241: 23 steps
lem-nat-SWbc-at14233241 : Ws → ⟪ (ℓ "乥伍乥") ⟫ʷ ≈ ⟪ (ℓ "伈") ⟫ʷ
lem-nat-SWbc-at14233241 c4 = derive (ℓ "乥伍乥") (ℓ "伈")
  (re 1 1 (ℓ "亠亡伌亡亠伌") ∷
   rw⁻ 0 (q7 c4) ∷
   rw 1 (q8 c4) ∷
   re 3 1 (ℓ "亜亟价亟亜价") ∷
   rw⁻ 2 (q9 c4) ∷
   rw 3 (q10 c4) ∷
   rw 4 (q11 c4) ∷
   rw 5 (q10 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   rw 7 (q11 c4) ∷
   rw 8 (q8 c4) ∷
   rw⁻ 9 (q7 c4) ∷
   re 11 1 (ℓ "亜亟价亟亜价") ∷
   rw⁻ 10 (q9 c4) ∷
   rw 11 (q10 c4) ∷
   rw 12 (q11 c4) ∷
   rw 13 (q10 c4) ∷
   rw⁻ 14 (q9 c4) ∷
   rw 15 (q11 c4) ∷
   rw 16 (q12 c4) ∷
   re 2 6 (ℓ "伇") ∷
   re 5 6 (ℓ "伇") ∷
   re 0 6 (ℓ "伈") ∷ []) Eq.refl

private
  q13 : Ws → Eqn
  q13 c4 = wlE 675 (lit c4)
  q14 : Ws → Eqn
  q14 c4 = wpE 185 c4
  q15 : Ws → Eqn
  q15 c4 = sE 10 (lem-comm-CX42-CCZ013 c4)
  q16 : Ws → Eqn
  q16 c4 = wlE 1167 (lit c4)
  q17 : Ws → Eqn
  q17 c4 = wlE 324 (lit c4)

-- cQ @03143140: 7 steps
lem-cQ-at03143140 : Ws → ⟪ (ℓ "亰亐") ⟫ʷ ≈ ⟪ (ℓ "亐亰") ⟫ʷ
lem-cQ-at03143140 c4 = derive (ℓ "亰亐") (ℓ "亐亰")
  (rw 0 (q13 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   rw 3 (q15 c4) ∷
   rw⁻ 2 (q16 c4) ∷
   rw 1 (q15 c4) ∷
   rw⁻ 0 (q17 c4) ∷
   rw⁻ 1 (q13 c4) ∷ []) Eq.refl

private
  q18 : Ws → Eqn
  q18 c4 = wlE 37 (lit c4)
  q19 : Ws → Eqn
  q19 c4 = wlE 38 (lit c4)
  q20 : Ws → Eqn
  q20 c4 = wlE 44 (lit c4)
  q21 : Ws → Eqn
  q21 c4 = wlE 84 (lit c4)
  q22 : Ws → Eqn
  q22 c4 = sE 43 (lem-comm-SWAP12-BOX⟨3·40⟩ c4)
  q23 : Ws → Eqn
  q23 c4 = wlE 6 (lit c4)

-- nat-SWbc @03143140: 23 steps
lem-nat-SWbc-at03143140 : Ws → ⟪ (ℓ "乊侌乊") ⟫ʷ ≈ ⟪ (ℓ "侅") ⟫ʷ
lem-nat-SWbc-at03143140 c4 = derive (ℓ "乊侌乊") (ℓ "侅")
  (re 1 1 (ℓ "亰亲例亲亰例") ∷
   rw⁻ 0 (q18 c4) ∷
   rw 1 (q19 c4) ∷
   re 3 1 (ℓ "京亯佶亯京佶") ∷
   rw⁻ 2 (q20 c4) ∷
   rw 3 (q21 c4) ∷
   rw 4 (q22 c4) ∷
   rw 5 (q21 c4) ∷
   rw⁻ 6 (q20 c4) ∷
   rw 7 (q22 c4) ∷
   rw 8 (q19 c4) ∷
   rw⁻ 9 (q18 c4) ∷
   re 11 1 (ℓ "京亯佶亯京佶") ∷
   rw⁻ 10 (q20 c4) ∷
   rw 11 (q21 c4) ∷
   rw 12 (q22 c4) ∷
   rw 13 (q21 c4) ∷
   rw⁻ 14 (q20 c4) ∷
   rw 15 (q22 c4) ∷
   rw 16 (q23 c4) ∷
   re 2 6 (ℓ "侄") ∷
   re 5 6 (ℓ "侄") ∷
   re 0 6 (ℓ "侅") ∷ []) Eq.refl

private
  q24 : Ws → Eqn
  q24 c4 = wlE 617 (lit c4)
  q25 : Ws → Eqn
  q25 c4 = wpE 543 c4
  q26 : Ws → Eqn
  q26 c4 = sE 21 (lem-comm-CX41-CCZ023 c4)
  q27 : Ws → Eqn
  q27 c4 = wlE 669 (lit c4)
  q28 : Ws → Eqn
  q28 c4 = wlE 670 (lit c4)

-- cQ @0314213240: 7 steps
lem-cQ-at0314213240 : Ws → ⟪ (ℓ "京亘") ⟫ʷ ≈ ⟪ (ℓ "亘京") ⟫ʷ
lem-cQ-at0314213240 c4 = derive (ℓ "京亘") (ℓ "亘京")
  (rw 0 (q24 c4) ∷
   rw⁻ 4 (q25 c4) ∷
   rw 3 (q26 c4) ∷
   rw⁻ 2 (q27 c4) ∷
   rw 1 (q26 c4) ∷
   rw⁻ 0 (q28 c4) ∷
   rw⁻ 1 (q24 c4) ∷ []) Eq.refl

private
  q29 : Ws → Eqn
  q29 c4 = wlE 698 (lit c4)
  q30 : Ws → Eqn
  q30 c4 = sE 4 (lem-comm-CX14-CCZ023 c4)
  q31 : Ws → Eqn
  q31 c4 = wpE 574 c4

-- cQ @03243240: 7 steps
lem-cQ-at03243240 : Ws → ⟪ (ℓ "京亘") ⟫ʷ ≈ ⟪ (ℓ "亘京") ⟫ʷ
lem-cQ-at03243240 c4 = derive (ℓ "京亘") (ℓ "亘京")
  (rw 0 (q29 c4) ∷
   rw⁻ 4 (q28 c4) ∷
   rw 3 (q30 c4) ∷
   rw⁻ 2 (q31 c4) ∷
   rw 1 (q30 c4) ∷
   rw⁻ 0 (q25 c4) ∷
   rw⁻ 1 (q29 c4) ∷ []) Eq.refl

private
  q32 : Ws → Eqn
  q32 c4 = wlE 45 (lit c4)
  q33 : Ws → Eqn
  q33 c4 = wlE 85 (lit c4)

-- nat-SWbc @0314213240: 23 steps
lem-nat-SWbc-at0314213240 : Ws → ⟪ (ℓ "乊侅乊") ⟫ʷ ≈ ⟪ (ℓ "侌") ⟫ʷ
lem-nat-SWbc-at0314213240 c4 = derive (ℓ "乊侅乊") (ℓ "侌")
  (re 1 1 (ℓ "京亮侄亮京侄") ∷
   rw⁻ 0 (q20 c4) ∷
   rw 1 (q32 c4) ∷
   re 3 1 (ℓ "亰亳佶亳亰佶") ∷
   rw⁻ 2 (q18 c4) ∷
   rw 3 (q33 c4) ∷
   rw 4 (q22 c4) ∷
   rw 5 (q33 c4) ∷
   rw⁻ 6 (q18 c4) ∷
   rw 7 (q22 c4) ∷
   rw 8 (q32 c4) ∷
   rw⁻ 9 (q20 c4) ∷
   re 11 1 (ℓ "亰亳佶亳亰佶") ∷
   rw⁻ 10 (q18 c4) ∷
   rw 11 (q33 c4) ∷
   rw 12 (q22 c4) ∷
   rw 13 (q33 c4) ∷
   rw⁻ 14 (q18 c4) ∷
   rw 15 (q22 c4) ∷
   rw 16 (q23 c4) ∷
   re 2 6 (ℓ "例") ∷
   re 5 6 (ℓ "例") ∷
   re 0 6 (ℓ "侌") ∷ []) Eq.refl

private
  q34 : Ws → Eqn
  q34 c4 = wlE 458 (lit c4)
  q35 : Ws → Eqn
  q35 c4 = wpE 706 c4
  q36 : Ws → Eqn
  q36 c4 = sE 0 (lem-comm-CX02-CCZ134 c4)
  q37 : Ws → Eqn
  q37 c4 = wlE 1237 (lit c4)
  q38 : Ws → Eqn
  q38 c4 = wlE 790 (lit c4)

-- cQ @03103441: 7 steps
lem-cQ-at03103441 : Ws → ⟪ (ℓ "亘京") ⟫ʷ ≈ ⟪ (ℓ "京亘") ⟫ʷ
lem-cQ-at03103441 c4 = derive (ℓ "亘京") (ℓ "京亘")
  (rw 0 (q34 c4) ∷
   rw⁻ 4 (q35 c4) ∷
   rw 3 (q36 c4) ∷
   rw⁻ 2 (q37 c4) ∷
   rw 1 (q36 c4) ∷
   rw⁻ 0 (q38 c4) ∷
   rw⁻ 1 (q34 c4) ∷ []) Eq.refl

private
  q39 : Ws → Eqn
  q39 c4 = wpE 352 c4
  q40 : Ws → Eqn
  q40 c4 = wlE 490 (lit c4)
  q41 : Ws → Eqn
  q41 c4 = sE 1 (lem-comm-CX04-CCZ123 c4)
  q42 : Ws → Eqn
  q42 c4 = wlE 491 (lit c4)
  q43 : Ws → Eqn
  q43 c4 = wlE 492 (lit c4)

-- cQ @0310243241: 7 steps
lem-cQ-at0310243241 : Ws → ⟪ (ℓ "亠交") ⟫ʷ ≈ ⟪ (ℓ "交亠") ⟫ʷ
lem-cQ-at0310243241 c4 = derive (ℓ "亠交") (ℓ "交亠")
  (rw 0 (q39 c4) ∷
   rw⁻ 4 (q40 c4) ∷
   rw 3 (q41 c4) ∷
   rw⁻ 2 (q42 c4) ∷
   rw 1 (q41 c4) ∷
   rw⁻ 0 (q43 c4) ∷
   rw⁻ 1 (q39 c4) ∷ []) Eq.refl

private
  q44 : Ws → Eqn
  q44 c4 = wpE 149 c4
  q45 : Ws → Eqn
  q45 c4 = wpE 289 c4
  q46 : Ws → Eqn
  q46 c4 = wpE 151 c4
  q47 : Ws → Eqn
  q47 c4 = wpE 288 c4
  q48 : Ws → Eqn
  q48 c4 = sE 50 (lem-comm-SWAP14-BOX⟨3·02⟩ c4)

-- nat-SWbc @0310243142: 23 steps
lem-nat-SWbc-at0310243142 : Ws → ⟪ (ℓ "乘佨乘") ⟫ʷ ≈ ⟪ (ℓ "佥") ⟫ʷ
lem-nat-SWbc-at0310243142 c4 = derive (ℓ "乘佨乘") (ℓ "佥")
  (re 1 1 (ℓ "亠亢仡亢亠仡") ∷
   rw⁻ 0 (q44 c4) ∷
   rw 1 (q45 c4) ∷
   re 3 1 (ℓ "亐云仠云亐仠") ∷
   rw⁻ 2 (q46 c4) ∷
   rw 3 (q47 c4) ∷
   rw 4 (q48 c4) ∷
   rw 5 (q47 c4) ∷
   rw⁻ 6 (q46 c4) ∷
   rw 7 (q48 c4) ∷
   rw 8 (q45 c4) ∷
   rw⁻ 9 (q44 c4) ∷
   re 11 1 (ℓ "亐云仠云亐仠") ∷
   rw⁻ 10 (q46 c4) ∷
   rw 11 (q47 c4) ∷
   rw 12 (q48 c4) ∷
   rw 13 (q47 c4) ∷
   rw⁻ 14 (q46 c4) ∷
   rw 15 (q48 c4) ∷
   rw 16 (q6 c4) ∷
   re 2 6 (ℓ "仴") ∷
   re 5 6 (ℓ "仴") ∷
   re 0 6 (ℓ "佥") ∷ []) Eq.refl

private
  q49 : Ws → Eqn
  q49 c4 = wpE 1068 c4
  q50 : Ws → Eqn
  q50 c4 = wlE 519 (lit c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (ℓ "个亰") (ℓ "亰个") (c₂ (CZ) (CCZ))
  q52 : Ws → Eqn
  q52 c4 = sE 58 (lem-cQ-at0310213442 c4)
  q53 : Ws → Eqn
  q53 c4 = wlE 520 (lit c4)

-- box-tQ @0310213442: 13 steps
lem-box-tQ-at0310213442 : Ws → ⟪ (ℓ "佥") ⟫ʷ ≈ ⟪ (ℓ "亓亰亓亰") ⟫ʷ
lem-box-tQ-at0310213442 c4 = derive (ℓ "佥") (ℓ "亓亰亓亰")
  (re 0 1 (ℓ "亐亓仴亓亐仴") ∷
   re 2 1 (ℓ "亠亡仠亡亠仠") ∷
   re 4 1 (ℓ "丱") ∷
   re 7 1 (ℓ "丱") ∷
   rw 2 (q49 c4) ∷
   re 5 1 (ℓ "亠亡仠亡亠仠") ∷
   re 7 1 (ℓ "丱") ∷
   re 10 1 (ℓ "丱") ∷
   rw 5 (q49 c4) ∷
   rw 0 (q50 c4) ∷
   rw 2 (q51 c4) ∷
   rw 1 (q52 c4) ∷
   rw 2 (q53 c4) ∷ []) Eq.refl

private
  q54 : Ws → Eqn
  q54 c4 = wpE 152 c4
  q55 : Ws → Eqn
  q55 c4 = wpE 150 c4

-- nat-SWbc @0310213442: 23 steps
lem-nat-SWbc-at0310213442 : Ws → ⟪ (ℓ "乘佥乘") ⟫ʷ ≈ ⟪ (ℓ "佨") ⟫ʷ
lem-nat-SWbc-at0310213442 c4 = derive (ℓ "乘佥乘") (ℓ "佨")
  (re 1 1 (ℓ "亐亓仴亓亐仴") ∷
   rw⁻ 0 (q46 c4) ∷
   rw 1 (q54 c4) ∷
   re 3 1 (ℓ "亠亡仠亡亠仠") ∷
   rw⁻ 2 (q44 c4) ∷
   rw 3 (q55 c4) ∷
   rw 4 (q48 c4) ∷
   rw 5 (q55 c4) ∷
   rw⁻ 6 (q44 c4) ∷
   rw 7 (q48 c4) ∷
   rw 8 (q54 c4) ∷
   rw⁻ 9 (q46 c4) ∷
   re 11 1 (ℓ "亠亡仠亡亠仠") ∷
   rw⁻ 10 (q44 c4) ∷
   rw 11 (q55 c4) ∷
   rw 12 (q48 c4) ∷
   rw 13 (q55 c4) ∷
   rw⁻ 14 (q44 c4) ∷
   rw 15 (q48 c4) ∷
   rw 16 (q6 c4) ∷
   re 2 6 (ℓ "仡") ∷
   re 5 6 (ℓ "仡") ∷
   re 0 6 (ℓ "佨") ∷ []) Eq.refl

private
  q56 : Ws → Eqn
  q56 c4 = wlE 1270 (lit c4)
  q57 : Ws → Eqn
  q57 c4 = sE 44 (lem-comm-CX20-CCZ134 c4)
  q58 : Ws → Eqn
  q58 c4 = wpE 704 c4

-- cQ @0312203441: 7 steps
lem-cQ-at0312203441 : Ws → ⟪ (ℓ "亘京") ⟫ʷ ≈ ⟪ (ℓ "京亘") ⟫ʷ
lem-cQ-at0312203441 c4 = derive (ℓ "亘京") (ℓ "京亘")
  (rw 0 (q56 c4) ∷
   rw⁻ 4 (q38 c4) ∷
   rw 3 (q57 c4) ∷
   rw⁻ 2 (q58 c4) ∷
   rw 1 (q57 c4) ∷
   rw⁻ 0 (q35 c4) ∷
   rw⁻ 1 (q56 c4) ∷ []) Eq.refl

private
  q59 : Ws → Eqn
  q59 c4 = wpE 1089 c4
  q60 : Ws → Eqn
  q60 c4 = wpE 1090 c4
  q61 : Ws → Eqn
  q61 c4 = wpE 1091 c4
  q62 : Ws → Eqn
  q62 c4 = wpE 1092 c4
  q63 : Ws → Eqn
  q63 c4 = sE 47 (lem-comm-SWAP04-BOX⟨3·21⟩ c4)
  q64 : Ws → Eqn
  q64 c4 = wpE 1093 c4

-- nat-SWbc @0312203441: 23 steps
lem-nat-SWbc-at0312203441 : Ws → ⟪ (ℓ "乀佱乀") ⟫ʷ ≈ ⟪ (ℓ "佴") ⟫ʷ
lem-nat-SWbc-at0312203441 c4 = derive (ℓ "乀佱乀") (ℓ "佴")
  (re 1 1 (ℓ "亘些佌些亘佌") ∷
   rw⁻ 0 (q59 c4) ∷
   rw 1 (q60 c4) ∷
   re 3 1 (ℓ "亰亱伸亱亰伸") ∷
   rw⁻ 2 (q61 c4) ∷
   rw 3 (q62 c4) ∷
   rw 4 (q63 c4) ∷
   rw 5 (q62 c4) ∷
   rw⁻ 6 (q61 c4) ∷
   rw 7 (q63 c4) ∷
   rw 8 (q60 c4) ∷
   rw⁻ 9 (q59 c4) ∷
   re 11 1 (ℓ "亰亱伸亱亰伸") ∷
   rw⁻ 10 (q61 c4) ∷
   rw 11 (q62 c4) ∷
   rw 12 (q63 c4) ∷
   rw 13 (q62 c4) ∷
   rw⁻ 14 (q61 c4) ∷
   rw 15 (q63 c4) ∷
   rw 16 (q64 c4) ∷
   re 2 6 (ℓ "伹") ∷
   re 5 6 (ℓ "伹") ∷
   re 0 6 (ℓ "佴") ∷ []) Eq.refl

private
  q65 : Ws → Eqn
  q65 c4 = wlE 245 (lit c4)
  q66 : Ws → Eqn
  q66 c4 = sE 7 (lem-comm-CX24-CCZ013 c4)
  q67 : Ws → Eqn
  q67 c4 = wpE 184 c4

-- cQ @0312243041: 7 steps
lem-cQ-at0312243041 : Ws → ⟪ (ℓ "亰亐") ⟫ʷ ≈ ⟪ (ℓ "亐亰") ⟫ʷ
lem-cQ-at0312243041 c4 = derive (ℓ "亰亐") (ℓ "亐亰")
  (rw 0 (q65 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 3 (q66 c4) ∷
   rw⁻ 2 (q67 c4) ∷
   rw 1 (q66 c4) ∷
   rw⁻ 0 (q14 c4) ∷
   rw⁻ 1 (q65 c4) ∷ []) Eq.refl

private
  q68 : Ws → Eqn
  q68 c4 = wpE 1103 c4
  q69 : Ws → Eqn
  q69 c4 = wpE 1104 c4

-- nat-SWbc @0312243041: 23 steps
lem-nat-SWbc-at0312243041 : Ws → ⟪ (ℓ "乀佴乀") ⟫ʷ ≈ ⟪ (ℓ "佱") ⟫ʷ
lem-nat-SWbc-at0312243041 c4 = derive (ℓ "乀佴乀") (ℓ "佱")
  (re 1 1 (ℓ "亰亲伹亲亰伹") ∷
   rw⁻ 0 (q61 c4) ∷
   rw 1 (q68 c4) ∷
   re 3 1 (ℓ "亘亚伸亚亘伸") ∷
   rw⁻ 2 (q59 c4) ∷
   rw 3 (q69 c4) ∷
   rw 4 (q63 c4) ∷
   rw 5 (q69 c4) ∷
   rw⁻ 6 (q59 c4) ∷
   rw 7 (q63 c4) ∷
   rw 8 (q68 c4) ∷
   rw⁻ 9 (q61 c4) ∷
   re 11 1 (ℓ "亘亚伸亚亘伸") ∷
   rw⁻ 10 (q59 c4) ∷
   rw 11 (q69 c4) ∷
   rw 12 (q63 c4) ∷
   rw 13 (q69 c4) ∷
   rw⁻ 14 (q59 c4) ∷
   rw 15 (q63 c4) ∷
   rw 16 (q64 c4) ∷
   re 2 6 (ℓ "佌") ∷
   re 5 6 (ℓ "佌") ∷
   re 0 6 (ℓ "佱") ∷ []) Eq.refl

private
  q70 : Ws → Eqn
  q70 c4 = wpE 584 c4
  q71 : Ws → Eqn
  q71 c4 = wpE 1116 c4
  q72 : Ws → Eqn
  q72 c4 = wpE 582 c4
  q73 : Ws → Eqn
  q73 c4 = wpE 1117 c4
  q74 : Ws → Eqn
  q74 c4 = sE 28 (lem-comm-SWAP24-BOX⟨0·13⟩ c4)
  q75 : Ws → Eqn
  q75 c4 = wlE 322 (lit c4)

-- nat-SWbc @3443: 23 steps
lem-nat-SWbc-at3443 : Ws → ⟪ (ℓ "乬亼乬") ⟫ʷ ≈ ⟪ (ℓ "仄") ⟫ʷ
lem-nat-SWbc-at3443 c4 = derive (ℓ "乬亼乬") (ℓ "仄")
  (re 1 1 (ℓ "二亍亻亍二亻") ∷
   rw⁻ 0 (q70 c4) ∷
   rw 1 (q71 c4) ∷
   re 3 1 (ℓ "五亖人亖五人") ∷
   rw⁻ 2 (q72 c4) ∷
   rw 3 (q73 c4) ∷
   rw 4 (q74 c4) ∷
   rw 5 (q73 c4) ∷
   rw⁻ 6 (q72 c4) ∷
   rw 7 (q74 c4) ∷
   rw 8 (q71 c4) ∷
   rw⁻ 9 (q70 c4) ∷
   re 11 1 (ℓ "五亖人亖五人") ∷
   rw⁻ 10 (q72 c4) ∷
   rw 11 (q73 c4) ∷
   rw 12 (q74 c4) ∷
   rw 13 (q73 c4) ∷
   rw⁻ 14 (q72 c4) ∷
   rw 15 (q74 c4) ∷
   rw 16 (q75 c4) ∷
   re 2 6 (ℓ "仃") ∷
   re 5 6 (ℓ "仃") ∷
   re 0 6 (ℓ "仄") ∷ []) Eq.refl

-- cQ @03122031: 7 steps
lem-cQ-at03122031 : Ws → ⟪ (ℓ "亘京") ⟫ʷ ≈ ⟪ (ℓ "京亘") ⟫ʷ
lem-cQ-at03122031 c4 = derive (ℓ "亘京") (ℓ "京亘")
  (rw 0 (q56 c4) ∷
   rw⁻ 4 (q38 c4) ∷
   rw 3 (q57 c4) ∷
   rw⁻ 2 (q58 c4) ∷
   rw 1 (q57 c4) ∷
   rw⁻ 0 (q35 c4) ∷
   rw⁻ 1 (q56 c4) ∷ []) Eq.refl

-- cQ @031031: 7 steps
lem-cQ-at031031 : Ws → ⟪ (ℓ "亘京") ⟫ʷ ≈ ⟪ (ℓ "京亘") ⟫ʷ
lem-cQ-at031031 c4 = derive (ℓ "亘京") (ℓ "京亘")
  (rw 0 (q34 c4) ∷
   rw⁻ 4 (q35 c4) ∷
   rw 3 (q36 c4) ∷
   rw⁻ 2 (q37 c4) ∷
   rw 1 (q36 c4) ∷
   rw⁻ 0 (q38 c4) ∷
   rw⁻ 1 (q34 c4) ∷ []) Eq.refl

private
  q76 : Ws → Eqn
  q76 c4 = wlE 838 (lit c4)
  q77 : Ws → Eqn
  q77 c4 = wlE 877 (lit c4)
  q78 : Ws → Eqn
  q78 c4 = wlE 840 (lit c4)
  q79 : Ws → Eqn
  q79 c4 = wlE 876 (lit c4)
  q80 : Ws → Eqn
  q80 c4 = sE 23 (lem-comm-SWAP12-BOX⟨3·04⟩ c4)

-- nat-SWbc @031031: 23 steps
lem-nat-SWbc-at031031 : Ws → ⟪ (ℓ "乊佦乊") ⟫ʷ ≈ ⟪ (ℓ "佤") ⟫ʷ
lem-nat-SWbc-at031031 c4 = derive (ℓ "乊佦乊") (ℓ "佤")
  (re 1 1 (ℓ "亘些仦些亘仦") ∷
   rw⁻ 0 (q76 c4) ∷
   rw 1 (q77 c4) ∷
   re 3 1 (ℓ "亐云以云亐以") ∷
   rw⁻ 2 (q78 c4) ∷
   rw 3 (q79 c4) ∷
   rw 4 (q80 c4) ∷
   rw 5 (q79 c4) ∷
   rw⁻ 6 (q78 c4) ∷
   rw 7 (q80 c4) ∷
   rw 8 (q77 c4) ∷
   rw⁻ 9 (q76 c4) ∷
   re 11 1 (ℓ "亐云以云亐以") ∷
   rw⁻ 10 (q78 c4) ∷
   rw 11 (q79 c4) ∷
   rw 12 (q80 c4) ∷
   rw 13 (q79 c4) ∷
   rw⁻ 14 (q78 c4) ∷
   rw 15 (q80 c4) ∷
   rw 16 (q23 c4) ∷
   re 2 6 (ℓ "仮") ∷
   re 5 6 (ℓ "仮") ∷
   re 0 6 (ℓ "佤") ∷ []) Eq.refl

-- cQ @03143041: 7 steps
lem-cQ-at03143041 : Ws → ⟪ (ℓ "亰亐") ⟫ʷ ≈ ⟪ (ℓ "亐亰") ⟫ʷ
lem-cQ-at03143041 c4 = derive (ℓ "亰亐") (ℓ "亐亰")
  (rw 0 (q13 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   rw 3 (q15 c4) ∷
   rw⁻ 2 (q16 c4) ∷
   rw 1 (q15 c4) ∷
   rw⁻ 0 (q17 c4) ∷
   rw⁻ 1 (q13 c4) ∷ []) Eq.refl

private
  q81 : Ws → Eqn
  q81 c4 = wpE 1146 c4
  q82 : Ws → Eqn
  q82 c4 = wpE 1147 c4
  q83 : Ws → Eqn
  q83 c4 = wpE 1148 c4
  q84 : Ws → Eqn
  q84 c4 = wpE 1149 c4
  q85 : Ws → Eqn
  q85 c4 = sE 45 (lem-comm-SWAP02-BOX⟨3·41⟩ c4)
  q86 : Ws → Eqn
  q86 c4 = wlE 485 (lit c4)

-- nat-SWbc @03143041: 23 steps
lem-nat-SWbc-at03143041 : Ws → ⟪ (ℓ "串侈串") ⟫ʷ ≈ ⟪ (ℓ "佾") ⟫ʷ
lem-nat-SWbc-at03143041 c4 = derive (ℓ "串侈串") (ℓ "佾")
  (re 1 1 (ℓ "亰亲侇亲亰侇") ∷
   rw⁻ 0 (q81 c4) ∷
   rw 1 (q82 c4) ∷
   re 3 1 (ℓ "亠亣佼亣亠佼") ∷
   rw⁻ 2 (q83 c4) ∷
   rw 3 (q84 c4) ∷
   rw 4 (q85 c4) ∷
   rw 5 (q84 c4) ∷
   rw⁻ 6 (q83 c4) ∷
   rw 7 (q85 c4) ∷
   rw 8 (q82 c4) ∷
   rw⁻ 9 (q81 c4) ∷
   re 11 1 (ℓ "亠亣佼亣亠佼") ∷
   rw⁻ 10 (q83 c4) ∷
   rw 11 (q84 c4) ∷
   rw 12 (q85 c4) ∷
   rw 13 (q84 c4) ∷
   rw⁻ 14 (q83 c4) ∷
   rw 15 (q85 c4) ∷
   rw 16 (q86 c4) ∷
   re 2 6 (ℓ "佽") ∷
   re 5 6 (ℓ "佽") ∷
   re 0 6 (ℓ "佾") ∷ []) Eq.refl

private
  q87 : Ws → Eqn
  q87 c4 = wpE 320 c4
  q88 : Ws → Eqn
  q88 c4 = sE 20 (lem-comm-CX40-CCZ123 c4)
  q89 : Ws → Eqn
  q89 c4 = wlE 495 (lit c4)

-- cQ @0314203241: 7 steps
lem-cQ-at0314203241 : Ws → ⟪ (ℓ "亠交") ⟫ʷ ≈ ⟪ (ℓ "交亠") ⟫ʷ
lem-cQ-at0314203241 c4 = derive (ℓ "亠交") (ℓ "交亠")
  (rw 0 (q87 c4) ∷
   rw⁻ 4 (q43 c4) ∷
   rw 3 (q88 c4) ∷
   rw⁻ 2 (q89 c4) ∷
   rw 1 (q88 c4) ∷
   rw⁻ 0 (q40 c4) ∷
   rw⁻ 1 (q87 c4) ∷ []) Eq.refl

private
  q90 : Ws → Eqn
  q90 c4 = wpE 496 c4
  q91 : Ws → Eqn
  q91 c4 = wlE 173 (lit c4)
  q92 : Ws → Eqn
  q92 c4 = wlE 611 (lit c4)
  q93 : Ws → Eqn
  q93 c4 = wlE 171 (lit c4)

-- cQ @02142041: 7 steps
lem-cQ-at02142041 : Ws → ⟪ (ℓ "亜交") ⟫ʷ ≈ ⟪ (ℓ "交亜") ⟫ʷ
lem-cQ-at02142041 c4 = derive (ℓ "亜交") (ℓ "交亜")
  (rw 0 (q90 c4) ∷
   rw⁻ 4 (q91 c4) ∷
   rw 3 (q88 c4) ∷
   rw⁻ 2 (q92 c4) ∷
   rw 1 (q88 c4) ∷
   rw⁻ 0 (q93 c4) ∷
   rw⁻ 1 (q90 c4) ∷ []) Eq.refl

private
  q94 : Ws → Eqn
  q94 c4 = wlE 417 (lit c4)
  q95 : Ws → Eqn
  q95 c4 = wlE 416 (lit c4)
  q96 : Ws → Eqn
  q96 c4 = wlE 175 (lit c4)
  q97 : Ws → Eqn
  q97 c4 = sE 57 (lem-cQ-at0214233041 c4)

-- tP @0214233041: 7 steps
lem-tP-at0214233041 : Ws → ⟪ (ℓ "亱亏") ⟫ʷ ≈ ⟪ (ℓ "亏亱") ⟫ʷ
lem-tP-at0214233041 c4 = derive (ℓ "亱亏") (ℓ "亏亱")
  (rw⁻ 0 (q94 c4) ∷
   rw⁻ 3 (q95 c4) ∷
   rw 2 (q96 c4) ∷
   rw 1 (q97 c4) ∷
   rw⁻ 2 (q96 c4) ∷
   rw 0 (q95 c4) ∷
   rw 1 (q94 c4) ∷ []) Eq.refl

private
  q98 : Ws → Eqn
  q98 c4 = wpE 1162 c4
  q99 : Ws → Eqn
  q99 c4 = wpE 1163 c4

-- nat-SWbc @0314203241: 23 steps
lem-nat-SWbc-at0314203241 : Ws → ⟪ (ℓ "串佾串") ⟫ʷ ≈ ⟪ (ℓ "侈") ⟫ʷ
lem-nat-SWbc-at0314203241 c4 = derive (ℓ "串佾串") (ℓ "侈")
  (re 1 1 (ℓ "亠亢佽亢亠佽") ∷
   rw⁻ 0 (q83 c4) ∷
   rw 1 (q98 c4) ∷
   re 3 1 (ℓ "亰亳佼亳亰佼") ∷
   rw⁻ 2 (q81 c4) ∷
   rw 3 (q99 c4) ∷
   rw 4 (q85 c4) ∷
   rw 5 (q99 c4) ∷
   rw⁻ 6 (q81 c4) ∷
   rw 7 (q85 c4) ∷
   rw 8 (q98 c4) ∷
   rw⁻ 9 (q83 c4) ∷
   re 11 1 (ℓ "亰亳佼亳亰佼") ∷
   rw⁻ 10 (q81 c4) ∷
   rw 11 (q99 c4) ∷
   rw 12 (q85 c4) ∷
   rw 13 (q99 c4) ∷
   rw⁻ 14 (q81 c4) ∷
   rw 15 (q85 c4) ∷
   rw 16 (q86 c4) ∷
   re 2 6 (ℓ "侇") ∷
   re 5 6 (ℓ "侇") ∷
   re 0 6 (ℓ "侈") ∷ []) Eq.refl

private
  q100 : Ws → Eqn
  q100 c4 = wpE 162 c4
  q101 : Ws → Eqn
  q101 c4 = wlE 936 (lit c4)
  q102 : Ws → Eqn
  q102 c4 = eqn (ℓ "二乻") (ℓ "乻二") (c₃ (CCZ) (CZ))
  q103 : Ws → Eqn
  q103 c4 = wlE 937 (lit c4)

-- box-tQ @0214233041: 13 steps
lem-box-tQ-at0214233041 : Ws → ⟪ (ℓ "佢") ⟫ʷ ≈ ⟪ (ℓ "亱二亱二") ⟫ʷ
lem-box-tQ-at0214233041 c4 = derive (ℓ "佢") (ℓ "亱二亱二")
  (re 0 1 (ℓ "亰亱佡亱亰佡") ∷
   re 2 1 (ℓ "亜亟佗亟亜佗") ∷
   re 4 1 (ℓ "乗") ∷
   re 7 1 (ℓ "乗") ∷
   rw⁻ 2 (q100 c4) ∷
   re 5 1 (ℓ "亜亟佗亟亜佗") ∷
   re 7 1 (ℓ "乗") ∷
   re 10 1 (ℓ "乗") ∷
   rw⁻ 5 (q100 c4) ∷
   rw 0 (q101 c4) ∷
   rw⁻ 2 (q102 c4) ∷
   rw 1 (q97 c4) ∷
   rw 2 (q103 c4) ∷ []) Eq.refl

private
  q104 : Ws → Eqn
  q104 c4 = wpE 197 c4
  q105 : Ws → Eqn
  q105 c4 = wpE 195 c4
  q106 : Ws → Eqn
  q106 c4 = sE 24 (lem-comm-SWAP14-BOX⟨2·03⟩ c4)

-- nat-SWbc @0210213443: 23 steps
lem-nat-SWbc-at0210213443 : Ws → ⟪ (ℓ "乘伮乘") ⟫ʷ ≈ ⟪ (ℓ "伱") ⟫ʷ
lem-nat-SWbc-at0210213443 c4 = derive (ℓ "乘伮乘") (ℓ "伱")
  (re 1 1 (ℓ "二亏仜亏二仜") ∷
   rw⁻ 0 (q1 c4) ∷
   rw 1 (q104 c4) ∷
   re 3 1 (ℓ "亜亝仈亝亜仈") ∷
   rw⁻ 2 (q3 c4) ∷
   rw 3 (q105 c4) ∷
   rw 4 (q106 c4) ∷
   rw 5 (q105 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   rw 7 (q106 c4) ∷
   rw 8 (q104 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   re 11 1 (ℓ "亜亝仈亝亜仈") ∷
   rw⁻ 10 (q3 c4) ∷
   rw 11 (q105 c4) ∷
   rw 12 (q106 c4) ∷
   rw 13 (q105 c4) ∷
   rw⁻ 14 (q3 c4) ∷
   rw 15 (q106 c4) ∷
   rw 16 (q6 c4) ∷
   re 2 6 (ℓ "仉") ∷
   re 5 6 (ℓ "仉") ∷
   re 0 6 (ℓ "伱") ∷ []) Eq.refl

private
  q107 : Ws → Eqn
  q107 c4 = wlE 297 (lit c4)
  q108 : Ws → Eqn
  q108 c4 = wpE 92 c4
  q109 : Ws → Eqn
  q109 c4 = sE 8 (lem-comm-CX31-CCZ024 c4)
  q110 : Ws → Eqn
  q110 c4 = wpE 87 c4
  q111 : Ws → Eqn
  q111 c4 = wpE 81 c4

-- cQ @02132130: 7 steps
lem-cQ-at02132130 : Ws → ⟪ (ℓ "交亜") ⟫ʷ ≈ ⟪ (ℓ "亜交") ⟫ʷ
lem-cQ-at02132130 c4 = derive (ℓ "交亜") (ℓ "亜交")
  (rw 0 (q107 c4) ∷
   rw⁻ 4 (q108 c4) ∷
   rw 3 (q109 c4) ∷
   rw⁻ 2 (q110 c4) ∷
   rw 1 (q109 c4) ∷
   rw⁻ 0 (q111 c4) ∷
   rw⁻ 1 (q107 c4) ∷ []) Eq.refl

private
  q112 : Ws → Eqn
  q112 c4 = wlE 757 (lit c4)
  q113 : Ws → Eqn
  q113 c4 = wlE 639 (lit c4)
  q114 : Ws → Eqn
  q114 c4 = sE 19 (lem-comm-CX30-CCZ124 c4)
  q115 : Ws → Eqn
  q115 c4 = wpE 679 c4
  q116 : Ws → Eqn
  q116 c4 = wpE 515 c4

-- cQ @02132031: 7 steps
lem-cQ-at02132031 : Ws → ⟪ (ℓ "亘亨") ⟫ʷ ≈ ⟪ (ℓ "亨亘") ⟫ʷ
lem-cQ-at02132031 c4 = derive (ℓ "亘亨") (ℓ "亨亘")
  (rw 0 (q112 c4) ∷
   rw⁻ 4 (q113 c4) ∷
   rw 3 (q114 c4) ∷
   rw⁻ 2 (q115 c4) ∷
   rw 1 (q114 c4) ∷
   rw⁻ 0 (q116 c4) ∷
   rw⁻ 1 (q112 c4) ∷ []) Eq.refl

private
  q117 : Ws → Eqn
  q117 c4 = wlE 434 (lit c4)
  q118 : Ws → Eqn
  q118 c4 = wlE 435 (lit c4)
  q119 : Ws → Eqn
  q119 c4 = wlE 436 (lit c4)

-- tP @0310213442: 7 steps
lem-tP-at0310213442 : Ws → ⟪ (ℓ "亓亲") ⟫ʷ ≈ ⟪ (ℓ "亲亓") ⟫ʷ
lem-tP-at0310213442 c4 = derive (ℓ "亓亲") (ℓ "亲亓")
  (rw⁻ 0 (q117 c4) ∷
   rw⁻ 3 (q118 c4) ∷
   rw 2 (q119 c4) ∷
   rw 1 (q52 c4) ∷
   rw⁻ 2 (q119 c4) ∷
   rw 0 (q118 c4) ∷
   rw 1 (q117 c4) ∷ []) Eq.refl

private
  q120 : Ws → Eqn
  q120 c4 = sE 56 (lem-cQ-at0213243041 c4)

-- tP @0213243041: 7 steps
lem-tP-at0213243041 : Ws → ⟪ (ℓ "亱亏") ⟫ʷ ≈ ⟪ (ℓ "亏亱") ⟫ʷ
lem-tP-at0213243041 c4 = derive (ℓ "亱亏") (ℓ "亏亱")
  (rw⁻ 0 (q94 c4) ∷
   rw⁻ 3 (q95 c4) ∷
   rw 2 (q96 c4) ∷
   rw 1 (q120 c4) ∷
   rw⁻ 2 (q96 c4) ∷
   rw 0 (q95 c4) ∷
   rw 1 (q94 c4) ∷ []) Eq.refl

private
  q121 : Ws → Eqn
  q121 c4 = wlE 288 (lit c4)

-- box-tQ @0213243041: 13 steps
lem-box-tQ-at0213243041 : Ws → ⟪ (ℓ "佋") ⟫ʷ ≈ ⟪ (ℓ "亱二亱二") ⟫ʷ
lem-box-tQ-at0213243041 c4 = derive (ℓ "佋") (ℓ "亱二亱二")
  (re 0 1 (ℓ "亰亱佊亱亰佊") ∷
   re 2 1 (ℓ "亘些伿些亘伿") ∷
   re 4 1 (ℓ "乐") ∷
   re 7 1 (ℓ "乐") ∷
   rw⁻ 2 (q121 c4) ∷
   re 5 1 (ℓ "亘些伿些亘伿") ∷
   re 7 1 (ℓ "乐") ∷
   re 10 1 (ℓ "乐") ∷
   rw⁻ 5 (q121 c4) ∷
   rw 0 (q101 c4) ∷
   rw⁻ 2 (q102 c4) ∷
   rw 1 (q120 c4) ∷
   rw 2 (q103 c4) ∷ []) Eq.refl

private
  q122 : Ws → Eqn
  q122 c4 = wpE 280 c4
  q123 : Ws → Eqn
  q123 c4 = wlE 930 (lit c4)
  q124 : Ws → Eqn
  q124 c4 = sE 29 (lem-cQ-at021021 c4)
  q125 : Ws → Eqn
  q125 c4 = wlE 931 (lit c4)

-- box-tQ @021021: 13 steps
lem-box-tQ-at021021 : Ws → ⟪ (ℓ "伭") ⟫ʷ ≈ ⟪ (ℓ "亏亰亏亰") ⟫ʷ
lem-box-tQ-at021021 c4 = derive (ℓ "伭") (ℓ "亏亰亏亰")
  (re 0 1 (ℓ "二亏他亏二他") ∷
   re 2 1 (ℓ "亘亙仍亙亘仍") ∷
   re 4 1 (ℓ "丿") ∷
   re 7 1 (ℓ "丿") ∷
   rw 2 (q122 c4) ∷
   re 5 1 (ℓ "亘亙仍亙亘仍") ∷
   re 7 1 (ℓ "丿") ∷
   re 10 1 (ℓ "丿") ∷
   rw 5 (q122 c4) ∷
   rw 0 (q123 c4) ∷
   rw 2 (q51 c4) ∷
   rw 1 (q124 c4) ∷
   rw 2 (q125 c4) ∷ []) Eq.refl

private
  q126 : Ws → Eqn
  q126 c4 = wlE 326 (lit c4)
  q127 : Ws → Eqn
  q127 c4 = wpE 314 c4
  q128 : Ws → Eqn
  q128 c4 = sE 5 (lem-comm-CX21-CCZ034 c4)
  q129 : Ws → Eqn
  q129 c4 = wpE 734 c4
  q130 : Ws → Eqn
  q130 c4 = wpE 312 c4

-- cQ @03122130: 7 steps
lem-cQ-at03122130 : Ws → ⟪ (ℓ "交亠") ⟫ʷ ≈ ⟪ (ℓ "亠交") ⟫ʷ
lem-cQ-at03122130 c4 = derive (ℓ "交亠") (ℓ "亠交")
  (rw 0 (q126 c4) ∷
   rw⁻ 4 (q127 c4) ∷
   rw 3 (q128 c4) ∷
   rw⁻ 2 (q129 c4) ∷
   rw 1 (q128 c4) ∷
   rw⁻ 0 (q130 c4) ∷
   rw⁻ 1 (q126 c4) ∷ []) Eq.refl

private
  q131 : Ws → Eqn
  q131 c4 = sE 55 (lem-sym-ab-at1221 c4)

-- box-perm-2134 @1221: 1 steps
lem-box-perm-2134-at1221 : Ws → ⟪ (ℓ "仌") ⟫ʷ ≈ ⟪ (ℓ "亹") ⟫ʷ
lem-box-perm-2134-at1221 c4 = derive (ℓ "仌") (ℓ "亹")
  (rw 0 (q131 c4) ∷ []) Eq.refl

private
  q132 : Ws → Eqn
  q132 c4 = sE 59 (lem-sym-ab-at021021 c4)

-- box-perm-2134 @021021: 1 steps
lem-box-perm-2134-at021021 : Ws → ⟪ (ℓ "伭") ⟫ʷ ≈ ⟪ (ℓ "伳") ⟫ʷ
lem-box-perm-2134-at021021 c4 = derive (ℓ "伭") (ℓ "伳")
  (rw 0 (q132 c4) ∷ []) Eq.refl

private
  q133 : Ws → Eqn
  q133 c4 = wlE 1379 (lit c4)
  q134 : Ws → Eqn
  q134 c4 = sE 61 (lem-cQ-at03203442 c4)

-- box-tQ @03203442: 13 steps
lem-box-tQ-at03203442 : Ws → ⟪ (ℓ "佫") ⟫ʷ ≈ ⟪ (ℓ "亓亰亓亰") ⟫ʷ
lem-box-tQ-at03203442 c4 = derive (ℓ "佫") (ℓ "亓亰亓亰")
  (re 0 1 (ℓ "亐亓伡亓亐伡") ∷
   re 2 1 (ℓ "京亭伙亭京伙") ∷
   re 4 1 (ℓ "义") ∷
   re 7 1 (ℓ "义") ∷
   rw 2 (q133 c4) ∷
   re 5 1 (ℓ "京亭伙亭京伙") ∷
   re 7 1 (ℓ "义") ∷
   re 10 1 (ℓ "义") ∷
   rw 5 (q133 c4) ∷
   rw 0 (q50 c4) ∷
   rw 2 (q51 c4) ∷
   rw 1 (q134 c4) ∷
   rw 2 (q53 c4) ∷ []) Eq.refl

private
  q135 : Ws → Eqn
  q135 c4 = sE 60 (lem-sym-ab-at0220 c4)

-- box-perm-2134 @0220: 1 steps
lem-box-perm-2134-at0220 : Ws → ⟪ (ℓ "伳") ⟫ʷ ≈ ⟪ (ℓ "伭") ⟫ʷ
lem-box-perm-2134-at0220 c4 = derive (ℓ "伳") (ℓ "伭")
  (rw 0 (q135 c4) ∷ []) Eq.refl

private
  q136 : Ws → Eqn
  q136 c4 = wlE 283 (lit c4)
  q137 : Ws → Eqn
  q137 c4 = wlE 990 (lit c4)
  q138 : Ws → Eqn
  q138 c4 = wlE 285 (lit c4)
  q139 : Ws → Eqn
  q139 c4 = wlE 989 (lit c4)
  q140 : Ws → Eqn
  q140 c4 = sE 49 (lem-comm-SWAP13-BOX⟨2·04⟩ c4)
  q141 : Ws → Eqn
  q141 c4 = wlE 287 (lit c4)

-- nat-SWbc @021021: 23 steps
lem-nat-SWbc-at021021 : Ws → ⟪ (ℓ "乑伭乑") ⟫ʷ ≈ ⟪ (ℓ "伯") ⟫ʷ
lem-nat-SWbc-at021021 c4 = derive (ℓ "乑伭乑") (ℓ "伯")
  (re 1 1 (ℓ "二亏他亏二他") ∷
   rw⁻ 0 (q136 c4) ∷
   rw 1 (q137 c4) ∷
   re 3 1 (ℓ "亘亙仍亙亘仍") ∷
   rw⁻ 2 (q138 c4) ∷
   rw 3 (q139 c4) ∷
   rw 4 (q140 c4) ∷
   rw 5 (q139 c4) ∷
   rw⁻ 6 (q138 c4) ∷
   rw 7 (q140 c4) ∷
   rw 8 (q137 c4) ∷
   rw⁻ 9 (q136 c4) ∷
   re 11 1 (ℓ "亘亙仍亙亘仍") ∷
   rw⁻ 10 (q138 c4) ∷
   rw 11 (q139 c4) ∷
   rw 12 (q140 c4) ∷
   rw 13 (q139 c4) ∷
   rw⁻ 14 (q138 c4) ∷
   rw 15 (q140 c4) ∷
   rw 16 (q141 c4) ∷
   re 2 6 (ℓ "从") ∷
   re 5 6 (ℓ "从") ∷
   re 0 6 (ℓ "伯") ∷ []) Eq.refl

private
  q142 : Ws → Eqn
  q142 c4 = wlE 637 (lit c4)
  q143 : Ws → Eqn
  q143 c4 = sE 18 (lem-comm-CX03-CCZ124 c4)
  q144 : Ws → Eqn
  q144 c4 = wlE 638 (lit c4)

-- cQ @02102331: 7 steps
lem-cQ-at02102331 : Ws → ⟪ (ℓ "亘亨") ⟫ʷ ≈ ⟪ (ℓ "亨亘") ⟫ʷ
lem-cQ-at02102331 c4 = derive (ℓ "亘亨") (ℓ "亨亘")
  (rw 0 (q142 c4) ∷
   rw⁻ 4 (q116 c4) ∷
   rw 3 (q143 c4) ∷
   rw⁻ 2 (q144 c4) ∷
   rw 1 (q143 c4) ∷
   rw⁻ 0 (q113 c4) ∷
   rw⁻ 1 (q142 c4) ∷ []) Eq.refl

-- cQ @03243042: 7 steps
lem-cQ-at03243042 : Ws → ⟪ (ℓ "京亘") ⟫ʷ ≈ ⟪ (ℓ "亘京") ⟫ʷ
lem-cQ-at03243042 c4 = derive (ℓ "京亘") (ℓ "亘京")
  (rw 0 (q29 c4) ∷
   rw⁻ 4 (q28 c4) ∷
   rw 3 (q30 c4) ∷
   rw⁻ 2 (q31 c4) ∷
   rw 1 (q30 c4) ∷
   rw⁻ 0 (q25 c4) ∷
   rw⁻ 1 (q29 c4) ∷ []) Eq.refl

private
  q145 : Ws → Eqn
  q145 c4 = wpE 540 c4
  q146 : Ws → Eqn
  q146 c4 = wpE 48 c4
  q147 : Ws → Eqn
  q147 c4 = wlE 667 (lit c4)
  q148 : Ws → Eqn
  q148 c4 = wlE 199 (lit c4)

-- cQ @142142: 7 steps
lem-cQ-at142142 : Ws → ⟪ (ℓ "五亘") ⟫ʷ ≈ ⟪ (ℓ "亘五") ⟫ʷ
lem-cQ-at142142 c4 = derive (ℓ "五亘") (ℓ "亘五")
  (rw 0 (q145 c4) ∷
   rw⁻ 4 (q146 c4) ∷
   rw 3 (q26 c4) ∷
   rw⁻ 2 (q147 c4) ∷
   rw 1 (q26 c4) ∷
   rw⁻ 0 (q148 c4) ∷
   rw⁻ 1 (q145 c4) ∷ []) Eq.refl

private
  q149 : Ws → Eqn
  q149 c4 = wpE 208 c4
  q150 : Ws → Eqn
  q150 c4 = wpE 1237 c4
  q151 : Ws → Eqn
  q151 c4 = wpE 206 c4
  q152 : Ws → Eqn
  q152 c4 = wpE 1238 c4
  q153 : Ws → Eqn
  q153 c4 = sE 13 (lem-comm-SWAP13-BOX⟨0·42⟩ c4)

-- nat-SWbc @142142: 23 steps
lem-nat-SWbc-at142142 : Ws → ⟪ (ℓ "乑企乑") ⟫ʷ ≈ ⟪ (ℓ "伋") ⟫ʷ
lem-nat-SWbc-at142142 c4 = derive (ℓ "乑企乑") (ℓ "伋")
  (re 1 1 (ℓ "五井伀井五伀") ∷
   rw⁻ 0 (q149 c4) ∷
   rw 1 (q150 c4) ∷
   re 3 1 (ℓ "亠亣仿亣亠仿") ∷
   rw⁻ 2 (q151 c4) ∷
   rw 3 (q152 c4) ∷
   rw 4 (q153 c4) ∷
   rw 5 (q152 c4) ∷
   rw⁻ 6 (q151 c4) ∷
   rw 7 (q153 c4) ∷
   rw 8 (q150 c4) ∷
   rw⁻ 9 (q149 c4) ∷
   re 11 1 (ℓ "亠亣仿亣亠仿") ∷
   rw⁻ 10 (q151 c4) ∷
   rw 11 (q152 c4) ∷
   rw 12 (q153 c4) ∷
   rw 13 (q152 c4) ∷
   rw⁻ 14 (q151 c4) ∷
   rw 15 (q153 c4) ∷
   rw 16 (q141 c4) ∷
   re 2 6 (ℓ "伊") ∷
   re 5 6 (ℓ "伊") ∷
   re 0 6 (ℓ "伋") ∷ []) Eq.refl

private
  q154 : Ws → Eqn
  q154 c4 = sE 54 (lem-sym-ab-at032032 c4)

-- box-perm-2134 @032032: 1 steps
lem-box-perm-2134-at032032 : Ws → ⟪ (ℓ "佪") ⟫ʷ ≈ ⟪ (ℓ "佤") ⟫ʷ
lem-box-perm-2134-at032032 c4 = derive (ℓ "佪") (ℓ "佤")
  (rw 0 (q154 c4) ∷ []) Eq.refl

private
  q155 : Ws → Eqn
  q155 c4 = wlE 286 (lit c4)
  q156 : Ws → Eqn
  q156 c4 = wlE 284 (lit c4)

-- nat-SWbc @02102331: 23 steps
lem-nat-SWbc-at02102331 : Ws → ⟪ (ℓ "乑伯乑") ⟫ʷ ≈ ⟪ (ℓ "伭") ⟫ʷ
lem-nat-SWbc-at02102331 c4 = derive (ℓ "乑伯乑") (ℓ "伭")
  (re 1 1 (ℓ "亘亚从亚亘从") ∷
   rw⁻ 0 (q138 c4) ∷
   rw 1 (q155 c4) ∷
   re 3 1 (ℓ "二亍仍亍二仍") ∷
   rw⁻ 2 (q136 c4) ∷
   rw 3 (q156 c4) ∷
   rw 4 (q140 c4) ∷
   rw 5 (q156 c4) ∷
   rw⁻ 6 (q136 c4) ∷
   rw 7 (q140 c4) ∷
   rw 8 (q155 c4) ∷
   rw⁻ 9 (q138 c4) ∷
   re 11 1 (ℓ "二亍仍亍二仍") ∷
   rw⁻ 10 (q136 c4) ∷
   rw 11 (q156 c4) ∷
   rw 12 (q140 c4) ∷
   rw 13 (q156 c4) ∷
   rw⁻ 14 (q136 c4) ∷
   rw 15 (q140 c4) ∷
   rw 16 (q141 c4) ∷
   re 2 6 (ℓ "他") ∷
   re 5 6 (ℓ "他") ∷
   re 0 6 (ℓ "伭") ∷ []) Eq.refl

private
  q157 : Ws → Eqn
  q157 c4 = sE 53 (lem-sym-ab-at0210243143 c4)

-- box-perm-2134 @0210243143: 1 steps
lem-box-perm-2134-at0210243143 : Ws → ⟪ (ℓ "伱") ⟫ʷ ≈ ⟪ (ℓ "佔") ⟫ʷ
lem-box-perm-2134-at0210243143 c4 = derive (ℓ "伱") (ℓ "佔")
  (rw 0 (q157 c4) ∷ []) Eq.refl

private
  q158 : Ws → Eqn
  q158 c4 = wpE 450 c4
  q159 : Ws → Eqn
  q159 c4 = wlE 1220 (lit c4)
  q160 : Ws → Eqn
  q160 c4 = wpE 1206 c4
  q161 : Ws → Eqn
  q161 c4 = wpE 1003 c4

-- cQ @04122041: 7 steps
lem-cQ-at04122041 : Ws → ⟪ (ℓ "亜京") ⟫ʷ ≈ ⟪ (ℓ "京亜") ⟫ʷ
lem-cQ-at04122041 c4 = derive (ℓ "亜京") (ℓ "京亜")
  (rw 0 (q158 c4) ∷
   rw⁻ 4 (q159 c4) ∷
   rw 3 (q57 c4) ∷
   rw⁻ 2 (q160 c4) ∷
   rw 1 (q57 c4) ∷
   rw⁻ 0 (q161 c4) ∷
   rw⁻ 1 (q158 c4) ∷ []) Eq.refl

private
  q162 : Ws → Eqn
  q162 c4 = wpE 1155 c4
  q163 : Ws → Eqn
  q163 c4 = wpE 1181 c4
  q164 : Ws → Eqn
  q164 c4 = wpE 1157 c4
  q165 : Ws → Eqn
  q165 c4 = wpE 1180 c4
  q166 : Ws → Eqn
  q166 c4 = sE 46 (lem-comm-SWAP03-BOX⟨4·21⟩ c4)
  q167 : Ws → Eqn
  q167 c4 = wlE 928 (lit c4)

-- nat-SWbc @04122041: 23 steps
lem-nat-SWbc-at04122041 : Ws → ⟪ (ℓ "丹侗丹") ⟫ʷ ≈ ⟪ (ℓ "侚") ⟫ʷ
lem-nat-SWbc-at04122041 c4 = derive (ℓ "丹侗丹") (ℓ "侚")
  (re 1 1 (ℓ "亜亟佣亟亜佣") ∷
   rw⁻ 0 (q162 c4) ∷
   rw 1 (q163 c4) ∷
   re 3 1 (ℓ "亰亱佐亱亰佐") ∷
   rw⁻ 2 (q164 c4) ∷
   rw 3 (q165 c4) ∷
   rw 4 (q166 c4) ∷
   rw 5 (q165 c4) ∷
   rw⁻ 6 (q164 c4) ∷
   rw 7 (q166 c4) ∷
   rw 8 (q163 c4) ∷
   rw⁻ 9 (q162 c4) ∷
   re 11 1 (ℓ "亰亱佐亱亰佐") ∷
   rw⁻ 10 (q164 c4) ∷
   rw 11 (q165 c4) ∷
   rw 12 (q166 c4) ∷
   rw 13 (q165 c4) ∷
   rw⁻ 14 (q164 c4) ∷
   rw 15 (q166 c4) ∷
   rw 16 (q167 c4) ∷
   re 2 6 (ℓ "佑") ∷
   re 5 6 (ℓ "佑") ∷
   re 0 6 (ℓ "侚") ∷ []) Eq.refl

private
  q168 : Ws → Eqn
  q168 c4 = wlE 274 (lit c4)
  q169 : Ws → Eqn
  q169 c4 = wpE 62 c4
  q170 : Ws → Eqn
  q170 c4 = sE 6 (lem-comm-CX23-CCZ014 c4)
  q171 : Ws → Eqn
  q171 c4 = wpE 63 c4
  q172 : Ws → Eqn
  q172 c4 = wpE 64 c4

-- cQ @0412233041: 7 steps
lem-cQ-at0412233041 : Ws → ⟪ (ℓ "亰五") ⟫ʷ ≈ ⟪ (ℓ "五亰") ⟫ʷ
lem-cQ-at0412233041 c4 = derive (ℓ "亰五") (ℓ "五亰")
  (rw 0 (q168 c4) ∷
   rw⁻ 4 (q169 c4) ∷
   rw 3 (q170 c4) ∷
   rw⁻ 2 (q171 c4) ∷
   rw 1 (q170 c4) ∷
   rw⁻ 0 (q172 c4) ∷
   rw⁻ 1 (q168 c4) ∷ []) Eq.refl

private
  q173 : Ws → Eqn
  q173 c4 = wpE 551 c4
  q174 : Ws → Eqn
  q174 c4 = wpE 973 c4
  q175 : Ws → Eqn
  q175 c4 = wpE 553 c4
  q176 : Ws → Eqn
  q176 c4 = wpE 972 c4
  q177 : Ws → Eqn
  q177 c4 = sE 48 (lem-comm-SWAP12-BOX⟨4·03⟩ c4)

-- nat-SWbc @0410213243: 23 steps
lem-nat-SWbc-at0410213243 : Ws → ⟪ (ℓ "乊侍乊") ⟫ʷ ≈ ⟪ (ℓ "侎") ⟫ʷ
lem-nat-SWbc-at0410213243 c4 = derive (ℓ "乊侍乊") (ℓ "侎")
  (re 1 1 (ℓ "五亗伆亗五伆") ∷
   rw⁻ 0 (q173 c4) ∷
   rw 1 (q174 c4) ∷
   re 3 1 (ℓ "亜亝份亝亜份") ∷
   rw⁻ 2 (q175 c4) ∷
   rw 3 (q176 c4) ∷
   rw 4 (q177 c4) ∷
   rw 5 (q176 c4) ∷
   rw⁻ 6 (q175 c4) ∷
   rw 7 (q177 c4) ∷
   rw 8 (q174 c4) ∷
   rw⁻ 9 (q173 c4) ∷
   re 11 1 (ℓ "亜亝份亝亜份") ∷
   rw⁻ 10 (q175 c4) ∷
   rw 11 (q176 c4) ∷
   rw 12 (q177 c4) ∷
   rw 13 (q176 c4) ∷
   rw⁻ 14 (q175 c4) ∷
   rw 15 (q177 c4) ∷
   rw 16 (q23 c4) ∷
   re 2 6 (ℓ "仾") ∷
   re 5 6 (ℓ "仾") ∷
   re 0 6 (ℓ "侎") ∷ []) Eq.refl

private
  q178 : Ws → Eqn
  q178 c4 = wpE 296 c4
  q179 : Ws → Eqn
  q179 c4 = wlE 1221 (lit c4)

-- cQ @04103143: 7 steps
lem-cQ-at04103143 : Ws → ⟪ (ℓ "亜京") ⟫ʷ ≈ ⟪ (ℓ "京亜") ⟫ʷ
lem-cQ-at04103143 c4 = derive (ℓ "亜京") (ℓ "京亜")
  (rw 0 (q178 c4) ∷
   rw⁻ 4 (q161 c4) ∷
   rw 3 (q36 c4) ∷
   rw⁻ 2 (q179 c4) ∷
   rw 1 (q36 c4) ∷
   rw⁻ 0 (q159 c4) ∷
   rw⁻ 1 (q178 c4) ∷ []) Eq.refl

private
  q180 : Ws → Eqn
  q180 c4 = wlE 166 (lit c4)
  q181 : Ws → Eqn
  q181 c4 = wpE 34 c4
  q182 : Ws → Eqn
  q182 c4 = sE 3 (lem-comm-CX13-CCZ024 c4)
  q183 : Ws → Eqn
  q183 c4 = wpE 35 c4
  q184 : Ws → Eqn
  q184 c4 = wpE 36 c4

-- cQ @04233042: 7 steps
lem-cQ-at04233042 : Ws → ⟪ (ℓ "京亜") ⟫ʷ ≈ ⟪ (ℓ "亜京") ⟫ʷ
lem-cQ-at04233042 c4 = derive (ℓ "京亜") (ℓ "亜京")
  (rw 0 (q180 c4) ∷
   rw⁻ 4 (q181 c4) ∷
   rw 3 (q182 c4) ∷
   rw⁻ 2 (q183 c4) ∷
   rw 1 (q182 c4) ∷
   rw⁻ 0 (q184 c4) ∷
   rw⁻ 1 (q180 c4) ∷ []) Eq.refl

private
  q185 : Ws → Eqn
  q185 c4 = wpE 1158 c4
  q186 : Ws → Eqn
  q186 c4 = wpE 1156 c4

-- nat-SWbc @0412233041: 23 steps
lem-nat-SWbc-at0412233041 : Ws → ⟪ (ℓ "丹侚丹") ⟫ʷ ≈ ⟪ (ℓ "侗") ⟫ʷ
lem-nat-SWbc-at0412233041 c4 = derive (ℓ "丹侚丹") (ℓ "侗")
  (re 1 1 (ℓ "亰亳佑亳亰佑") ∷
   rw⁻ 0 (q164 c4) ∷
   rw 1 (q185 c4) ∷
   re 3 1 (ℓ "亜亞佐亞亜佐") ∷
   rw⁻ 2 (q162 c4) ∷
   rw 3 (q186 c4) ∷
   rw 4 (q166 c4) ∷
   rw 5 (q186 c4) ∷
   rw⁻ 6 (q162 c4) ∷
   rw 7 (q166 c4) ∷
   rw 8 (q185 c4) ∷
   rw⁻ 9 (q164 c4) ∷
   re 11 1 (ℓ "亜亞佐亞亜佐") ∷
   rw⁻ 10 (q162 c4) ∷
   rw 11 (q186 c4) ∷
   rw 12 (q166 c4) ∷
   rw 13 (q186 c4) ∷
   rw⁻ 14 (q162 c4) ∷
   rw 15 (q166 c4) ∷
   rw 16 (q167 c4) ∷
   re 2 6 (ℓ "佣") ∷
   re 5 6 (ℓ "佣") ∷
   re 0 6 (ℓ "侗") ∷ []) Eq.refl

-- cQ @041041: 7 steps
lem-cQ-at041041 : Ws → ⟪ (ℓ "亜京") ⟫ʷ ≈ ⟪ (ℓ "京亜") ⟫ʷ
lem-cQ-at041041 c4 = derive (ℓ "亜京") (ℓ "京亜")
  (rw 0 (q178 c4) ∷
   rw⁻ 4 (q161 c4) ∷
   rw 3 (q36 c4) ∷
   rw⁻ 2 (q179 c4) ∷
   rw 1 (q36 c4) ∷
   rw⁻ 0 (q159 c4) ∷
   rw⁻ 1 (q178 c4) ∷ []) Eq.refl

private
  q187 : Ws → Eqn
  q187 c4 = wpE 231 c4
  q188 : Ws → Eqn
  q188 c4 = wpE 384 c4
  q189 : Ws → Eqn
  q189 c4 = wlE 1399 (lit c4)
  q190 : Ws → Eqn
  q190 c4 = wlE 471 (lit c4)

-- cQ @0410233241: 7 steps
lem-cQ-at0410233241 : Ws → ⟪ (ℓ "亠亨") ⟫ʷ ≈ ⟪ (ℓ "亨亠") ⟫ʷ
lem-cQ-at0410233241 c4 = derive (ℓ "亠亨") (ℓ "亨亠")
  (rw 0 (q187 c4) ∷
   rw⁻ 4 (q188 c4) ∷
   rw 3 (q143 c4) ∷
   rw⁻ 2 (q189 c4) ∷
   rw 1 (q143 c4) ∷
   rw⁻ 0 (q190 c4) ∷
   rw⁻ 1 (q187 c4) ∷ []) Eq.refl

private
  q191 : Ws → Eqn
  q191 c4 = wlE 271 (lit c4)
  q192 : Ws → Eqn
  q192 c4 = wpE 108 c4
  q193 : Ws → Eqn
  q193 c4 = wpE 123 c4
  q194 : Ws → Eqn
  q194 c4 = wpE 106 c4

-- cQ @0412213043: 7 steps
lem-cQ-at0412213043 : Ws → ⟪ (ℓ "亨亠") ⟫ʷ ≈ ⟪ (ℓ "亠亨") ⟫ʷ
lem-cQ-at0412213043 c4 = derive (ℓ "亨亠") (ℓ "亠亨")
  (rw 0 (q191 c4) ∷
   rw⁻ 4 (q192 c4) ∷
   rw 3 (q128 c4) ∷
   rw⁻ 2 (q193 c4) ∷
   rw 1 (q128 c4) ∷
   rw⁻ 0 (q194 c4) ∷
   rw⁻ 1 (q191 c4) ∷ []) Eq.refl

private
  q195 : Ws → Eqn
  q195 c4 = wlE 831 (lit c4)
  q196 : Ws → Eqn
  q196 c4 = wpE 746 c4

-- cQ @0413213240: 7 steps
lem-cQ-at0413213240 : Ws → ⟪ (ℓ "京亜") ⟫ʷ ≈ ⟪ (ℓ "亜京") ⟫ʷ
lem-cQ-at0413213240 c4 = derive (ℓ "京亜") (ℓ "亜京")
  (rw 0 (q195 c4) ∷
   rw⁻ 4 (q184 c4) ∷
   rw 3 (q109 c4) ∷
   rw⁻ 2 (q196 c4) ∷
   rw 1 (q109 c4) ∷
   rw⁻ 0 (q181 c4) ∷
   rw⁻ 1 (q195 c4) ∷ []) Eq.refl

-- cQ @04233240: 7 steps
lem-cQ-at04233240 : Ws → ⟪ (ℓ "京亜") ⟫ʷ ≈ ⟪ (ℓ "亜京") ⟫ʷ
lem-cQ-at04233240 c4 = derive (ℓ "京亜") (ℓ "亜京")
  (rw 0 (q180 c4) ∷
   rw⁻ 4 (q181 c4) ∷
   rw 3 (q182 c4) ∷
   rw⁻ 2 (q183 c4) ∷
   rw 1 (q182 c4) ∷
   rw⁻ 0 (q184 c4) ∷
   rw⁻ 1 (q180 c4) ∷ []) Eq.refl

private
  q197 : Ws → Eqn
  q197 c4 = wlE 256 (lit c4)
  q198 : Ws → Eqn
  q198 c4 = sE 2 (lem-comm-CX12-CCZ034 c4)
  q199 : Ws → Eqn
  q199 c4 = wpE 107 c4

-- cQ @0440: 7 steps
lem-cQ-at0440 : Ws → ⟪ (ℓ "亨亠") ⟫ʷ ≈ ⟪ (ℓ "亠亨") ⟫ʷ
lem-cQ-at0440 c4 = derive (ℓ "亨亠") (ℓ "亠亨")
  (rw 0 (q197 c4) ∷
   rw⁻ 4 (q194 c4) ∷
   rw 3 (q198 c4) ∷
   rw⁻ 2 (q199 c4) ∷
   rw 1 (q198 c4) ∷
   rw⁻ 0 (q192 c4) ∷
   rw⁻ 1 (q197 c4) ∷ []) Eq.refl

private
  q200 : Ws → Eqn
  q200 c4 = wpE 1193 c4
  q201 : Ws → Eqn
  q201 c4 = wpE 318 c4

-- cQ @0413203142: 7 steps
lem-cQ-at0413203142 : Ws → ⟪ (ℓ "亠亨") ⟫ʷ ≈ ⟪ (ℓ "亨亠") ⟫ʷ
lem-cQ-at0413203142 c4 = derive (ℓ "亠亨") (ℓ "亨亠")
  (rw 0 (q200 c4) ∷
   rw⁻ 4 (q190 c4) ∷
   rw 3 (q114 c4) ∷
   rw⁻ 2 (q201 c4) ∷
   rw 1 (q114 c4) ∷
   rw⁻ 0 (q188 c4) ∷
   rw⁻ 1 (q200 c4) ∷ []) Eq.refl

private
  q202 : Ws → Eqn
  q202 c4 = wlE 334 (lit c4)
  q203 : Ws → Eqn
  q203 c4 = wpE 513 c4
  q204 : Ws → Eqn
  q204 c4 = wlE 620 (lit c4)
  q205 : Ws → Eqn
  q205 c4 = wlE 621 (lit c4)

-- cQ @02142140: 7 steps
lem-cQ-at02142140 : Ws → ⟪ (ℓ "亨亘") ⟫ʷ ≈ ⟪ (ℓ "亘亨") ⟫ʷ
lem-cQ-at02142140 c4 = derive (ℓ "亨亘") (ℓ "亘亨")
  (rw 0 (q202 c4) ∷
   rw⁻ 4 (q203 c4) ∷
   rw 3 (q26 c4) ∷
   rw⁻ 2 (q204 c4) ∷
   rw 1 (q26 c4) ∷
   rw⁻ 0 (q205 c4) ∷
   rw⁻ 1 (q202 c4) ∷ []) Eq.refl

-- cQ @0413213042: 7 steps
lem-cQ-at0413213042 : Ws → ⟪ (ℓ "京亜") ⟫ʷ ≈ ⟪ (ℓ "亜京") ⟫ʷ
lem-cQ-at0413213042 c4 = derive (ℓ "京亜") (ℓ "亜京")
  (rw 0 (q195 c4) ∷
   rw⁻ 4 (q184 c4) ∷
   rw 3 (q109 c4) ∷
   rw⁻ 2 (q196 c4) ∷
   rw 1 (q109 c4) ∷
   rw⁻ 0 (q181 c4) ∷
   rw⁻ 1 (q195 c4) ∷ []) Eq.refl

-- cQ @0412233140: 7 steps
lem-cQ-at0412233140 : Ws → ⟪ (ℓ "亰五") ⟫ʷ ≈ ⟪ (ℓ "五亰") ⟫ʷ
lem-cQ-at0412233140 c4 = derive (ℓ "亰五") (ℓ "五亰")
  (rw 0 (q168 c4) ∷
   rw⁻ 4 (q169 c4) ∷
   rw 3 (q170 c4) ∷
   rw⁻ 2 (q171 c4) ∷
   rw 1 (q170 c4) ∷
   rw⁻ 0 (q172 c4) ∷
   rw⁻ 1 (q168 c4) ∷ []) Eq.refl

private
  q206 : Ws → Eqn
  q206 c4 = wlE 1669 (lit c4)
  q207 : Ws → Eqn
  q207 c4 = wlE 1670 (lit c4)
  q208 : Ws → Eqn
  q208 c4 = wlE 1671 (lit c4)
  q209 : Ws → Eqn
  q209 c4 = wlE 1672 (lit c4)
  q210 : Ws → Eqn
  q210 c4 = sE 52 (lem-comm-SWAP13-BOX⟨4·20⟩ c4)

-- nat-SWbc @0412233140: 23 steps
lem-nat-SWbc-at0412233140 : Ws → ⟪ (ℓ "乑供乑") ⟫ʷ ≈ ⟪ (ℓ "侙") ⟫ʷ
lem-nat-SWbc-at0412233140 c4 = derive (ℓ "乑供乑") (ℓ "侙")
  (re 1 1 (ℓ "亰亳佛亳亰佛") ∷
   rw⁻ 0 (q206 c4) ∷
   rw 1 (q207 c4) ∷
   re 3 1 (ℓ "亨亪佚亪亨佚") ∷
   rw⁻ 2 (q208 c4) ∷
   rw 3 (q209 c4) ∷
   rw 4 (q210 c4) ∷
   rw 5 (q209 c4) ∷
   rw⁻ 6 (q208 c4) ∷
   rw 7 (q210 c4) ∷
   rw 8 (q207 c4) ∷
   rw⁻ 9 (q206 c4) ∷
   re 11 1 (ℓ "亨亪佚亪亨佚") ∷
   rw⁻ 10 (q208 c4) ∷
   rw 11 (q209 c4) ∷
   rw 12 (q210 c4) ∷
   rw 13 (q209 c4) ∷
   rw⁻ 14 (q208 c4) ∷
   rw 15 (q210 c4) ∷
   rw 16 (q141 c4) ∷
   re 2 6 (ℓ "你") ∷
   re 5 6 (ℓ "你") ∷
   re 0 6 (ℓ "侙") ∷ []) Eq.refl

-- cQ @0410233142: 7 steps
lem-cQ-at0410233142 : Ws → ⟪ (ℓ "亠亨") ⟫ʷ ≈ ⟪ (ℓ "亨亠") ⟫ʷ
lem-cQ-at0410233142 c4 = derive (ℓ "亠亨") (ℓ "亨亠")
  (rw 0 (q187 c4) ∷
   rw⁻ 4 (q188 c4) ∷
   rw 3 (q143 c4) ∷
   rw⁻ 2 (q189 c4) ∷
   rw 1 (q143 c4) ∷
   rw⁻ 0 (q190 c4) ∷
   rw⁻ 1 (q187 c4) ∷ []) Eq.refl

-- cQ @04122140: 7 steps
lem-cQ-at04122140 : Ws → ⟪ (ℓ "亨亠") ⟫ʷ ≈ ⟪ (ℓ "亠亨") ⟫ʷ
lem-cQ-at04122140 c4 = derive (ℓ "亨亠") (ℓ "亠亨")
  (rw 0 (q191 c4) ∷
   rw⁻ 4 (q192 c4) ∷
   rw 3 (q128 c4) ∷
   rw⁻ 2 (q193 c4) ∷
   rw 1 (q128 c4) ∷
   rw⁻ 0 (q194 c4) ∷
   rw⁻ 1 (q191 c4) ∷ []) Eq.refl

private
  q211 : Ws → Eqn
  q211 c4 = wlE 1680 (lit c4)
  q212 : Ws → Eqn
  q212 c4 = wlE 1681 (lit c4)

-- nat-SWbc @04122140: 23 steps
lem-nat-SWbc-at04122140 : Ws → ⟪ (ℓ "乑侙乑") ⟫ʷ ≈ ⟪ (ℓ "供") ⟫ʷ
lem-nat-SWbc-at04122140 c4 = derive (ℓ "乑侙乑") (ℓ "供")
  (re 1 1 (ℓ "亨享你享亨你") ∷
   rw⁻ 0 (q208 c4) ∷
   rw 1 (q211 c4) ∷
   re 3 1 (ℓ "亰亱佚亱亰佚") ∷
   rw⁻ 2 (q206 c4) ∷
   rw 3 (q212 c4) ∷
   rw 4 (q210 c4) ∷
   rw 5 (q212 c4) ∷
   rw⁻ 6 (q206 c4) ∷
   rw 7 (q210 c4) ∷
   rw 8 (q211 c4) ∷
   rw⁻ 9 (q208 c4) ∷
   re 11 1 (ℓ "亰亱佚亱亰佚") ∷
   rw⁻ 10 (q206 c4) ∷
   rw 11 (q212 c4) ∷
   rw 12 (q210 c4) ∷
   rw 13 (q212 c4) ∷
   rw⁻ 14 (q206 c4) ∷
   rw 15 (q210 c4) ∷
   rw 16 (q141 c4) ∷
   re 2 6 (ℓ "佛") ∷
   re 5 6 (ℓ "佛") ∷
   re 0 6 (ℓ "供") ∷ []) Eq.refl

-- cQ @0413203241: 7 steps
lem-cQ-at0413203241 : Ws → ⟪ (ℓ "亠亨") ⟫ʷ ≈ ⟪ (ℓ "亨亠") ⟫ʷ
lem-cQ-at0413203241 c4 = derive (ℓ "亠亨") (ℓ "亨亠")
  (rw 0 (q200 c4) ∷
   rw⁻ 4 (q190 c4) ∷
   rw 3 (q114 c4) ∷
   rw⁻ 2 (q201 c4) ∷
   rw 1 (q114 c4) ∷
   rw⁻ 0 (q188 c4) ∷
   rw⁻ 1 (q200 c4) ∷ []) Eq.refl

private
  q213 : Ws → Eqn
  q213 c4 = wlE 829 (lit c4)
  q214 : Ws → Eqn
  q214 c4 = sE 9 (lem-comm-CX32-CCZ014 c4)
  q215 : Ws → Eqn
  q215 c4 = wpE 722 c4

-- cQ @04133140: 7 steps
lem-cQ-at04133140 : Ws → ⟪ (ℓ "亰五") ⟫ʷ ≈ ⟪ (ℓ "五亰") ⟫ʷ
lem-cQ-at04133140 c4 = derive (ℓ "亰五") (ℓ "五亰")
  (rw 0 (q213 c4) ∷
   rw⁻ 4 (q172 c4) ∷
   rw 3 (q214 c4) ∷
   rw⁻ 2 (q215 c4) ∷
   rw 1 (q214 c4) ∷
   rw⁻ 0 (q169 c4) ∷
   rw⁻ 1 (q213 c4) ∷ []) Eq.refl

private
  q216 : Ws → Eqn
  q216 c4 = sE 51 (lem-comm-SWAP12-BOX⟨4·30⟩ c4)

-- nat-SWbc @04133140: 23 steps
lem-nat-SWbc-at04133140 : Ws → ⟪ (ℓ "乊侠乊") ⟫ʷ ≈ ⟪ (ℓ "侟") ⟫ʷ
lem-nat-SWbc-at04133140 c4 = derive (ℓ "乊侠乊") (ℓ "侟")
  (re 1 1 (ℓ "亰亳侀亳亰侀") ∷
   rw⁻ 0 (q18 c4) ∷
   rw 1 (q33 c4) ∷
   re 3 1 (ℓ "京亮使亮京使") ∷
   rw⁻ 2 (q20 c4) ∷
   rw 3 (q32 c4) ∷
   rw 4 (q216 c4) ∷
   rw 5 (q32 c4) ∷
   rw⁻ 6 (q20 c4) ∷
   rw 7 (q216 c4) ∷
   rw 8 (q33 c4) ∷
   rw⁻ 9 (q18 c4) ∷
   re 11 1 (ℓ "京亮使亮京使") ∷
   rw⁻ 10 (q20 c4) ∷
   rw 11 (q32 c4) ∷
   rw 12 (q216 c4) ∷
   rw 13 (q32 c4) ∷
   rw⁻ 14 (q20 c4) ∷
   rw 15 (q216 c4) ∷
   rw 16 (q23 c4) ∷
   re 2 6 (ℓ "來") ∷
   re 5 6 (ℓ "來") ∷
   re 0 6 (ℓ "侟") ∷ []) Eq.refl

-- nat-SWbc @0413213240: 23 steps
lem-nat-SWbc-at0413213240 : Ws → ⟪ (ℓ "乊侟乊") ⟫ʷ ≈ ⟪ (ℓ "侠") ⟫ʷ
lem-nat-SWbc-at0413213240 c4 = derive (ℓ "乊侟乊") (ℓ "侠")
  (re 1 1 (ℓ "京亯來亯京來") ∷
   rw⁻ 0 (q20 c4) ∷
   rw 1 (q21 c4) ∷
   re 3 1 (ℓ "亰亲使亲亰使") ∷
   rw⁻ 2 (q18 c4) ∷
   rw 3 (q19 c4) ∷
   rw 4 (q216 c4) ∷
   rw 5 (q19 c4) ∷
   rw⁻ 6 (q18 c4) ∷
   rw 7 (q216 c4) ∷
   rw 8 (q21 c4) ∷
   rw⁻ 9 (q20 c4) ∷
   re 11 1 (ℓ "亰亲使亲亰使") ∷
   rw⁻ 10 (q18 c4) ∷
   rw 11 (q19 c4) ∷
   rw 12 (q216 c4) ∷
   rw 13 (q19 c4) ∷
   rw⁻ 14 (q18 c4) ∷
   rw 15 (q216 c4) ∷
   rw 16 (q23 c4) ∷
   re 2 6 (ℓ "侀") ∷
   re 5 6 (ℓ "侀") ∷
   re 0 6 (ℓ "侠") ∷ []) Eq.refl
