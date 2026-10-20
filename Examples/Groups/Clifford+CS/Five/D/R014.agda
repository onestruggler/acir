{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R014 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0011 ; wl0012 ; wl0014 ; wl0015 ; wl0016 ; wl0017 ; wl0018 ; wl0020 ; wl0021 ; wl0026 ; wl0029 ; wl0033 ; wl0034 ; wl0037 ; wl0044 ; wl0045 ; wl0047 ; wl0053 ; wl0063 ; wl0064 ; wl0065 ; wl0078 ; wl0079 ; wl0084 ; wl0086 ; wl0088 ; wl0089 ; wl0092 ; wl0093 ; wl0095 ; wl0096 ; wl0098 ; wl0107 ; wl0109 ; wl0111 ; wl0112 ; wl0122 ; wl0124 ; wl0125 ; wl0126 ; wl0127 ; wl0128 ; wl0129 ; wl0132 ; wl0133 ; wl0136 ; wl0141 ; wl0142 ; wl0146 ; wl0154 ; wl0155 ; wl0156)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF024 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-2-TOFF103 ; lem-nat-2-TOFF301 ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-TOFF013 ; lem-nat-3-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF302 ; lem-nat-2-BOX⟨0·34⟩ ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF204 ; lem-nat-2-TOFF304 ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023 ; lem-nat-3-CZ14 ; lem-nat-3-TOFF203 ; lem-nat-3-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-BOX⟨3·4102⟩ ; lem-nat-0-CCZ014 ; lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF014 ; lem-nat-0-TOFF304 ; lem-nat-0-TOFF314 ; lem-nat-0-TOFF403 ; lem-nat-1-TOFF104 ; lem-nat-2-TOFF413 ; lem-nat-3-CZ23)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-BOX⟨3·4012⟩ ; lem-nat-0-TOFF402 ; lem-nat-0-TOFF413 ; lem-nat-1-BOX⟨3·41⟩ ; lem-nat-1-BOX⟨3·42⟩ ; lem-nat-1-TOFF013 ; lem-nat-1-TOFF304 ; lem-nat-2-BOX⟨0·2314⟩ ; lem-nat-2-BOX⟨2·41⟩ ; lem-nat-2-TOFF412 ; lem-nat-3-TOFF023 ; lem-nat-3-TOFF301 ; lem-nat-3-TOFF302)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-TOFF024 ; lem-nat-0-TOFF401 ; lem-nat-1-TOFF023 ; lem-nat-1-TOFF401 ; lem-nat-2-CCZ014 ; lem-nat-2-CZ02 ; lem-nat-2-TOFF214 ; lem-nat-2-TOFF402 ; lem-nat-3-CCZ123 ; lem-nat-3-TOFF103)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-BOX⟨0·1324⟩ ; lem-nat-0-BOX⟨0·23⟩ ; lem-nat-0-BOX⟨1·23⟩ ; lem-nat-1-BOX⟨1·24⟩ ; lem-nat-2-TOFF314 ; lem-nat-3-BOX⟨0·24⟩ ; lem-nat-3-CS14 ; lem-nat-3-CSd14)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-CS14 ; lem-nat-2-TOFF014 ; lem-nat-2-TOFF403 ; lem-nat-3-CS23 ; lem-nat-3-CS24)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨4·01⟩ ; lem-nat-0-CSd14 ; lem-nat-1-TOFF403 ; lem-nat-2-BOX⟨1·04⟩ ; lem-nat-3-BOX⟨3·04⟩ ; lem-nat-3-TOFF024 ; lem-nat-3-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-BOX⟨4·10⟩ ; lem-nat-1-BOX⟨4·01⟩ ; lem-nat-1-TOFF402 ; lem-nat-2-BOX⟨4·02⟩ ; lem-nat-2-BOX⟨4·03⟩)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-TOFF124 ; lem-nat-3-TOFF123)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-1-BOX⟨3·01⟩ ; lem-nat-2-BOX⟨2·01⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-1-BOX⟨0·3214⟩ ; lem-nat-3-BOX⟨1·03⟩ ; lem-nat-3-BOX⟨1·04⟩ ; lem-nat-3-CSd24 ; lem-nat-3-SBOX⟨1·4·2·0⟩ ; lem-nat-3-SBOXd⟨1·4·2·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-3-BOXd⟨1·42⟩ ; lem-nat-3-CSd23)

private
  q1 : WsL → Eqn
  q1 c4 = eqn (Sw34 ∷ Bx⁻1-42 ∷ []) (Bx⁻1-32 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·42⟩ c4)
  q2 : WsL → Eqn
  q2 c4 = eqn (Sw34 ∷ CCZ014 ∷ []) (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4)
  q3 : WsL → Eqn
  q3 c4 = eqn (Sw34 ∷ Toff401 ∷ []) (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4)

-- nat 3 BOXd(4;102): 8 steps
lem-nat-3-BOXd⟨4·102⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻4-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-102 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨4·102⟩ c4 = derive (Sw34 ∷ Bx⁻4-102 ∷ []) (Bx⁻3-102 ∷ Sw34 ∷ [])
  (re 1 1 (Bx⁻1-42 ∷ CCZ014 ∷ Toff401 ∷ Bx⁻1-42 ∷ Toff401 ∷ CCZ014 ∷ []) ∷
   rw 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q3 c4) ∷
   rw 5 (q2 c4) ∷
   re 0 6 (Bx⁻3-102 ∷ []) ∷ []) Eq.refl

private
  q4 : WsL → Eqn
  q4 c4 = eqn (Sw34 ∷ Bx⁻4-102 ∷ []) (Bx⁻3-102 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨4·102⟩ c4)
  q5 : WsL → Eqn
  q5 c4 = eqn (CCZ134 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ134 ∷ []) (wl0154 c4)
  q6 : WsL → Eqn
  q6 c4 = eqn (Sw34 ∷ Toff134 ∷ []) (Toff134 ∷ Sw34 ∷ []) (wl0129 c4)

-- nat 3 BOXd(1;4302): 8 steps
lem-nat-3-BOXd⟨1·4302⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻1-4302 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-3402 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·4302⟩ c4 = derive (Sw34 ∷ Bx⁻1-4302 ∷ []) (Bx⁻1-3402 ∷ Sw34 ∷ [])
  (re 1 1 (Bx⁻4-102 ∷ CCZ134 ∷ Toff134 ∷ Bx⁻4-102 ∷ Toff134 ∷ CCZ134 ∷ []) ∷
   rw 0 (q4 c4) ∷
   rw⁻ 1 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   rw 3 (q4 c4) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   re 0 6 (Bx⁻1-3402 ∷ []) ∷ []) Eq.refl

private
  q7 : WsL → Eqn
  q7 c4 = eqn (Sw34 ∷ Sb1-4-2-0 ∷ []) (Sb1-3-2-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·4·2·0⟩ c4)
  q8 : WsL → Eqn
  q8 c4 = eqn (Sw34 ∷ Toff203 ∷ []) (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4)
  q9 : WsL → Eqn
  q9 c4 = eqn (Sw34 ∷ Sb⁻1-4-2-0 ∷ []) (Sb⁻1-3-2-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·4·2·0⟩ c4)
  q10 : WsL → Eqn
  q10 c4 = eqn (Sw34 ∷ Bx⁻1-4302 ∷ []) (Bx⁻1-3402 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·4302⟩ c4)

-- nat 3 SBOXd(1;4;30;2): 7 steps
lem-nat-3-SBOXd⟨1·4·30·2⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻1-4-30-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-40-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·4·30·2⟩ c4 = derive (Sw34 ∷ Sb⁻1-4-30-2 ∷ []) (Sb⁻1-3-40-2 ∷ Sw34 ∷ [])
  (re 1 1 (Sb1-4-2-0 ∷ Toff203 ∷ Sb⁻1-4-2-0 ∷ Toff203 ∷ Bx⁻1-4302 ∷ []) ∷
   rw 0 (q7 c4) ∷
   rw 1 (q8 c4) ∷
   rw 2 (q9 c4) ∷
   rw 3 (q8 c4) ∷
   rw 4 (q10 c4) ∷
   re 0 5 (Sb⁻1-3-40-2 ∷ []) ∷ []) Eq.refl

private
  q11 : WsL → Eqn
  q11 c4 = eqn (Sw23 ∷ CZ02 ∷ []) (CZ03 ∷ Sw23 ∷ []) (lem-nat-2-CZ02 c4)

-- nat 2 BOXd(3;02): 3 steps
lem-nat-2-BOXd⟨3·02⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻3-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-03 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨3·02⟩ c4 = derive (Sw23 ∷ Bx⁻3-02 ∷ []) (Bx⁻2-03 ∷ Sw23 ∷ [])
  (re 1 1 (CZ02 ∷ []) ∷
   rw 0 (q11 c4) ∷
   re 0 1 (Bx⁻2-03 ∷ []) ∷ []) Eq.refl

private
  q12 : WsL → Eqn
  q12 c4 = eqn (Sw23 ∷ Bx⁻3-02 ∷ []) (Bx⁻2-03 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·02⟩ c4)
  q13 : WsL → Eqn
  q13 c4 = eqn (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4)
  q14 : WsL → Eqn
  q14 c4 = eqn (Sw23 ∷ Toff013 ∷ []) (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4)

-- nat 2 BOXd(0;312): 8 steps
lem-nat-2-BOXd⟨0·312⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-312 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-213 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·312⟩ c4 = derive (Sw23 ∷ Bx⁻0-312 ∷ []) (Bx⁻0-213 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻3-02 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻3-02 ∷ Toff013 ∷ CCZ013 ∷ []) ∷
   rw 0 (q12 c4) ∷
   rw 1 (q13 c4) ∷
   rw 2 (q14 c4) ∷
   rw 3 (q12 c4) ∷
   rw 4 (q14 c4) ∷
   rw 5 (q13 c4) ∷
   re 0 6 (Bx⁻0-213 ∷ []) ∷ []) Eq.refl

private
  q15 : WsL → Eqn
  q15 c4 = eqn (Sw23 ∷ Bx⁻0-312 ∷ []) (Bx⁻0-213 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·312⟩ c4)
  q16 : WsL → Eqn
  q16 c4 = eqn (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4)
  q17 : WsL → Eqn
  q17 c4 = eqn (Sw23 ∷ Toff304 ∷ []) (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4)

-- nat 2 BOXd(3;0412): 8 steps
lem-nat-2-BOXd⟨3·0412⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0413 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨3·0412⟩ c4 = derive (Sw23 ∷ Bx⁻3-0412 ∷ []) (Bx⁻2-0413 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻0-312 ∷ CCZ034 ∷ Toff304 ∷ Bx⁻0-312 ∷ Toff304 ∷ CCZ034 ∷ []) ∷
   rw 0 (q15 c4) ∷
   rw 1 (q16 c4) ∷
   rw 2 (q17 c4) ∷
   rw 3 (q15 c4) ∷
   rw 4 (q17 c4) ∷
   rw 5 (q16 c4) ∷
   re 0 6 (Bx⁻2-0413 ∷ []) ∷ []) Eq.refl

private
  q18 : WsL → Eqn
  q18 c4 = eqn (CCZ023 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ023 ∷ []) (wl0065 c4)
  q19 : WsL → Eqn
  q19 c4 = eqn (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) (wl0093 c4)
  q20 : WsL → Eqn
  q20 c4 = eqn (Sw23 ∷ Bx2-01 ∷ []) (Bx3-01 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·01⟩ c4)

-- nat 2 BOX(0;231): 8 steps
lem-nat-2-BOX⟨0·231⟩ : WsL → ⟪ (Sw23 ∷ Bx0-231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-321 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·231⟩ c4 = derive (Sw23 ∷ Bx0-231 ∷ []) (Bx0-321 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) ∷
   rw⁻ 0 (q18 c4) ∷
   rw 1 (q19 c4) ∷
   rw 2 (q20 c4) ∷
   rw 3 (q19 c4) ∷
   rw⁻ 4 (q18 c4) ∷
   rw 5 (q20 c4) ∷
   re 0 6 (Bx0-321 ∷ []) ∷ []) Eq.refl

private
  q21 : WsL → Eqn
  q21 c4 = eqn (Sw23 ∷ CCZ024 ∷ []) (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4)
  q22 : WsL → Eqn
  q22 c4 = eqn (Sw23 ∷ Toff204 ∷ []) (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4)
  q23 : WsL → Eqn
  q23 c4 = eqn (Sw23 ∷ Bx0-231 ∷ []) (Bx0-321 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·231⟩ c4)

-- nat 2 BOX(2;0431): 8 steps
lem-nat-2-BOX⟨2·0431⟩ : WsL → ⟪ (Sw23 ∷ Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·0431⟩ c4 = derive (Sw23 ∷ Bx2-0431 ∷ []) (Bx3-0421 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-231 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ []) ∷
   rw 0 (q21 c4) ∷
   rw 1 (q22 c4) ∷
   rw 2 (q23 c4) ∷
   rw 3 (q22 c4) ∷
   rw 4 (q21 c4) ∷
   rw 5 (q23 c4) ∷
   re 0 6 (Bx3-0421 ∷ []) ∷ []) Eq.refl

private
  q24 : WsL → Eqn
  q24 c4 = eqn (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4)
  q25 : WsL → Eqn
  q25 c4 = eqn (Sw12 ∷ Toff023 ∷ []) (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4)
  q26 : WsL → Eqn
  q26 c4 = eqn (Sw12 ∷ Bx3-01 ∷ []) (Bx3-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·01⟩ c4)

-- nat 1 BOX(0;321): 8 steps
lem-nat-1-BOX⟨0·321⟩ : WsL → ⟪ (Sw12 ∷ Bx0-321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-312 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·321⟩ c4 = derive (Sw12 ∷ Bx0-321 ∷ []) (Bx0-312 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) ∷
   rw 0 (q24 c4) ∷
   rw 1 (q25 c4) ∷
   rw 2 (q26 c4) ∷
   rw 3 (q25 c4) ∷
   rw 4 (q24 c4) ∷
   rw 5 (q26 c4) ∷
   re 0 6 (Bx0-312 ∷ []) ∷ []) Eq.refl

private
  q27 : WsL → Eqn
  q27 c4 = eqn (Sw12 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4)
  q28 : WsL → Eqn
  q28 c4 = eqn (Sw12 ∷ Toff304 ∷ []) (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4)
  q29 : WsL → Eqn
  q29 c4 = eqn (Sw12 ∷ Bx0-321 ∷ []) (Bx0-312 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·321⟩ c4)

-- nat 1 BOX(3;0421): 8 steps
lem-nat-1-BOX⟨3·0421⟩ : WsL → ⟪ (Sw12 ∷ Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·0421⟩ c4 = derive (Sw12 ∷ Bx3-0421 ∷ []) (Bx3-0412 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-321 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ []) ∷
   rw 0 (q27 c4) ∷
   rw 1 (q28 c4) ∷
   rw 2 (q29 c4) ∷
   rw 3 (q28 c4) ∷
   rw 4 (q27 c4) ∷
   rw 5 (q29 c4) ∷
   re 0 6 (Bx3-0412 ∷ []) ∷ []) Eq.refl

private
  q30 : WsL → Eqn
  q30 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 c4)
  q31 : WsL → Eqn
  q31 c4 = eqn (CX41 ∷ Sw23 ∷ []) (Sw23 ∷ CX41 ∷ []) (wl0156 c4)
  q32 : WsL → Eqn
  q32 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 c4)
  q33 : WsL → Eqn
  q33 c4 = eqn (CX41 ∷ Sw12 ∷ []) (Sw12 ∷ CX42 ∷ []) (wl0125 c4)
  q34 : WsL → Eqn
  q34 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 c4)
  q35 : WsL → Eqn
  q35 c4 = eqn (Sw01 ∷ CX42 ∷ []) (CX42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CX₁₀ • Swap ↑))

-- resp CX41 at 3: 6 steps
lem-resp-CX41-at-3 : WsL → ⟪ (CX41 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX42 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CX41-at-3 c4 = derive (CX41 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX42 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q30 c4) ∷
   rw 0 (q31 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 1 (q33 c4) ∷
   rw⁻ 3 (q34 c4) ∷
   rw⁻ 2 (q35 c4) ∷ []) Eq.refl

private
  q36 : WsL → Eqn
  q36 c4 = eqn (CX30 ∷ Sw12 ∷ []) (Sw12 ∷ CX30 ∷ []) (wl0124 c4)
  q37 : WsL → Eqn
  q37 c4 = eqn (CX30 ∷ Sw01 ∷ []) (Sw01 ∷ CX31 ∷ []) (wl0122 c4)

-- resp CX30 at 2: 4 steps
lem-resp-CX30-at-2 : WsL → ⟪ (CX30 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX31 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX30-at-2 c4 = derive (CX30 ∷ []) (Sw12 ∷ Sw01 ∷ CX31 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q32 c4) ∷
   rw 0 (q36 c4) ∷
   rw⁻ 2 (q34 c4) ∷
   rw 1 (q37 c4) ∷ []) Eq.refl

private
  q38 : WsL → Eqn
  q38 c4 = eqn (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) (wl0020 c4)

-- resp CX03 at 1: 2 steps
lem-resp-CX03-at-1 : WsL → ⟪ (CX03 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX13 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX03-at-1 c4 = derive (CX03 ∷ []) (Sw01 ∷ CX13 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q34 c4) ∷
   rw 0 (q38 c4) ∷ []) Eq.refl

private
  q39 : WsL → Eqn
  q39 c4 = eqn (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) (wl0014 c4)

-- resp CX03 at 2: 4 steps
lem-resp-CX03-at-2 : WsL → ⟪ (CX03 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX13 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX03-at-2 c4 = derive (CX03 ∷ []) (Sw12 ∷ Sw01 ∷ CX13 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q32 c4) ∷
   rw 0 (q39 c4) ∷
   rw⁻ 2 (q34 c4) ∷
   rw 1 (q38 c4) ∷ []) Eq.refl

private
  q40 : WsL → Eqn
  q40 c4 = eqn (Sw12 ∷ Toff403 ∷ []) (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4)
  q41 : WsL → Eqn
  q41 c4 = eqn (Sw12 ∷ Bx3-41 ∷ []) (Bx3-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·41⟩ c4)

-- nat 1 BOX(4;301): 8 steps
lem-nat-1-BOX⟨4·301⟩ : WsL → ⟪ (Sw12 ∷ Bx4-301 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-302 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·301⟩ c4 = derive (Sw12 ∷ Bx4-301 ∷ []) (Bx4-302 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) ∷
   rw 0 (q27 c4) ∷
   rw 1 (q40 c4) ∷
   rw 2 (q41 c4) ∷
   rw 3 (q40 c4) ∷
   rw 4 (q27 c4) ∷
   rw 5 (q41 c4) ∷
   re 0 6 (Bx4-302 ∷ []) ∷ []) Eq.refl

private
  q42 : WsL → Eqn
  q42 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl0034 c4)
  q43 : WsL → Eqn
  q43 c4 = eqn (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) (wl0063 c4)
  q44 : WsL → Eqn
  q44 c4 = eqn (Sw12 ∷ Bx4-301 ∷ []) (Bx4-302 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·301⟩ c4)

-- nat 1 BOX(3;4201): 8 steps
lem-nat-1-BOX⟨3·4201⟩ : WsL → ⟪ (Sw12 ∷ Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·4201⟩ c4 = derive (Sw12 ∷ Bx3-4201 ∷ []) (Bx3-4102 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff324 ∷ Bx4-301 ∷ Toff324 ∷ CCZ234 ∷ Bx4-301 ∷ []) ∷
   rw⁻ 0 (q42 c4) ∷
   rw 1 (q43 c4) ∷
   rw 2 (q44 c4) ∷
   rw 3 (q43 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   rw 5 (q44 c4) ∷
   re 0 6 (Bx3-4102 ∷ []) ∷ []) Eq.refl

private
  q45 : WsL → Eqn
  q45 c4 = eqn (Sw12 ∷ Bx3-42 ∷ []) (Bx3-41 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·42⟩ c4)

-- nat 1 BOX(4;302): 8 steps
lem-nat-1-BOX⟨4·302⟩ : WsL → ⟪ (Sw12 ∷ Bx4-302 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-301 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·302⟩ c4 = derive (Sw12 ∷ Bx4-302 ∷ []) (Bx4-301 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) ∷
   rw 0 (q27 c4) ∷
   rw 1 (q40 c4) ∷
   rw 2 (q45 c4) ∷
   rw 3 (q40 c4) ∷
   rw 4 (q27 c4) ∷
   rw 5 (q45 c4) ∷
   re 0 6 (Bx4-301 ∷ []) ∷ []) Eq.refl

private
  q46 : WsL → Eqn
  q46 c4 = eqn (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) (wl0084 c4)
  q47 : WsL → Eqn
  q47 c4 = eqn (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) (wl0064 c4)
  q48 : WsL → Eqn
  q48 c4 = eqn (Sw12 ∷ Bx4-302 ∷ []) (Bx4-301 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·302⟩ c4)

-- nat 1 BOX(3;4102): 8 steps
lem-nat-1-BOX⟨3·4102⟩ : WsL → ⟪ (Sw12 ∷ Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·4102⟩ c4 = derive (Sw12 ∷ Bx3-4102 ∷ []) (Bx3-4201 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff314 ∷ Bx4-302 ∷ Toff314 ∷ CCZ134 ∷ Bx4-302 ∷ []) ∷
   rw⁻ 0 (q46 c4) ∷
   rw 1 (q47 c4) ∷
   rw 2 (q48 c4) ∷
   rw 3 (q47 c4) ∷
   rw⁻ 4 (q46 c4) ∷
   rw 5 (q48 c4) ∷
   re 0 6 (Bx3-4201 ∷ []) ∷ []) Eq.refl

private
  q49 : WsL → Eqn
  q49 c4 = eqn (Sw23 ∷ Toff402 ∷ []) (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4)
  q50 : WsL → Eqn
  q50 c4 = eqn (Sw23 ∷ Bx2-41 ∷ []) (Bx3-41 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·41⟩ c4)

-- nat 2 BOX(4;201): 8 steps
lem-nat-2-BOX⟨4·201⟩ : WsL → ⟪ (Sw23 ∷ Bx4-201 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-301 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·201⟩ c4 = derive (Sw23 ∷ Bx4-201 ∷ []) (Bx4-301 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) ∷
   rw 0 (q21 c4) ∷
   rw 1 (q49 c4) ∷
   rw 2 (q50 c4) ∷
   rw 3 (q49 c4) ∷
   rw 4 (q21 c4) ∷
   rw 5 (q50 c4) ∷
   re 0 6 (Bx4-301 ∷ []) ∷ []) Eq.refl

private
  q51 : WsL → Eqn
  q51 c4 = eqn (CCZ234 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ234 ∷ []) (wl0086 c4)
  q52 : WsL → Eqn
  q52 c4 = eqn (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) (wl0127 c4)
  q53 : WsL → Eqn
  q53 c4 = eqn (Sw23 ∷ Bx4-201 ∷ []) (Bx4-301 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·201⟩ c4)

-- nat 2 BOX(2;4301): 8 steps
lem-nat-2-BOX⟨2·4301⟩ : WsL → ⟪ (Sw23 ∷ Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·4301⟩ c4 = derive (Sw23 ∷ Bx2-4301 ∷ []) (Bx3-4201 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-201 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ []) ∷
   rw⁻ 0 (q51 c4) ∷
   rw 1 (q52 c4) ∷
   rw 2 (q53 c4) ∷
   rw 3 (q52 c4) ∷
   rw⁻ 4 (q51 c4) ∷
   rw 5 (q53 c4) ∷
   re 0 6 (Bx3-4201 ∷ []) ∷ []) Eq.refl

private
  q54 : WsL → Eqn
  q54 c4 = eqn (Sw34 ∷ CZ14 ∷ []) (CZ13 ∷ Sw34 ∷ []) (lem-nat-3-CZ14 c4)

-- nat 3 BOX(2;41): 3 steps
lem-nat-3-BOX⟨2·41⟩ : WsL → ⟪ (Sw34 ∷ Bx2-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-31 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·41⟩ c4 = derive (Sw34 ∷ Bx2-41 ∷ []) (Bx2-31 ∷ Sw34 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   rw 0 (q54 c4) ∷
   re 0 1 (Bx2-31 ∷ []) ∷ []) Eq.refl

private
  q55 : WsL → Eqn
  q55 c4 = eqn (Sw34 ∷ CCZ024 ∷ []) (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4)
  q56 : WsL → Eqn
  q56 c4 = eqn (Sw34 ∷ Toff402 ∷ []) (Toff302 ∷ Sw34 ∷ []) (lem-nat-3-TOFF402 c4)
  q57 : WsL → Eqn
  q57 c4 = eqn (Sw34 ∷ Bx2-41 ∷ []) (Bx2-31 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·41⟩ c4)

-- nat 3 BOX(4;201): 8 steps
lem-nat-3-BOX⟨4·201⟩ : WsL → ⟪ (Sw34 ∷ Bx4-201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-201 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·201⟩ c4 = derive (Sw34 ∷ Bx4-201 ∷ []) (Bx3-201 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) ∷
   rw 0 (q55 c4) ∷
   rw 1 (q56 c4) ∷
   rw 2 (q57 c4) ∷
   rw 3 (q56 c4) ∷
   rw 4 (q55 c4) ∷
   rw 5 (q57 c4) ∷
   re 0 6 (Bx3-201 ∷ []) ∷ []) Eq.refl

private
  q58 : WsL → Eqn
  q58 c4 = eqn (CCZ234 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ234 ∷ []) (wl0155 c4)
  q59 : WsL → Eqn
  q59 c4 = eqn (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) (wl0128 c4)
  q60 : WsL → Eqn
  q60 c4 = eqn (Sw34 ∷ Bx4-201 ∷ []) (Bx3-201 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·201⟩ c4)

-- nat 3 BOX(2;4301): 8 steps
lem-nat-3-BOX⟨2·4301⟩ : WsL → ⟪ (Sw34 ∷ Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·4301⟩ c4 = derive (Sw34 ∷ Bx2-4301 ∷ []) (Bx2-3401 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-201 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ []) ∷
   rw⁻ 0 (q58 c4) ∷
   rw 1 (q59 c4) ∷
   rw 2 (q60 c4) ∷
   rw 3 (q59 c4) ∷
   rw⁻ 4 (q58 c4) ∷
   rw 5 (q60 c4) ∷
   re 0 6 (Bx2-3401 ∷ []) ∷ []) Eq.refl

private
  q61 : WsL → Eqn
  q61 c4 = eqn (Sw01 ∷ Sb3-4-2-0 ∷ []) (Sb3-4-2-0 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))

-- nat 0 SBOX(3;4;2;0): 2 steps
lem-nat-0-SBOX⟨3·4·2·0⟩ : WsL → ⟪ (Sw01 ∷ Sb3-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-2-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·4·2·0⟩ c4 = derive (Sw01 ∷ Sb3-4-2-0 ∷ []) (Sb3-4-2-1 ∷ Sw01 ∷ [])
  (rw 0 (q61 c4) ∷
   re 0 1 (Sb3-4-2-1 ∷ []) ∷ []) Eq.refl

private
  q62 : WsL → Eqn
  q62 c4 = eqn (Sw01 ∷ Sb⁻3-4-2-0 ∷ []) (Sb⁻3-4-2-0 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))

-- nat 0 SBOXd(3;4;2;0): 2 steps
lem-nat-0-SBOXd⟨3·4·2·0⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻3-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-2-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨3·4·2·0⟩ c4 = derive (Sw01 ∷ Sb⁻3-4-2-0 ∷ []) (Sb⁻3-4-2-1 ∷ Sw01 ∷ [])
  (rw 0 (q62 c4) ∷
   re 0 1 (Sb⁻3-4-2-1 ∷ []) ∷ []) Eq.refl

private
  q63 : WsL → Eqn
  q63 c4 = eqn (Sw01 ∷ Bx3-4102 ∷ []) (Bx3-4012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4102⟩ c4)
  q64 : WsL → Eqn
  q64 c4 = eqn (Sw01 ∷ Toff201 ∷ []) (Toff201 ∷ Sw01 ∷ []) (wl0107 c4)
  q65 : WsL → Eqn
  q65 c4 = eqn (Sw01 ∷ Sb3-4-2-0 ∷ []) (Sb3-4-2-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·4·2·0⟩ c4)
  q66 : WsL → Eqn
  q66 c4 = eqn (Sw01 ∷ Sb⁻3-4-2-0 ∷ []) (Sb⁻3-4-2-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨3·4·2·0⟩ c4)

-- nat 0 SBOX(3;4;10;2): 7 steps
lem-nat-0-SBOX⟨3·4·10·2⟩ : WsL → ⟪ (Sw01 ∷ Sb3-4-10-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-01-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·4·10·2⟩ c4 = derive (Sw01 ∷ Sb3-4-10-2 ∷ []) (Sb3-4-01-2 ∷ Sw01 ∷ [])
  (re 1 1 (Bx3-4102 ∷ Toff201 ∷ Sb3-4-2-0 ∷ Toff201 ∷ Sb⁻3-4-2-0 ∷ []) ∷
   rw 0 (q63 c4) ∷
   rw 1 (q64 c4) ∷
   rw 2 (q65 c4) ∷
   rw 3 (q64 c4) ∷
   rw 4 (q66 c4) ∷
   re 0 5 (Sb3-4-01-2 ∷ []) ∷ []) Eq.refl

private
  q67 : WsL → Eqn
  q67 c4 = eqn (Sw01 ∷ Sb3-4-2-1 ∷ []) (Sb3-4-2-1 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))

-- nat 0 SBOX(3;4;2;1): 2 steps
lem-nat-0-SBOX⟨3·4·2·1⟩ : WsL → ⟪ (Sw01 ∷ Sb3-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-2-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·4·2·1⟩ c4 = derive (Sw01 ∷ Sb3-4-2-1 ∷ []) (Sb3-4-2-0 ∷ Sw01 ∷ [])
  (rw 0 (q67 c4) ∷
   re 0 1 (Sb3-4-2-0 ∷ []) ∷ []) Eq.refl

private
  q68 : WsL → Eqn
  q68 c4 = eqn (Sw01 ∷ Sb⁻3-4-2-1 ∷ []) (Sb⁻3-4-2-1 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))

-- nat 0 SBOXd(3;4;2;1): 2 steps
lem-nat-0-SBOXd⟨3·4·2·1⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻3-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-2-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨3·4·2·1⟩ c4 = derive (Sw01 ∷ Sb⁻3-4-2-1 ∷ []) (Sb⁻3-4-2-0 ∷ Sw01 ∷ [])
  (rw 0 (q68 c4) ∷
   re 0 1 (Sb⁻3-4-2-0 ∷ []) ∷ []) Eq.refl

private
  q69 : WsL → Eqn
  q69 c4 = eqn (Sw01 ∷ Bx3-4012 ∷ []) (Bx3-4102 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4012⟩ c4)
  q70 : WsL → Eqn
  q70 c4 = eqn (Sw01 ∷ Sb3-4-2-1 ∷ []) (Sb3-4-2-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·4·2·1⟩ c4)
  q71 : WsL → Eqn
  q71 c4 = eqn (Sw01 ∷ Sb⁻3-4-2-1 ∷ []) (Sb⁻3-4-2-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨3·4·2·1⟩ c4)

-- nat 0 SBOX(3;4;01;2): 7 steps
lem-nat-0-SBOX⟨3·4·01·2⟩ : WsL → ⟪ (Sw01 ∷ Sb3-4-01-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-10-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·4·01·2⟩ c4 = derive (Sw01 ∷ Sb3-4-01-2 ∷ []) (Sb3-4-10-2 ∷ Sw01 ∷ [])
  (re 1 1 (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ []) ∷
   rw 0 (q69 c4) ∷
   rw 1 (q64 c4) ∷
   rw 2 (q70 c4) ∷
   rw 3 (q64 c4) ∷
   rw 4 (q71 c4) ∷
   re 0 5 (Sb3-4-10-2 ∷ []) ∷ []) Eq.refl

private
  q72 : WsL → Eqn
  q72 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0008 c4)

-- nat 1 SBOX(3;4;1;0): 3 steps
lem-nat-1-SBOX⟨3·4·1·0⟩ : WsL → ⟪ (Sw12 ∷ Sb3-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·4·1·0⟩ c4 = derive (Sw12 ∷ Sb3-4-1-0 ∷ []) (Sb3-4-2-0 ∷ Sw12 ∷ [])
  (re 1 1 (CS14 ∷ []) ∷
   rw⁻ 0 (q72 c4) ∷
   re 0 1 (Sb3-4-2-0 ∷ []) ∷ []) Eq.refl

private
  q73 : WsL → Eqn
  q73 c4 = eqn (CS24⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS14⁻ ∷ []) (wl0009 c4)

-- nat 1 SBOXd(3;4;1;0): 3 steps
lem-nat-1-SBOXd⟨3·4·1·0⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻3-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·4·1·0⟩ c4 = derive (Sw12 ∷ Sb⁻3-4-1-0 ∷ []) (Sb⁻3-4-2-0 ∷ Sw12 ∷ [])
  (re 1 1 (CS14⁻ ∷ []) ∷
   rw⁻ 0 (q73 c4) ∷
   re 0 1 (Sb⁻3-4-2-0 ∷ []) ∷ []) Eq.refl

private
  q74 : WsL → Eqn
  q74 c4 = eqn (Sw12 ∷ Bx3-4201 ∷ []) (Bx3-4102 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4201⟩ c4)
  q75 : WsL → Eqn
  q75 c4 = eqn (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) (wl0047 c4)
  q76 : WsL → Eqn
  q76 c4 = eqn (Sw12 ∷ Sb3-4-1-0 ∷ []) (Sb3-4-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·4·1·0⟩ c4)
  q77 : WsL → Eqn
  q77 c4 = eqn (Sw12 ∷ Sb⁻3-4-1-0 ∷ []) (Sb⁻3-4-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·4·1·0⟩ c4)

-- nat 1 SBOX(3;4;20;1): 7 steps
lem-nat-1-SBOX⟨3·4·20·1⟩ : WsL → ⟪ (Sw12 ∷ Sb3-4-20-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-10-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·4·20·1⟩ c4 = derive (Sw12 ∷ Sb3-4-20-1 ∷ []) (Sb3-4-10-2 ∷ Sw12 ∷ [])
  (re 1 1 (Bx3-4201 ∷ Toff102 ∷ Sb3-4-1-0 ∷ Toff102 ∷ Sb⁻3-4-1-0 ∷ []) ∷
   rw 0 (q74 c4) ∷
   rw 1 (q75 c4) ∷
   rw 2 (q76 c4) ∷
   rw 3 (q75 c4) ∷
   rw 4 (q77 c4) ∷
   re 0 5 (Sb3-4-10-2 ∷ []) ∷ []) Eq.refl

private
  q78 : WsL → Eqn
  q78 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl0017 c4)

-- nat 1 SBOX(3;4;2;0): 3 steps
lem-nat-1-SBOX⟨3·4·2·0⟩ : WsL → ⟪ (Sw12 ∷ Sb3-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-1-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·4·2·0⟩ c4 = derive (Sw12 ∷ Sb3-4-2-0 ∷ []) (Sb3-4-1-0 ∷ Sw12 ∷ [])
  (re 1 1 (CS24 ∷ []) ∷
   rw⁻ 0 (q78 c4) ∷
   re 0 1 (Sb3-4-1-0 ∷ []) ∷ []) Eq.refl

private
  q79 : WsL → Eqn
  q79 c4 = eqn (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ []) (wl0018 c4)

-- nat 1 SBOXd(3;4;2;0): 3 steps
lem-nat-1-SBOXd⟨3·4·2·0⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻3-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-1-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·4·2·0⟩ c4 = derive (Sw12 ∷ Sb⁻3-4-2-0 ∷ []) (Sb⁻3-4-1-0 ∷ Sw12 ∷ [])
  (re 1 1 (CS24⁻ ∷ []) ∷
   rw⁻ 0 (q79 c4) ∷
   re 0 1 (Sb⁻3-4-1-0 ∷ []) ∷ []) Eq.refl

private
  q80 : WsL → Eqn
  q80 c4 = eqn (Sw12 ∷ Bx3-4102 ∷ []) (Bx3-4201 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4102⟩ c4)
  q81 : WsL → Eqn
  q81 c4 = eqn (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) (wl0044 c4)
  q82 : WsL → Eqn
  q82 c4 = eqn (Sw12 ∷ Sb3-4-2-0 ∷ []) (Sb3-4-1-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·4·2·0⟩ c4)
  q83 : WsL → Eqn
  q83 c4 = eqn (Sw12 ∷ Sb⁻3-4-2-0 ∷ []) (Sb⁻3-4-1-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·4·2·0⟩ c4)

-- nat 1 SBOX(3;4;10;2): 7 steps
lem-nat-1-SBOX⟨3·4·10·2⟩ : WsL → ⟪ (Sw12 ∷ Sb3-4-10-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-20-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·4·10·2⟩ c4 = derive (Sw12 ∷ Sb3-4-10-2 ∷ []) (Sb3-4-20-1 ∷ Sw12 ∷ [])
  (re 1 1 (Bx3-4102 ∷ Toff201 ∷ Sb3-4-2-0 ∷ Toff201 ∷ Sb⁻3-4-2-0 ∷ []) ∷
   rw 0 (q80 c4) ∷
   rw 1 (q81 c4) ∷
   rw 2 (q82 c4) ∷
   rw 3 (q81 c4) ∷
   rw 4 (q83 c4) ∷
   re 0 5 (Sb3-4-20-1 ∷ []) ∷ []) Eq.refl

private
  q84 : WsL → Eqn
  q84 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl0021 c4)

-- nat 2 SBOX(2;4;1;0): 3 steps
lem-nat-2-SBOX⟨2·4·1·0⟩ : WsL → ⟪ (Sw23 ∷ Sb2-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-1-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·4·1·0⟩ c4 = derive (Sw23 ∷ Sb2-4-1-0 ∷ []) (Sb3-4-1-0 ∷ Sw23 ∷ [])
  (re 1 1 (CS14 ∷ []) ∷
   rw⁻ 0 (q84 c4) ∷
   re 0 1 (Sb3-4-1-0 ∷ []) ∷ []) Eq.refl

private
  q85 : WsL → Eqn
  q85 c4 = eqn (CS14⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS14⁻ ∷ []) (wl0033 c4)

-- nat 2 SBOXd(2;4;1;0): 3 steps
lem-nat-2-SBOXd⟨2·4·1·0⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻2-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-1-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨2·4·1·0⟩ c4 = derive (Sw23 ∷ Sb⁻2-4-1-0 ∷ []) (Sb⁻3-4-1-0 ∷ Sw23 ∷ [])
  (re 1 1 (CS14⁻ ∷ []) ∷
   rw⁻ 0 (q85 c4) ∷
   re 0 1 (Sb⁻3-4-1-0 ∷ []) ∷ []) Eq.refl

private
  q86 : WsL → Eqn
  q86 c4 = eqn (Sw23 ∷ Bx2-4301 ∷ []) (Bx3-4201 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·4301⟩ c4)
  q87 : WsL → Eqn
  q87 c4 = eqn (Sw23 ∷ Toff103 ∷ []) (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4)
  q88 : WsL → Eqn
  q88 c4 = eqn (Sw23 ∷ Sb2-4-1-0 ∷ []) (Sb3-4-1-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·4·1·0⟩ c4)
  q89 : WsL → Eqn
  q89 c4 = eqn (Sw23 ∷ Sb⁻2-4-1-0 ∷ []) (Sb⁻3-4-1-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨2·4·1·0⟩ c4)

-- nat 2 SBOX(2;4;30;1): 7 steps
lem-nat-2-SBOX⟨2·4·30·1⟩ : WsL → ⟪ (Sw23 ∷ Sb2-4-30-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-20-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·4·30·1⟩ c4 = derive (Sw23 ∷ Sb2-4-30-1 ∷ []) (Sb3-4-20-1 ∷ Sw23 ∷ [])
  (re 1 1 (Bx2-4301 ∷ Toff103 ∷ Sb2-4-1-0 ∷ Toff103 ∷ Sb⁻2-4-1-0 ∷ []) ∷
   rw 0 (q86 c4) ∷
   rw 1 (q87 c4) ∷
   rw 2 (q88 c4) ∷
   rw 3 (q87 c4) ∷
   rw 4 (q89 c4) ∷
   re 0 5 (Sb3-4-20-1 ∷ []) ∷ []) Eq.refl

private
  q90 : WsL → Eqn
  q90 c4 = eqn (Sw34 ∷ CS14 ∷ []) (CS13 ∷ Sw34 ∷ []) (lem-nat-3-CS14 c4)

-- nat 3 SBOX(2;4;1;0): 3 steps
lem-nat-3-SBOX⟨2·4·1·0⟩ : WsL → ⟪ (Sw34 ∷ Sb2-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-1-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·4·1·0⟩ c4 = derive (Sw34 ∷ Sb2-4-1-0 ∷ []) (Sb2-3-1-0 ∷ Sw34 ∷ [])
  (re 1 1 (CS14 ∷ []) ∷
   rw 0 (q90 c4) ∷
   re 0 1 (Sb2-3-1-0 ∷ []) ∷ []) Eq.refl

private
  q91 : WsL → Eqn
  q91 c4 = eqn (Sw34 ∷ CS14⁻ ∷ []) (CS13⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd14 c4)

-- nat 3 SBOXd(2;4;1;0): 3 steps
lem-nat-3-SBOXd⟨2·4·1·0⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻2-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-1-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·4·1·0⟩ c4 = derive (Sw34 ∷ Sb⁻2-4-1-0 ∷ []) (Sb⁻2-3-1-0 ∷ Sw34 ∷ [])
  (re 1 1 (CS14⁻ ∷ []) ∷
   rw 0 (q91 c4) ∷
   re 0 1 (Sb⁻2-3-1-0 ∷ []) ∷ []) Eq.refl

private
  q92 : WsL → Eqn
  q92 c4 = eqn (Sw34 ∷ Bx2-4301 ∷ []) (Bx2-3401 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·4301⟩ c4)
  q93 : WsL → Eqn
  q93 c4 = eqn (Sw34 ∷ Toff103 ∷ []) (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4)
  q94 : WsL → Eqn
  q94 c4 = eqn (Sw34 ∷ Sb2-4-1-0 ∷ []) (Sb2-3-1-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·4·1·0⟩ c4)
  q95 : WsL → Eqn
  q95 c4 = eqn (Sw34 ∷ Sb⁻2-4-1-0 ∷ []) (Sb⁻2-3-1-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·4·1·0⟩ c4)

-- nat 3 SBOX(2;4;30;1): 7 steps
lem-nat-3-SBOX⟨2·4·30·1⟩ : WsL → ⟪ (Sw34 ∷ Sb2-4-30-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-40-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·4·30·1⟩ c4 = derive (Sw34 ∷ Sb2-4-30-1 ∷ []) (Sb2-3-40-1 ∷ Sw34 ∷ [])
  (re 1 1 (Bx2-4301 ∷ Toff103 ∷ Sb2-4-1-0 ∷ Toff103 ∷ Sb⁻2-4-1-0 ∷ []) ∷
   rw 0 (q92 c4) ∷
   rw 1 (q93 c4) ∷
   rw 2 (q94 c4) ∷
   rw 3 (q93 c4) ∷
   rw 4 (q95 c4) ∷
   re 0 5 (Sb2-3-40-1 ∷ []) ∷ []) Eq.refl

private
  q96 : WsL → Eqn
  q96 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4)
  q97 : WsL → Eqn
  q97 c4 = eqn (Sw23 ∷ Toff012 ∷ []) (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4)
  q98 : WsL → Eqn
  q98 c4 = eqn (Sw23 ∷ Bx1-04 ∷ []) (Bx1-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·04⟩ c4)

-- nat 2 BOX(0;124): 8 steps
lem-nat-2-BOX⟨0·124⟩ : WsL → ⟪ (Sw23 ∷ Bx0-124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-134 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·124⟩ c4 = derive (Sw23 ∷ Bx0-124 ∷ []) (Bx0-134 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-04 ∷ Toff012 ∷ CCZ012 ∷ Bx1-04 ∷ []) ∷
   rw 0 (q96 c4) ∷
   rw 1 (q97 c4) ∷
   rw 2 (q98 c4) ∷
   rw 3 (q97 c4) ∷
   rw 4 (q96 c4) ∷
   rw 5 (q98 c4) ∷
   re 0 6 (Bx0-134 ∷ []) ∷ []) Eq.refl

private
  q99 : WsL → Eqn
  q99 c4 = eqn (Sw23 ∷ Bx0-124 ∷ []) (Bx0-134 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·124⟩ c4)

-- nat 2 BOX(1;0324): 8 steps
lem-nat-2-BOX⟨1·0324⟩ : WsL → ⟪ (Sw23 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·0324⟩ c4 = derive (Sw23 ∷ Bx1-0324 ∷ []) (Bx1-0234 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-124 ∷ Toff103 ∷ CCZ013 ∷ Bx0-124 ∷ []) ∷
   rw 0 (q13 c4) ∷
   rw 1 (q87 c4) ∷
   rw 2 (q99 c4) ∷
   rw 3 (q87 c4) ∷
   rw 4 (q13 c4) ∷
   rw 5 (q99 c4) ∷
   re 0 6 (Bx1-0234 ∷ []) ∷ []) Eq.refl

private
  q100 : WsL → Eqn
  q100 c4 = eqn (CCZ012 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (Swap))
  q101 : WsL → Eqn
  q101 c4 = eqn (Toff012 ∷ Sw34 ∷ []) (Sw34 ∷ Toff012 ∷ []) (c₃ (Toff) (Swap))
  q102 : WsL → Eqn
  q102 c4 = eqn (Sw34 ∷ Bx1-03 ∷ []) (Bx1-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·03⟩ c4)

-- nat 3 BOX(0;123): 8 steps
lem-nat-3-BOX⟨0·123⟩ : WsL → ⟪ (Sw34 ∷ Bx0-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-124 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·123⟩ c4 = derive (Sw34 ∷ Bx0-123 ∷ []) (Bx0-124 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-03 ∷ Toff012 ∷ CCZ012 ∷ Bx1-03 ∷ []) ∷
   rw⁻ 0 (q100 c4) ∷
   rw⁻ 1 (q101 c4) ∷
   rw 2 (q102 c4) ∷
   rw⁻ 3 (q101 c4) ∷
   rw⁻ 4 (q100 c4) ∷
   rw 5 (q102 c4) ∷
   re 0 6 (Bx0-124 ∷ []) ∷ []) Eq.refl

private
  q103 : WsL → Eqn
  q103 c4 = eqn (Sw34 ∷ Toff104 ∷ []) (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4)
  q104 : WsL → Eqn
  q104 c4 = eqn (Sw34 ∷ Bx0-123 ∷ []) (Bx0-124 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·123⟩ c4)

-- nat 3 BOX(1;0423): 8 steps
lem-nat-3-BOX⟨1·0423⟩ : WsL → ⟪ (Sw34 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·0423⟩ c4 = derive (Sw34 ∷ Bx1-0423 ∷ []) (Bx1-0324 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-123 ∷ Toff104 ∷ CCZ014 ∷ Bx0-123 ∷ []) ∷
   rw 0 (q2 c4) ∷
   rw 1 (q103 c4) ∷
   rw 2 (q104 c4) ∷
   rw 3 (q103 c4) ∷
   rw 4 (q2 c4) ∷
   rw 5 (q104 c4) ∷
   re 0 6 (Bx1-0324 ∷ []) ∷ []) Eq.refl

private
  q105 : WsL → Eqn
  q105 c4 = eqn (Sw34 ∷ Bx1-04 ∷ []) (Bx1-03 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·04⟩ c4)

-- nat 3 BOX(0;124): 8 steps
lem-nat-3-BOX⟨0·124⟩ : WsL → ⟪ (Sw34 ∷ Bx0-124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-123 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·124⟩ c4 = derive (Sw34 ∷ Bx0-124 ∷ []) (Bx0-123 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-04 ∷ Toff012 ∷ CCZ012 ∷ Bx1-04 ∷ []) ∷
   rw⁻ 0 (q100 c4) ∷
   rw⁻ 1 (q101 c4) ∷
   rw 2 (q105 c4) ∷
   rw⁻ 3 (q101 c4) ∷
   rw⁻ 4 (q100 c4) ∷
   rw 5 (q105 c4) ∷
   re 0 6 (Bx0-123 ∷ []) ∷ []) Eq.refl

private
  q106 : WsL → Eqn
  q106 c4 = eqn (Sw34 ∷ CCZ013 ∷ []) (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4)
  q107 : WsL → Eqn
  q107 c4 = eqn (Sw34 ∷ Bx0-124 ∷ []) (Bx0-123 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·124⟩ c4)

-- nat 3 BOX(1;0324): 8 steps
lem-nat-3-BOX⟨1·0324⟩ : WsL → ⟪ (Sw34 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·0324⟩ c4 = derive (Sw34 ∷ Bx1-0324 ∷ []) (Bx1-0423 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-124 ∷ Toff103 ∷ CCZ013 ∷ Bx0-124 ∷ []) ∷
   rw 0 (q106 c4) ∷
   rw 1 (q93 c4) ∷
   rw 2 (q107 c4) ∷
   rw 3 (q93 c4) ∷
   rw 4 (q106 c4) ∷
   rw 5 (q107 c4) ∷
   re 0 6 (Bx1-0423 ∷ []) ∷ []) Eq.refl

private
  q108 : WsL → Eqn
  q108 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 c4)
  q109 : WsL → Eqn
  q109 c4 = eqn (CX10 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ))

-- comm CCZ134 CX20: 23 steps
lem-comm-CCZ134-CX20 : WsL → ⟪ (CCZ134 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ CCZ134 ∷ []) ⟫ʷ
lem-comm-CCZ134-CX20 c4 = derive (CCZ134 ∷ CX20 ∷ []) (CX20 ∷ CCZ134 ∷ [])
  (re 0 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q30 c4) ∷
   re 4 3 (CX30 ∷ []) ∷
   rw⁻ 5 (q108 c4) ∷
   re 3 3 (CX40 ∷ []) ∷
   re 3 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q108 c4) ∷
   re 3 3 (CCZ124 ∷ []) ∷
   rw⁻ 3 (q30 c4) ∷
   re 4 3 (CCZ134 ∷ []) ∷
   rw 4 (q42 c4) ∷
   rw⁻ 5 (q109 c4) ∷
   rw 6 (q46 c4) ∷
   re 7 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 9 (q30 c4) ∷
   re 8 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   rw 10 (q108 c4) ∷
   re 2 7 (CX40 ∷ []) ∷
   re 2 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) ∷
   rw 1 (q108 c4) ∷
   re 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 0 (q30 c4) ∷
   re 1 5 (CCZ134 ∷ []) ∷ []) Eq.refl

private
  q110 : WsL → Eqn
  q110 c4 = eqn (CS01⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ))

-- comm CSd04 CCZ123: 13 steps
lem-comm-CSd04-CCZ123 : WsL → ⟪ (CS04⁻ ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-comm-CSd04-CCZ123 c4 = derive (CS04⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ CS04⁻ ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q108 c4) ∷
   re 6 3 (CCZ124 ∷ []) ∷
   rw⁻ 7 (q30 c4) ∷
   re 5 3 (CCZ134 ∷ []) ∷
   rw⁻ 4 (q46 c4) ∷
   rw 3 (q110 c4) ∷
   rw⁻ 2 (q42 c4) ∷
   re 2 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 1 (q30 c4) ∷
   re 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   rw 0 (q108 c4) ∷
   re 1 7 (CS04⁻ ∷ []) ∷ []) Eq.refl

private
  q111 : WsL → Eqn
  q111 c4 = eqn (Sw12 ∷ Sb0-3-4-1 ∷ []) (Sb0-3-4-1 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))

-- nat 1 SBOX(0;3;4;1): 2 steps
lem-nat-1-SBOX⟨0·3·4·1⟩ : WsL → ⟪ (Sw12 ∷ Sb0-3-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-4-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·3·4·1⟩ c4 = derive (Sw12 ∷ Sb0-3-4-1 ∷ []) (Sb0-3-4-2 ∷ Sw12 ∷ [])
  (rw 0 (q111 c4) ∷
   re 0 1 (Sb0-3-4-2 ∷ []) ∷ []) Eq.refl

private
  q112 : WsL → Eqn
  q112 c4 = eqn (Sw12 ∷ Sb⁻0-3-4-1 ∷ []) (Sb⁻0-3-4-1 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS))

-- nat 1 SBOXd(0;3;4;1): 2 steps
lem-nat-1-SBOXd⟨0·3·4·1⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻0-3-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-4-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·3·4·1⟩ c4 = derive (Sw12 ∷ Sb⁻0-3-4-1 ∷ []) (Sb⁻0-3-4-2 ∷ Sw12 ∷ [])
  (rw 0 (q112 c4) ∷
   re 0 1 (Sb⁻0-3-4-2 ∷ []) ∷ []) Eq.refl

private
  q113 : WsL → Eqn
  q113 c4 = eqn (Sw12 ∷ Bx0-3214 ∷ []) (Bx0-3124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3214⟩ c4)
  q114 : WsL → Eqn
  q114 c4 = eqn (Sw12 ∷ Toff412 ∷ []) (Toff412 ∷ Sw12 ∷ []) (wl0079 c4)
  q115 : WsL → Eqn
  q115 c4 = eqn (Sw12 ∷ Sb0-3-4-1 ∷ []) (Sb0-3-4-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·3·4·1⟩ c4)
  q116 : WsL → Eqn
  q116 c4 = eqn (Sw12 ∷ Sb⁻0-3-4-1 ∷ []) (Sb⁻0-3-4-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·3·4·1⟩ c4)

-- nat 1 SBOX(0;3;21;4): 7 steps
lem-nat-1-SBOX⟨0·3·21·4⟩ : WsL → ⟪ (Sw12 ∷ Sb0-3-21-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-12-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·3·21·4⟩ c4 = derive (Sw12 ∷ Sb0-3-21-4 ∷ []) (Sb0-3-12-4 ∷ Sw12 ∷ [])
  (re 1 1 (Bx0-3214 ∷ Toff412 ∷ Sb0-3-4-1 ∷ Toff412 ∷ Sb⁻0-3-4-1 ∷ []) ∷
   rw 0 (q113 c4) ∷
   rw 1 (q114 c4) ∷
   rw 2 (q115 c4) ∷
   rw 3 (q114 c4) ∷
   rw 4 (q116 c4) ∷
   re 0 5 (Sb0-3-12-4 ∷ []) ∷ []) Eq.refl

private
  q117 : WsL → Eqn
  q117 c4 = eqn (Sw12 ∷ Toff302 ∷ []) (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4)
  q118 : WsL → Eqn
  q118 c4 = eqn (Sw12 ∷ Bx0-34 ∷ []) (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ))

-- nat 1 BOX(3;024): 8 steps
lem-nat-1-BOX⟨3·024⟩ : WsL → ⟪ (Sw12 ∷ Bx3-024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-014 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·024⟩ c4 = derive (Sw12 ∷ Bx3-024 ∷ []) (Bx3-014 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) ∷
   rw 0 (q24 c4) ∷
   rw 1 (q117 c4) ∷
   rw 2 (q118 c4) ∷
   rw 3 (q117 c4) ∷
   rw 4 (q24 c4) ∷
   rw 5 (q118 c4) ∷
   re 0 6 (Bx3-014 ∷ []) ∷ []) Eq.refl

private
  q119 : WsL → Eqn
  q119 c4 = eqn (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4)
  q120 : WsL → Eqn
  q120 c4 = eqn (Sw12 ∷ Toff013 ∷ []) (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4)
  q121 : WsL → Eqn
  q121 c4 = eqn (Sw12 ∷ Bx3-024 ∷ []) (Bx3-014 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·024⟩ c4)

-- nat 1 BOX(0;3124): 8 steps
lem-nat-1-BOX⟨0·3124⟩ : WsL → ⟪ (Sw12 ∷ Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·3124⟩ c4 = derive (Sw12 ∷ Bx0-3124 ∷ []) (Bx0-3214 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ []) ∷
   rw 0 (q119 c4) ∷
   rw 1 (q120 c4) ∷
   rw 2 (q121 c4) ∷
   rw 3 (q120 c4) ∷
   rw 4 (q119 c4) ∷
   rw 5 (q121 c4) ∷
   re 0 6 (Bx0-3214 ∷ []) ∷ []) Eq.refl

private
  q122 : WsL → Eqn
  q122 c4 = eqn (Sw12 ∷ Sb0-3-4-2 ∷ []) (Sb0-3-4-2 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))

-- nat 1 SBOX(0;3;4;2): 2 steps
lem-nat-1-SBOX⟨0·3·4·2⟩ : WsL → ⟪ (Sw12 ∷ Sb0-3-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-4-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·3·4·2⟩ c4 = derive (Sw12 ∷ Sb0-3-4-2 ∷ []) (Sb0-3-4-1 ∷ Sw12 ∷ [])
  (rw 0 (q122 c4) ∷
   re 0 1 (Sb0-3-4-1 ∷ []) ∷ []) Eq.refl

private
  q123 : WsL → Eqn
  q123 c4 = eqn (Sw12 ∷ Sb⁻0-3-4-2 ∷ []) (Sb⁻0-3-4-2 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS))

-- nat 1 SBOXd(0;3;4;2): 2 steps
lem-nat-1-SBOXd⟨0·3·4·2⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻0-3-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-4-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·3·4·2⟩ c4 = derive (Sw12 ∷ Sb⁻0-3-4-2 ∷ []) (Sb⁻0-3-4-1 ∷ Sw12 ∷ [])
  (rw 0 (q123 c4) ∷
   re 0 1 (Sb⁻0-3-4-1 ∷ []) ∷ []) Eq.refl

private
  q124 : WsL → Eqn
  q124 c4 = eqn (Sw12 ∷ Bx0-3124 ∷ []) (Bx0-3214 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3124⟩ c4)
  q125 : WsL → Eqn
  q125 c4 = eqn (Sw12 ∷ Sb0-3-4-2 ∷ []) (Sb0-3-4-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·3·4·2⟩ c4)
  q126 : WsL → Eqn
  q126 c4 = eqn (Sw12 ∷ Sb⁻0-3-4-2 ∷ []) (Sb⁻0-3-4-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·3·4·2⟩ c4)

-- nat 1 SBOX(0;3;12;4): 7 steps
lem-nat-1-SBOX⟨0·3·12·4⟩ : WsL → ⟪ (Sw12 ∷ Sb0-3-12-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-21-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·3·12·4⟩ c4 = derive (Sw12 ∷ Sb0-3-12-4 ∷ []) (Sb0-3-21-4 ∷ Sw12 ∷ [])
  (re 1 1 (Bx0-3124 ∷ Toff412 ∷ Sb0-3-4-2 ∷ Toff412 ∷ Sb⁻0-3-4-2 ∷ []) ∷
   rw 0 (q124 c4) ∷
   rw 1 (q114 c4) ∷
   rw 2 (q125 c4) ∷
   rw 3 (q114 c4) ∷
   rw 4 (q126 c4) ∷
   re 0 5 (Sb0-3-21-4 ∷ []) ∷ []) Eq.refl

private
  q127 : WsL → Eqn
  q127 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl0011 c4)

-- nat 2 SBOX(0;2;4;1): 3 steps
lem-nat-2-SBOX⟨0·2·4·1⟩ : WsL → ⟪ (Sw23 ∷ Sb0-2-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-4-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·2·4·1⟩ c4 = derive (Sw23 ∷ Sb0-2-4-1 ∷ []) (Sb0-3-4-1 ∷ Sw23 ∷ [])
  (re 1 1 (CS24 ∷ []) ∷
   rw⁻ 0 (q127 c4) ∷
   re 0 1 (Sb0-3-4-1 ∷ []) ∷ []) Eq.refl

private
  q128 : WsL → Eqn
  q128 c4 = eqn (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) (wl0012 c4)

-- nat 2 SBOXd(0;2;4;1): 3 steps
lem-nat-2-SBOXd⟨0·2·4·1⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻0-2-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-4-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·2·4·1⟩ c4 = derive (Sw23 ∷ Sb⁻0-2-4-1 ∷ []) (Sb⁻0-3-4-1 ∷ Sw23 ∷ [])
  (re 1 1 (CS24⁻ ∷ []) ∷
   rw⁻ 0 (q128 c4) ∷
   re 0 1 (Sb⁻0-3-4-1 ∷ []) ∷ []) Eq.refl

private
  q129 : WsL → Eqn
  q129 c4 = eqn (Sw23 ∷ Bx0-2314 ∷ []) (Bx0-3214 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·2314⟩ c4)
  q130 : WsL → Eqn
  q130 c4 = eqn (Sw23 ∷ Toff413 ∷ []) (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4)
  q131 : WsL → Eqn
  q131 c4 = eqn (Sw23 ∷ Sb0-2-4-1 ∷ []) (Sb0-3-4-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·2·4·1⟩ c4)
  q132 : WsL → Eqn
  q132 c4 = eqn (Sw23 ∷ Sb⁻0-2-4-1 ∷ []) (Sb⁻0-3-4-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·2·4·1⟩ c4)

-- nat 2 SBOX(0;2;31;4): 7 steps
lem-nat-2-SBOX⟨0·2·31·4⟩ : WsL → ⟪ (Sw23 ∷ Sb0-2-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-21-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·2·31·4⟩ c4 = derive (Sw23 ∷ Sb0-2-31-4 ∷ []) (Sb0-3-21-4 ∷ Sw23 ∷ [])
  (re 1 1 (Bx0-2314 ∷ Toff413 ∷ Sb0-2-4-1 ∷ Toff413 ∷ Sb⁻0-2-4-1 ∷ []) ∷
   rw 0 (q129 c4) ∷
   rw 1 (q130 c4) ∷
   rw 2 (q131 c4) ∷
   rw 3 (q130 c4) ∷
   rw 4 (q132 c4) ∷
   re 0 5 (Sb0-3-21-4 ∷ []) ∷ []) Eq.refl

private
  q133 : WsL → Eqn
  q133 c4 = eqn (Sw23 ∷ Toff301 ∷ []) (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4)
  q134 : WsL → Eqn
  q134 c4 = eqn (Sw23 ∷ Bx0-34 ∷ []) (Bx0-24 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·34⟩ c4)

-- nat 2 BOX(3;014): 8 steps
lem-nat-2-BOX⟨3·014⟩ : WsL → ⟪ (Sw23 ∷ Bx3-014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-014 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·014⟩ c4 = derive (Sw23 ∷ Bx3-014 ∷ []) (Bx2-014 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) ∷
   rw 0 (q13 c4) ∷
   rw 1 (q133 c4) ∷
   rw 2 (q134 c4) ∷
   rw 3 (q133 c4) ∷
   rw 4 (q13 c4) ∷
   rw 5 (q134 c4) ∷
   re 0 6 (Bx2-014 ∷ []) ∷ []) Eq.refl

private
  q135 : WsL → Eqn
  q135 c4 = eqn (Sw23 ∷ Bx3-014 ∷ []) (Bx2-014 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·014⟩ c4)

-- nat 2 BOX(0;3214): 8 steps
lem-nat-2-BOX⟨0·3214⟩ : WsL → ⟪ (Sw23 ∷ Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·3214⟩ c4 = derive (Sw23 ∷ Bx0-3214 ∷ []) (Bx0-2314 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ []) ∷
   rw⁻ 0 (q18 c4) ∷
   rw 1 (q19 c4) ∷
   rw 2 (q135 c4) ∷
   rw 3 (q19 c4) ∷
   rw⁻ 4 (q18 c4) ∷
   rw 5 (q135 c4) ∷
   re 0 6 (Bx0-2314 ∷ []) ∷ []) Eq.refl

private
  q136 : WsL → Eqn
  q136 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl0015 c4)

-- nat 2 SBOX(0;3;4;1): 3 steps
lem-nat-2-SBOX⟨0·3·4·1⟩ : WsL → ⟪ (Sw23 ∷ Sb0-3-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-4-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·3·4·1⟩ c4 = derive (Sw23 ∷ Sb0-3-4-1 ∷ []) (Sb0-2-4-1 ∷ Sw23 ∷ [])
  (re 1 1 (CS34 ∷ []) ∷
   rw⁻ 0 (q136 c4) ∷
   re 0 1 (Sb0-2-4-1 ∷ []) ∷ []) Eq.refl

private
  q137 : WsL → Eqn
  q137 c4 = eqn (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) (wl0016 c4)

-- nat 2 SBOXd(0;3;4;1): 3 steps
lem-nat-2-SBOXd⟨0·3·4·1⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻0-3-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-4-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·3·4·1⟩ c4 = derive (Sw23 ∷ Sb⁻0-3-4-1 ∷ []) (Sb⁻0-2-4-1 ∷ Sw23 ∷ [])
  (re 1 1 (CS34⁻ ∷ []) ∷
   rw⁻ 0 (q137 c4) ∷
   re 0 1 (Sb⁻0-2-4-1 ∷ []) ∷ []) Eq.refl

private
  q138 : WsL → Eqn
  q138 c4 = eqn (Sw23 ∷ Bx0-3214 ∷ []) (Bx0-2314 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3214⟩ c4)
  q139 : WsL → Eqn
  q139 c4 = eqn (Sw23 ∷ Toff412 ∷ []) (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4)
  q140 : WsL → Eqn
  q140 c4 = eqn (Sw23 ∷ Sb0-3-4-1 ∷ []) (Sb0-2-4-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·3·4·1⟩ c4)
  q141 : WsL → Eqn
  q141 c4 = eqn (Sw23 ∷ Sb⁻0-3-4-1 ∷ []) (Sb⁻0-2-4-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·3·4·1⟩ c4)

-- nat 2 SBOX(0;3;21;4): 7 steps
lem-nat-2-SBOX⟨0·3·21·4⟩ : WsL → ⟪ (Sw23 ∷ Sb0-3-21-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-31-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·3·21·4⟩ c4 = derive (Sw23 ∷ Sb0-3-21-4 ∷ []) (Sb0-2-31-4 ∷ Sw23 ∷ [])
  (re 1 1 (Bx0-3214 ∷ Toff412 ∷ Sb0-3-4-1 ∷ Toff412 ∷ Sb⁻0-3-4-1 ∷ []) ∷
   rw 0 (q138 c4) ∷
   rw 1 (q139 c4) ∷
   rw 2 (q140 c4) ∷
   rw 3 (q139 c4) ∷
   rw 4 (q141 c4) ∷
   re 0 5 (Sb0-2-31-4 ∷ []) ∷ []) Eq.refl

private
  q142 : WsL → Eqn
  q142 c4 = eqn (Sw34 ∷ CZ23 ∷ []) (CZ24 ∷ Sw34 ∷ []) (lem-nat-3-CZ23 c4)

-- nat 3 BOX(0;23): 3 steps
lem-nat-3-BOX⟨0·23⟩ : WsL → ⟪ (Sw34 ∷ Bx0-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-24 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·23⟩ c4 = derive (Sw34 ∷ Bx0-23 ∷ []) (Bx0-24 ∷ Sw34 ∷ [])
  (re 1 1 (CZ23 ∷ []) ∷
   rw 0 (q142 c4) ∷
   re 0 1 (Bx0-24 ∷ []) ∷ []) Eq.refl

private
  q143 : WsL → Eqn
  q143 c4 = eqn (Toff201 ∷ Sw34 ∷ []) (Sw34 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (Swap))
  q144 : WsL → Eqn
  q144 c4 = eqn (Sw34 ∷ Bx0-23 ∷ []) (Bx0-24 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·23⟩ c4)

-- nat 3 BOX(2;013): 8 steps
lem-nat-3-BOX⟨2·013⟩ : WsL → ⟪ (Sw34 ∷ Bx2-013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-014 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·013⟩ c4 = derive (Sw34 ∷ Bx2-013 ∷ []) (Bx2-014 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) ∷
   rw⁻ 0 (q100 c4) ∷
   rw⁻ 1 (q143 c4) ∷
   rw 2 (q144 c4) ∷
   rw⁻ 3 (q143 c4) ∷
   rw⁻ 4 (q100 c4) ∷
   rw 5 (q144 c4) ∷
   re 0 6 (Bx2-014 ∷ []) ∷ []) Eq.refl

private
  q145 : WsL → Eqn
  q145 c4 = eqn (Sw34 ∷ Toff024 ∷ []) (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4)
  q146 : WsL → Eqn
  q146 c4 = eqn (Sw34 ∷ Bx2-013 ∷ []) (Bx2-014 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·013⟩ c4)

-- nat 3 BOX(0;2413): 8 steps
lem-nat-3-BOX⟨0·2413⟩ : WsL → ⟪ (Sw34 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·2413⟩ c4 = derive (Sw34 ∷ Bx0-2413 ∷ []) (Bx0-2314 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-013 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ []) ∷
   rw 0 (q55 c4) ∷
   rw 1 (q145 c4) ∷
   rw 2 (q146 c4) ∷
   rw 3 (q145 c4) ∷
   rw 4 (q55 c4) ∷
   rw 5 (q146 c4) ∷
   re 0 6 (Bx0-2314 ∷ []) ∷ []) Eq.refl

private
  q147 : WsL → Eqn
  q147 c4 = eqn (Sw34 ∷ CS23 ∷ []) (CS24 ∷ Sw34 ∷ []) (lem-nat-3-CS23 c4)

-- nat 3 SBOX(0;2;3;1): 3 steps
lem-nat-3-SBOX⟨0·2·3·1⟩ : WsL → ⟪ (Sw34 ∷ Sb0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-4-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·2·3·1⟩ c4 = derive (Sw34 ∷ Sb0-2-3-1 ∷ []) (Sb0-2-4-1 ∷ Sw34 ∷ [])
  (re 1 1 (CS23 ∷ []) ∷
   rw 0 (q147 c4) ∷
   re 0 1 (Sb0-2-4-1 ∷ []) ∷ []) Eq.refl

private
  q148 : WsL → Eqn
  q148 c4 = eqn (Sw34 ∷ CS23⁻ ∷ []) (CS24⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd23 c4)

-- nat 3 SBOXd(0;2;3;1): 3 steps
lem-nat-3-SBOXd⟨0·2·3·1⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-4-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·2·3·1⟩ c4 = derive (Sw34 ∷ Sb⁻0-2-3-1 ∷ []) (Sb⁻0-2-4-1 ∷ Sw34 ∷ [])
  (re 1 1 (CS23⁻ ∷ []) ∷
   rw 0 (q148 c4) ∷
   re 0 1 (Sb⁻0-2-4-1 ∷ []) ∷ []) Eq.refl

private
  q149 : WsL → Eqn
  q149 c4 = eqn (Sw34 ∷ Bx0-2413 ∷ []) (Bx0-2314 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2413⟩ c4)
  q150 : WsL → Eqn
  q150 c4 = eqn (Sw34 ∷ Toff314 ∷ []) (Toff413 ∷ Sw34 ∷ []) (wl0142 c4)
  q151 : WsL → Eqn
  q151 c4 = eqn (Sw34 ∷ Sb0-2-3-1 ∷ []) (Sb0-2-4-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·2·3·1⟩ c4)
  q152 : WsL → Eqn
  q152 c4 = eqn (Sw34 ∷ Sb⁻0-2-3-1 ∷ []) (Sb⁻0-2-4-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·2·3·1⟩ c4)

-- nat 3 SBOX(0;2;41;3): 7 steps
lem-nat-3-SBOX⟨0·2·41·3⟩ : WsL → ⟪ (Sw34 ∷ Sb0-2-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-31-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·2·41·3⟩ c4 = derive (Sw34 ∷ Sb0-2-41-3 ∷ []) (Sb0-2-31-4 ∷ Sw34 ∷ [])
  (re 1 1 (Bx0-2413 ∷ Toff314 ∷ Sb0-2-3-1 ∷ Toff314 ∷ Sb⁻0-2-3-1 ∷ []) ∷
   rw 0 (q149 c4) ∷
   rw 1 (q150 c4) ∷
   rw 2 (q151 c4) ∷
   rw 3 (q150 c4) ∷
   rw 4 (q152 c4) ∷
   re 0 5 (Sb0-2-31-4 ∷ []) ∷ []) Eq.refl

private
  q153 : WsL → Eqn
  q153 c4 = eqn (Sw34 ∷ Bx0-24 ∷ []) (Bx0-23 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·24⟩ c4)

-- nat 3 BOX(2;014): 8 steps
lem-nat-3-BOX⟨2·014⟩ : WsL → ⟪ (Sw34 ∷ Bx2-014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-013 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·014⟩ c4 = derive (Sw34 ∷ Bx2-014 ∷ []) (Bx2-013 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) ∷
   rw⁻ 0 (q100 c4) ∷
   rw⁻ 1 (q143 c4) ∷
   rw 2 (q153 c4) ∷
   rw⁻ 3 (q143 c4) ∷
   rw⁻ 4 (q100 c4) ∷
   rw 5 (q153 c4) ∷
   re 0 6 (Bx2-013 ∷ []) ∷ []) Eq.refl

private
  q154 : WsL → Eqn
  q154 c4 = eqn (Sw34 ∷ CCZ023 ∷ []) (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4)
  q155 : WsL → Eqn
  q155 c4 = eqn (Sw34 ∷ Toff023 ∷ []) (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4)
  q156 : WsL → Eqn
  q156 c4 = eqn (Sw34 ∷ Bx2-014 ∷ []) (Bx2-013 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·014⟩ c4)

-- nat 3 BOX(0;2314): 8 steps
lem-nat-3-BOX⟨0·2314⟩ : WsL → ⟪ (Sw34 ∷ Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·2314⟩ c4 = derive (Sw34 ∷ Bx0-2314 ∷ []) (Bx0-2413 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) ∷
   rw 0 (q154 c4) ∷
   rw 1 (q155 c4) ∷
   rw 2 (q156 c4) ∷
   rw 3 (q155 c4) ∷
   rw 4 (q154 c4) ∷
   rw 5 (q156 c4) ∷
   re 0 6 (Bx0-2413 ∷ []) ∷ []) Eq.refl

private
  q157 : WsL → Eqn
  q157 c4 = eqn (Sw34 ∷ CS24 ∷ []) (CS23 ∷ Sw34 ∷ []) (lem-nat-3-CS24 c4)

-- nat 3 SBOX(0;2;4;1): 3 steps
lem-nat-3-SBOX⟨0·2·4·1⟩ : WsL → ⟪ (Sw34 ∷ Sb0-2-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-3-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·2·4·1⟩ c4 = derive (Sw34 ∷ Sb0-2-4-1 ∷ []) (Sb0-2-3-1 ∷ Sw34 ∷ [])
  (re 1 1 (CS24 ∷ []) ∷
   rw 0 (q157 c4) ∷
   re 0 1 (Sb0-2-3-1 ∷ []) ∷ []) Eq.refl

private
  q158 : WsL → Eqn
  q158 c4 = eqn (Sw34 ∷ CS24⁻ ∷ []) (CS23⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd24 c4)

-- nat 3 SBOXd(0;2;4;1): 3 steps
lem-nat-3-SBOXd⟨0·2·4·1⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻0-2-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-3-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·2·4·1⟩ c4 = derive (Sw34 ∷ Sb⁻0-2-4-1 ∷ []) (Sb⁻0-2-3-1 ∷ Sw34 ∷ [])
  (re 1 1 (CS24⁻ ∷ []) ∷
   rw 0 (q158 c4) ∷
   re 0 1 (Sb⁻0-2-3-1 ∷ []) ∷ []) Eq.refl

private
  q159 : WsL → Eqn
  q159 c4 = eqn (Sw34 ∷ Bx0-2314 ∷ []) (Bx0-2413 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·2314⟩ c4)
  q160 : WsL → Eqn
  q160 c4 = eqn (Sw34 ∷ Toff413 ∷ []) (Toff314 ∷ Sw34 ∷ []) (wl0141 c4)
  q161 : WsL → Eqn
  q161 c4 = eqn (Sw34 ∷ Sb0-2-4-1 ∷ []) (Sb0-2-3-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·2·4·1⟩ c4)
  q162 : WsL → Eqn
  q162 c4 = eqn (Sw34 ∷ Sb⁻0-2-4-1 ∷ []) (Sb⁻0-2-3-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·2·4·1⟩ c4)

-- nat 3 SBOX(0;2;31;4): 7 steps
lem-nat-3-SBOX⟨0·2·31·4⟩ : WsL → ⟪ (Sw34 ∷ Sb0-2-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-41-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·2·31·4⟩ c4 = derive (Sw34 ∷ Sb0-2-31-4 ∷ []) (Sb0-2-41-3 ∷ Sw34 ∷ [])
  (re 1 1 (Bx0-2314 ∷ Toff413 ∷ Sb0-2-4-1 ∷ Toff413 ∷ Sb⁻0-2-4-1 ∷ []) ∷
   rw 0 (q159 c4) ∷
   rw 1 (q160 c4) ∷
   rw 2 (q161 c4) ∷
   rw 3 (q160 c4) ∷
   rw 4 (q162 c4) ∷
   re 0 5 (Sb0-2-41-3 ∷ []) ∷ []) Eq.refl

private
  q163 : WsL → Eqn
  q163 c4 = eqn (CCZ012 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ012 ∷ []) (wl0096 c4)
  q164 : WsL → Eqn
  q164 c4 = eqn (Sw01 ∷ Bx1-23 ∷ []) (Bx0-23 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·23⟩ c4)

-- nat 0 BOX(2;103): 8 steps
lem-nat-0-BOX⟨2·103⟩ : WsL → ⟪ (Sw01 ∷ Bx2-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-013 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·103⟩ c4 = derive (Sw01 ∷ Bx2-103 ∷ []) (Bx2-013 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-23 ∷ Toff201 ∷ CCZ012 ∷ Bx1-23 ∷ []) ∷
   rw⁻ 0 (q163 c4) ∷
   rw 1 (q64 c4) ∷
   rw 2 (q164 c4) ∷
   rw 3 (q64 c4) ∷
   rw⁻ 4 (q163 c4) ∷
   rw 5 (q164 c4) ∷
   re 0 6 (Bx2-013 ∷ []) ∷ []) Eq.refl

private
  q165 : WsL → Eqn
  q165 c4 = eqn (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4)
  q166 : WsL → Eqn
  q166 c4 = eqn (Sw01 ∷ Toff124 ∷ []) (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4)
  q167 : WsL → Eqn
  q167 c4 = eqn (Sw01 ∷ Bx2-103 ∷ []) (Bx2-013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·103⟩ c4)

-- nat 0 BOX(1;2403): 8 steps
lem-nat-0-BOX⟨1·2403⟩ : WsL → ⟪ (Sw01 ∷ Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·2403⟩ c4 = derive (Sw01 ∷ Bx1-2403 ∷ []) (Bx0-2413 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-103 ∷ Toff124 ∷ CCZ124 ∷ Bx2-103 ∷ []) ∷
   rw 0 (q165 c4) ∷
   rw 1 (q166 c4) ∷
   rw 2 (q167 c4) ∷
   rw 3 (q166 c4) ∷
   rw 4 (q165 c4) ∷
   rw 5 (q167 c4) ∷
   re 0 6 (Bx0-2413 ∷ []) ∷ []) Eq.refl

private
  q168 : WsL → Eqn
  q168 c4 = eqn (Sw01 ∷ Sb1-2-3-0 ∷ []) (Sb1-2-3-0 ∷ Sw01 ∷ []) (c₂ (Swap) (CS))

-- nat 0 SBOX(1;2;3;0): 2 steps
lem-nat-0-SBOX⟨1·2·3·0⟩ : WsL → ⟪ (Sw01 ∷ Sb1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·2·3·0⟩ c4 = derive (Sw01 ∷ Sb1-2-3-0 ∷ []) (Sb0-2-3-1 ∷ Sw01 ∷ [])
  (rw 0 (q168 c4) ∷
   re 0 1 (Sb0-2-3-1 ∷ []) ∷ []) Eq.refl

private
  q169 : WsL → Eqn
  q169 c4 = eqn (Sw01 ∷ Sb⁻1-2-3-0 ∷ []) (Sb⁻1-2-3-0 ∷ Sw01 ∷ []) (c₂ (Swap) (CS • CS • CS))

-- nat 0 SBOXd(1;2;3;0): 2 steps
lem-nat-0-SBOXd⟨1·2·3·0⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·2·3·0⟩ c4 = derive (Sw01 ∷ Sb⁻1-2-3-0 ∷ []) (Sb⁻0-2-3-1 ∷ Sw01 ∷ [])
  (rw 0 (q169 c4) ∷
   re 0 1 (Sb⁻0-2-3-1 ∷ []) ∷ []) Eq.refl

private
  q170 : WsL → Eqn
  q170 c4 = eqn (Sw01 ∷ Bx1-2403 ∷ []) (Bx0-2413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2403⟩ c4)
  q171 : WsL → Eqn
  q171 c4 = eqn (Sw01 ∷ Toff304 ∷ []) (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4)
  q172 : WsL → Eqn
  q172 c4 = eqn (Sw01 ∷ Sb1-2-3-0 ∷ []) (Sb0-2-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·3·0⟩ c4)
  q173 : WsL → Eqn
  q173 c4 = eqn (Sw01 ∷ Sb⁻1-2-3-0 ∷ []) (Sb⁻0-2-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·2·3·0⟩ c4)

-- nat 0 SBOX(1;2;40;3): 7 steps
lem-nat-0-SBOX⟨1·2·40·3⟩ : WsL → ⟪ (Sw01 ∷ Sb1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-41-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·2·40·3⟩ c4 = derive (Sw01 ∷ Sb1-2-40-3 ∷ []) (Sb0-2-41-3 ∷ Sw01 ∷ [])
  (re 1 1 (Bx1-2403 ∷ Toff304 ∷ Sb1-2-3-0 ∷ Toff304 ∷ Sb⁻1-2-3-0 ∷ []) ∷
   rw 0 (q170 c4) ∷
   rw 1 (q171 c4) ∷
   rw 2 (q172 c4) ∷
   rw 3 (q171 c4) ∷
   rw 4 (q173 c4) ∷
   re 0 5 (Sb0-2-41-3 ∷ []) ∷ []) Eq.refl

private
  q174 : WsL → Eqn
  q174 c4 = eqn (Sw01 ∷ Bx0-23 ∷ []) (Bx1-23 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·23⟩ c4)

-- nat 0 BOX(2;013): 8 steps
lem-nat-0-BOX⟨2·013⟩ : WsL → ⟪ (Sw01 ∷ Bx2-013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-103 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·013⟩ c4 = derive (Sw01 ∷ Bx2-013 ∷ []) (Bx2-103 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) ∷
   rw⁻ 0 (q163 c4) ∷
   rw 1 (q64 c4) ∷
   rw 2 (q174 c4) ∷
   rw 3 (q64 c4) ∷
   rw⁻ 4 (q163 c4) ∷
   rw 5 (q174 c4) ∷
   re 0 6 (Bx2-103 ∷ []) ∷ []) Eq.refl

private
  q175 : WsL → Eqn
  q175 c4 = eqn (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4)
  q176 : WsL → Eqn
  q176 c4 = eqn (Sw01 ∷ Toff024 ∷ []) (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4)
  q177 : WsL → Eqn
  q177 c4 = eqn (Sw01 ∷ Bx2-013 ∷ []) (Bx2-103 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·013⟩ c4)

-- nat 0 BOX(0;2413): 8 steps
lem-nat-0-BOX⟨0·2413⟩ : WsL → ⟪ (Sw01 ∷ Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·2413⟩ c4 = derive (Sw01 ∷ Bx0-2413 ∷ []) (Bx1-2403 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-013 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ []) ∷
   rw 0 (q175 c4) ∷
   rw 1 (q176 c4) ∷
   rw 2 (q177 c4) ∷
   rw 3 (q176 c4) ∷
   rw 4 (q175 c4) ∷
   rw 5 (q177 c4) ∷
   re 0 6 (Bx1-2403 ∷ []) ∷ []) Eq.refl

private
  q178 : WsL → Eqn
  q178 c4 = eqn (Sw01 ∷ Sb0-2-3-1 ∷ []) (Sb0-2-3-1 ∷ Sw01 ∷ []) (c₂ (Swap) (CS))

-- nat 0 SBOX(0;2;3;1): 2 steps
lem-nat-0-SBOX⟨0·2·3·1⟩ : WsL → ⟪ (Sw01 ∷ Sb0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-3-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·2·3·1⟩ c4 = derive (Sw01 ∷ Sb0-2-3-1 ∷ []) (Sb1-2-3-0 ∷ Sw01 ∷ [])
  (rw 0 (q178 c4) ∷
   re 0 1 (Sb1-2-3-0 ∷ []) ∷ []) Eq.refl

private
  q179 : WsL → Eqn
  q179 c4 = eqn (Sw01 ∷ Sb⁻0-2-3-1 ∷ []) (Sb⁻0-2-3-1 ∷ Sw01 ∷ []) (c₂ (Swap) (CS • CS • CS))

-- nat 0 SBOXd(0;2;3;1): 2 steps
lem-nat-0-SBOXd⟨0·2·3·1⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-3-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·2·3·1⟩ c4 = derive (Sw01 ∷ Sb⁻0-2-3-1 ∷ []) (Sb⁻1-2-3-0 ∷ Sw01 ∷ [])
  (rw 0 (q179 c4) ∷
   re 0 1 (Sb⁻1-2-3-0 ∷ []) ∷ []) Eq.refl

private
  q180 : WsL → Eqn
  q180 c4 = eqn (Sw01 ∷ Bx0-2413 ∷ []) (Bx1-2403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2413⟩ c4)
  q181 : WsL → Eqn
  q181 c4 = eqn (Sw01 ∷ Toff314 ∷ []) (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4)
  q182 : WsL → Eqn
  q182 c4 = eqn (Sw01 ∷ Sb0-2-3-1 ∷ []) (Sb1-2-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·3·1⟩ c4)
  q183 : WsL → Eqn
  q183 c4 = eqn (Sw01 ∷ Sb⁻0-2-3-1 ∷ []) (Sb⁻1-2-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·2·3·1⟩ c4)

-- nat 0 SBOX(0;2;41;3): 7 steps
lem-nat-0-SBOX⟨0·2·41·3⟩ : WsL → ⟪ (Sw01 ∷ Sb0-2-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-40-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·2·41·3⟩ c4 = derive (Sw01 ∷ Sb0-2-41-3 ∷ []) (Sb1-2-40-3 ∷ Sw01 ∷ [])
  (re 1 1 (Bx0-2413 ∷ Toff314 ∷ Sb0-2-3-1 ∷ Toff314 ∷ Sb⁻0-2-3-1 ∷ []) ∷
   rw 0 (q180 c4) ∷
   rw 1 (q181 c4) ∷
   rw 2 (q182 c4) ∷
   rw 3 (q181 c4) ∷
   rw 4 (q183 c4) ∷
   re 0 5 (Sb1-2-40-3 ∷ []) ∷ []) Eq.refl

-- comm CX20 CCZ134: 23 steps
lem-comm-CX20-CCZ134 : WsL → ⟪ (CX20 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CX20 ∷ []) ⟫ʷ
lem-comm-CX20-CCZ134 c4 = derive (CX20 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX20 ∷ [])
  (re 1 1 (Sw23 ∷ Sw34 ∷ CCZ123 ∷ Sw34 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q30 c4) ∷
   re 1 3 (CX30 ∷ []) ∷
   rw⁻ 1 (q108 c4) ∷
   re 2 3 (CX40 ∷ []) ∷
   re 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 10 (q108 c4) ∷
   re 8 3 (CCZ124 ∷ []) ∷
   rw⁻ 9 (q30 c4) ∷
   re 7 3 (CCZ134 ∷ []) ∷
   rw⁻ 6 (q46 c4) ∷
   rw 5 (q109 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   re 4 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 3 (q30 c4) ∷
   re 3 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   rw 2 (q108 c4) ∷
   re 3 7 (CX40 ∷ []) ∷
   re 3 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) ∷
   rw 5 (q108 c4) ∷
   re 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 6 (q30 c4) ∷
   re 0 5 (CCZ134 ∷ []) ∷ []) Eq.refl

private
  q184 : WsL → Eqn
  q184 c4 = eqn (Sw01 ∷ CS14 ∷ []) (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 c4)

-- nat 0 SBOX(0;1;4;2): 3 steps
lem-nat-0-SBOX⟨0·1·4·2⟩ : WsL → ⟪ (Sw01 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-4-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·1·4·2⟩ c4 = derive (Sw01 ∷ Sb0-1-4-2 ∷ []) (Sb1-0-4-2 ∷ Sw01 ∷ [])
  (re 1 1 (CS14 ∷ []) ∷
   rw 0 (q184 c4) ∷
   re 0 1 (Sb1-0-4-2 ∷ []) ∷ []) Eq.refl

private
  q185 : WsL → Eqn
  q185 c4 = eqn (Sw01 ∷ CS14⁻ ∷ []) (CS04⁻ ∷ Sw01 ∷ []) (lem-nat-0-CSd14 c4)

-- nat 0 SBOXd(0;1;4;2): 3 steps
lem-nat-0-SBOXd⟨0·1·4·2⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-4-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·1·4·2⟩ c4 = derive (Sw01 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻1-0-4-2 ∷ Sw01 ∷ [])
  (re 1 1 (CS14⁻ ∷ []) ∷
   rw 0 (q185 c4) ∷
   re 0 1 (Sb⁻1-0-4-2 ∷ []) ∷ []) Eq.refl

private
  q186 : WsL → Eqn
  q186 c4 = eqn (Sw01 ∷ Bx0-1324 ∷ []) (Bx1-0324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1324⟩ c4)
  q187 : WsL → Eqn
  q187 c4 = eqn (Sw01 ∷ Toff423 ∷ []) (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ))
  q188 : WsL → Eqn
  q188 c4 = eqn (Sw01 ∷ Sb0-1-4-2 ∷ []) (Sb1-0-4-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·4·2⟩ c4)
  q189 : WsL → Eqn
  q189 c4 = eqn (Sw01 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻1-0-4-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·4·2⟩ c4)

-- nat 0 SBOX(0;1;32;4): 7 steps
lem-nat-0-SBOX⟨0·1·32·4⟩ : WsL → ⟪ (Sw01 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-32-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·1·32·4⟩ c4 = derive (Sw01 ∷ Sb0-1-32-4 ∷ []) (Sb1-0-32-4 ∷ Sw01 ∷ [])
  (re 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) ∷
   rw 0 (q186 c4) ∷
   rw 1 (q187 c4) ∷
   rw 2 (q188 c4) ∷
   rw 3 (q187 c4) ∷
   rw 4 (q189 c4) ∷
   re 0 5 (Sb1-0-32-4 ∷ []) ∷ []) Eq.refl

private
  q190 : WsL → Eqn
  q190 c4 = eqn (Sw01 ∷ Bx4-01 ∷ []) (Bx4-10 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·01⟩ c4)

-- nat 0 BOX(0;421): 8 steps
lem-nat-0-BOX⟨0·421⟩ : WsL → ⟪ (Sw01 ∷ Bx0-421 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-420 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·421⟩ c4 = derive (Sw01 ∷ Bx0-421 ∷ []) (Bx1-420 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ []) ∷
   rw 0 (q175 c4) ∷
   rw 1 (q176 c4) ∷
   rw 2 (q190 c4) ∷
   rw 3 (q176 c4) ∷
   rw 4 (q175 c4) ∷
   rw 5 (q190 c4) ∷
   re 0 6 (Bx1-420 ∷ []) ∷ []) Eq.refl

private
  q191 : WsL → Eqn
  q191 c4 = eqn (Sw01 ∷ CCZ034 ∷ []) (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4)
  q192 : WsL → Eqn
  q192 c4 = eqn (Sw01 ∷ Toff403 ∷ []) (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4)
  q193 : WsL → Eqn
  q193 c4 = eqn (Sw01 ∷ Bx0-421 ∷ []) (Bx1-420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·421⟩ c4)

-- nat 0 BOX(4;0321): 8 steps
lem-nat-0-BOX⟨4·0321⟩ : WsL → ⟪ (Sw01 ∷ Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·0321⟩ c4 = derive (Sw01 ∷ Bx4-0321 ∷ []) (Bx4-1320 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-421 ∷ Toff403 ∷ CCZ034 ∷ Bx0-421 ∷ []) ∷
   rw 0 (q191 c4) ∷
   rw 1 (q192 c4) ∷
   rw 2 (q193 c4) ∷
   rw 3 (q192 c4) ∷
   rw 4 (q191 c4) ∷
   rw 5 (q193 c4) ∷
   re 0 6 (Bx4-1320 ∷ []) ∷ []) Eq.refl

private
  q194 : WsL → Eqn
  q194 c4 = eqn (CS01 ∷ Sw01 ∷ []) (Sw01 ∷ CS01 ∷ []) (wl0132 c4)

-- nat 0 SBOX(4;0;1;2): 3 steps
lem-nat-0-SBOX⟨4·0·1·2⟩ : WsL → ⟪ (Sw01 ∷ Sb4-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-0-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨4·0·1·2⟩ c4 = derive (Sw01 ∷ Sb4-0-1-2 ∷ []) (Sb4-1-0-2 ∷ Sw01 ∷ [])
  (re 1 1 (CS01 ∷ []) ∷
   rw⁻ 0 (q194 c4) ∷
   re 0 1 (Sb4-1-0-2 ∷ []) ∷ []) Eq.refl

private
  q195 : WsL → Eqn
  q195 c4 = eqn (CS01⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS01⁻ ∷ []) (wl0133 c4)

-- nat 0 SBOXd(4;0;1;2): 3 steps
lem-nat-0-SBOXd⟨4·0·1·2⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻4-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-1-0-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨4·0·1·2⟩ c4 = derive (Sw01 ∷ Sb⁻4-0-1-2 ∷ []) (Sb⁻4-1-0-2 ∷ Sw01 ∷ [])
  (re 1 1 (CS01⁻ ∷ []) ∷
   rw⁻ 0 (q195 c4) ∷
   re 0 1 (Sb⁻4-1-0-2 ∷ []) ∷ []) Eq.refl

private
  q196 : WsL → Eqn
  q196 c4 = eqn (Sw01 ∷ Bx4-0321 ∷ []) (Bx4-1320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0321⟩ c4)
  q197 : WsL → Eqn
  q197 c4 = eqn (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) (wl0053 c4)
  q198 : WsL → Eqn
  q198 c4 = eqn (Sw01 ∷ Sb4-0-1-2 ∷ []) (Sb4-1-0-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨4·0·1·2⟩ c4)
  q199 : WsL → Eqn
  q199 c4 = eqn (Sw01 ∷ Sb⁻4-0-1-2 ∷ []) (Sb⁻4-1-0-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨4·0·1·2⟩ c4)

-- nat 0 SBOX(4;0;32;1): 7 steps
lem-nat-0-SBOX⟨4·0·32·1⟩ : WsL → ⟪ (Sw01 ∷ Sb4-0-32-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-32-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨4·0·32·1⟩ c4 = derive (Sw01 ∷ Sb4-0-32-1 ∷ []) (Sb4-1-32-0 ∷ Sw01 ∷ [])
  (re 1 1 (Bx4-0321 ∷ Toff123 ∷ Sb4-0-1-2 ∷ Toff123 ∷ Sb⁻4-0-1-2 ∷ []) ∷
   rw 0 (q196 c4) ∷
   rw 1 (q197 c4) ∷
   rw 2 (q198 c4) ∷
   rw 3 (q197 c4) ∷
   rw 4 (q199 c4) ∷
   re 0 5 (Sb4-1-32-0 ∷ []) ∷ []) Eq.refl

private
  q200 : WsL → Eqn
  q200 c4 = eqn (Sw34 ∷ Toff013 ∷ []) (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4)
  q201 : WsL → Eqn
  q201 c4 = eqn (Sw34 ∷ Bx3-04 ∷ []) (Bx4-03 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·04⟩ c4)

-- nat 3 BOX(0;314): 8 steps
lem-nat-3-BOX⟨0·314⟩ : WsL → ⟪ (Sw34 ∷ Bx0-314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-413 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·314⟩ c4 = derive (Sw34 ∷ Bx0-314 ∷ []) (Bx0-413 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) ∷
   rw 0 (q106 c4) ∷
   rw 1 (q200 c4) ∷
   rw 2 (q201 c4) ∷
   rw 3 (q200 c4) ∷
   rw 4 (q106 c4) ∷
   rw 5 (q201 c4) ∷
   re 0 6 (Bx0-413 ∷ []) ∷ []) Eq.refl

private
  q202 : WsL → Eqn
  q202 c4 = eqn (Sw34 ∷ Toff302 ∷ []) (Toff402 ∷ Sw34 ∷ []) (lem-nat-3-TOFF302 c4)
  q203 : WsL → Eqn
  q203 c4 = eqn (Sw34 ∷ Bx0-314 ∷ []) (Bx0-413 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·314⟩ c4)

-- nat 3 BOX(3;0214): 8 steps
lem-nat-3-BOX⟨3·0214⟩ : WsL → ⟪ (Sw34 ∷ Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·0214⟩ c4 = derive (Sw34 ∷ Bx3-0214 ∷ []) (Bx4-0213 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ []) ∷
   rw 0 (q154 c4) ∷
   rw 1 (q202 c4) ∷
   rw 2 (q203 c4) ∷
   rw 3 (q202 c4) ∷
   rw 4 (q154 c4) ∷
   rw 5 (q203 c4) ∷
   re 0 6 (Bx4-0213 ∷ []) ∷ []) Eq.refl

private
  q204 : WsL → Eqn
  q204 c4 = eqn (CZ03 ∷ Sw12 ∷ []) (Sw12 ∷ CZ03 ∷ []) (wl0098 c4)

-- nat 1 BOX(4;03): 3 steps
lem-nat-1-BOX⟨4·03⟩ : WsL → ⟪ (Sw12 ∷ Bx4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-03 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·03⟩ c4 = derive (Sw12 ∷ Bx4-03 ∷ []) (Bx4-03 ∷ Sw12 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw⁻ 0 (q204 c4) ∷
   re 0 1 (Bx4-03 ∷ []) ∷ []) Eq.refl

private
  q205 : WsL → Eqn
  q205 c4 = eqn (Sw12 ∷ CCZ014 ∷ []) (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4)
  q206 : WsL → Eqn
  q206 c4 = eqn (Sw12 ∷ Toff014 ∷ []) (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4)
  q207 : WsL → Eqn
  q207 c4 = eqn (Sw12 ∷ Bx4-03 ∷ []) (Bx4-03 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·03⟩ c4)

-- nat 1 BOX(0;413): 8 steps
lem-nat-1-BOX⟨0·413⟩ : WsL → ⟪ (Sw12 ∷ Bx0-413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-423 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·413⟩ c4 = derive (Sw12 ∷ Bx0-413 ∷ []) (Bx0-423 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ CCZ014 ∷ Bx4-03 ∷ []) ∷
   rw 0 (q205 c4) ∷
   rw 1 (q206 c4) ∷
   rw 2 (q207 c4) ∷
   rw 3 (q206 c4) ∷
   rw 4 (q205 c4) ∷
   rw 5 (q207 c4) ∷
   re 0 6 (Bx0-423 ∷ []) ∷ []) Eq.refl

private
  q208 : WsL → Eqn
  q208 c4 = eqn (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4)
  q209 : WsL → Eqn
  q209 c4 = eqn (Sw12 ∷ Toff402 ∷ []) (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4)
  q210 : WsL → Eqn
  q210 c4 = eqn (Sw12 ∷ Bx0-413 ∷ []) (Bx0-423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·413⟩ c4)

-- nat 1 BOX(4;0213): 8 steps
lem-nat-1-BOX⟨4·0213⟩ : WsL → ⟪ (Sw12 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·0213⟩ c4 = derive (Sw12 ∷ Bx4-0213 ∷ []) (Bx4-0123 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-413 ∷ Toff402 ∷ CCZ024 ∷ Bx0-413 ∷ []) ∷
   rw 0 (q208 c4) ∷
   rw 1 (q209 c4) ∷
   rw 2 (q210 c4) ∷
   rw 3 (q209 c4) ∷
   rw 4 (q208 c4) ∷
   rw 5 (q210 c4) ∷
   re 0 6 (Bx4-0123 ∷ []) ∷ []) Eq.refl

private
  q211 : WsL → Eqn
  q211 c4 = eqn (Sw23 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4)
  q212 : WsL → Eqn
  q212 c4 = eqn (Sw23 ∷ Toff014 ∷ []) (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4)
  q213 : WsL → Eqn
  q213 c4 = eqn (Sw23 ∷ Bx4-02 ∷ []) (Bx4-03 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·02⟩ c4)

-- nat 2 BOX(0;412): 8 steps
lem-nat-2-BOX⟨0·412⟩ : WsL → ⟪ (Sw23 ∷ Bx0-412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-413 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·412⟩ c4 = derive (Sw23 ∷ Bx0-412 ∷ []) (Bx0-413 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) ∷
   rw 0 (q211 c4) ∷
   rw 1 (q212 c4) ∷
   rw 2 (q213 c4) ∷
   rw 3 (q212 c4) ∷
   rw 4 (q211 c4) ∷
   rw 5 (q213 c4) ∷
   re 0 6 (Bx0-413 ∷ []) ∷ []) Eq.refl

private
  q214 : WsL → Eqn
  q214 c4 = eqn (Sw23 ∷ Toff403 ∷ []) (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4)
  q215 : WsL → Eqn
  q215 c4 = eqn (Sw23 ∷ Bx0-412 ∷ []) (Bx0-413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·412⟩ c4)

-- nat 2 BOX(4;0312): 8 steps
lem-nat-2-BOX⟨4·0312⟩ : WsL → ⟪ (Sw23 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·0312⟩ c4 = derive (Sw23 ∷ Bx4-0312 ∷ []) (Bx4-0213 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-412 ∷ Toff403 ∷ CCZ034 ∷ Bx0-412 ∷ []) ∷
   rw 0 (q16 c4) ∷
   rw 1 (q214 c4) ∷
   rw 2 (q215 c4) ∷
   rw 3 (q214 c4) ∷
   rw 4 (q16 c4) ∷
   rw 5 (q215 c4) ∷
   re 0 6 (Bx4-0213 ∷ []) ∷ []) Eq.refl

private
  q216 : WsL → Eqn
  q216 c4 = eqn (Sw12 ∷ Toff024 ∷ []) (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4)
  q217 : WsL → Eqn
  q217 c4 = eqn (Sw12 ∷ Bx4-01 ∷ []) (Bx4-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·01⟩ c4)

-- nat 1 BOX(0;421): 8 steps
lem-nat-1-BOX⟨0·421⟩ : WsL → ⟪ (Sw12 ∷ Bx0-421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-412 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·421⟩ c4 = derive (Sw12 ∷ Bx0-421 ∷ []) (Bx0-412 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ []) ∷
   rw 0 (q208 c4) ∷
   rw 1 (q216 c4) ∷
   rw 2 (q217 c4) ∷
   rw 3 (q216 c4) ∷
   rw 4 (q208 c4) ∷
   rw 5 (q217 c4) ∷
   re 0 6 (Bx0-412 ∷ []) ∷ []) Eq.refl

private
  q218 : WsL → Eqn
  q218 c4 = eqn (Sw12 ∷ Bx0-421 ∷ []) (Bx0-412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·421⟩ c4)

-- nat 1 BOX(4;0321): 8 steps
lem-nat-1-BOX⟨4·0321⟩ : WsL → ⟪ (Sw12 ∷ Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·0321⟩ c4 = derive (Sw12 ∷ Bx4-0321 ∷ []) (Bx4-0312 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-421 ∷ Toff403 ∷ CCZ034 ∷ Bx0-421 ∷ []) ∷
   rw 0 (q27 c4) ∷
   rw 1 (q40 c4) ∷
   rw 2 (q218 c4) ∷
   rw 3 (q40 c4) ∷
   rw 4 (q27 c4) ∷
   rw 5 (q218 c4) ∷
   re 0 6 (Bx4-0312 ∷ []) ∷ []) Eq.refl

private
  q219 : WsL → Eqn
  q219 c4 = eqn (Sw01 ∷ Bx4-10 ∷ []) (Bx4-01 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·10⟩ c4)

-- nat 0 BOX(1;420): 8 steps
lem-nat-0-BOX⟨1·420⟩ : WsL → ⟪ (Sw01 ∷ Bx1-420 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-421 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·420⟩ c4 = derive (Sw01 ∷ Bx1-420 ∷ []) (Bx0-421 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) ∷
   rw 0 (q165 c4) ∷
   rw 1 (q166 c4) ∷
   rw 2 (q219 c4) ∷
   rw 3 (q166 c4) ∷
   rw 4 (q165 c4) ∷
   rw 5 (q219 c4) ∷
   re 0 6 (Bx0-421 ∷ []) ∷ []) Eq.refl

private
  q220 : WsL → Eqn
  q220 c4 = eqn (Sw01 ∷ CCZ134 ∷ []) (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4)
  q221 : WsL → Eqn
  q221 c4 = eqn (Sw01 ∷ Toff413 ∷ []) (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4)
  q222 : WsL → Eqn
  q222 c4 = eqn (Sw01 ∷ Bx1-420 ∷ []) (Bx0-421 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·420⟩ c4)

-- nat 0 BOX(4;1320): 8 steps
lem-nat-0-BOX⟨4·1320⟩ : WsL → ⟪ (Sw01 ∷ Bx4-1320 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0321 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·1320⟩ c4 = derive (Sw01 ∷ Bx4-1320 ∷ []) (Bx4-0321 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff413 ∷ Bx1-420 ∷ Toff413 ∷ CCZ134 ∷ Bx1-420 ∷ []) ∷
   rw 0 (q220 c4) ∷
   rw 1 (q221 c4) ∷
   rw 2 (q222 c4) ∷
   rw 3 (q221 c4) ∷
   rw 4 (q220 c4) ∷
   rw 5 (q222 c4) ∷
   re 0 6 (Bx4-0321 ∷ []) ∷ []) Eq.refl

-- nat 1 BOX(0;423): 8 steps
lem-nat-1-BOX⟨0·423⟩ : WsL → ⟪ (Sw12 ∷ Bx0-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-413 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·423⟩ c4 = derive (Sw12 ∷ Bx0-423 ∷ []) (Bx0-413 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) ∷
   rw 0 (q208 c4) ∷
   rw 1 (q216 c4) ∷
   rw 2 (q207 c4) ∷
   rw 3 (q216 c4) ∷
   rw 4 (q208 c4) ∷
   rw 5 (q207 c4) ∷
   re 0 6 (Bx0-413 ∷ []) ∷ []) Eq.refl

private
  q223 : WsL → Eqn
  q223 c4 = eqn (Sw12 ∷ Toff401 ∷ []) (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4)
  q224 : WsL → Eqn
  q224 c4 = eqn (Sw12 ∷ Bx0-423 ∷ []) (Bx0-413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·423⟩ c4)

-- nat 1 BOX(4;0123): 8 steps
lem-nat-1-BOX⟨4·0123⟩ : WsL → ⟪ (Sw12 ∷ Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·0123⟩ c4 = derive (Sw12 ∷ Bx4-0123 ∷ []) (Bx4-0213 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) ∷
   rw 0 (q205 c4) ∷
   rw 1 (q223 c4) ∷
   rw 2 (q224 c4) ∷
   rw 3 (q223 c4) ∷
   rw 4 (q205 c4) ∷
   rw 5 (q224 c4) ∷
   re 0 6 (Bx4-0213 ∷ []) ∷ []) Eq.refl

private
  q225 : WsL → Eqn
  q225 c4 = eqn (CZ13 ∷ Sw01 ∷ []) (Sw01 ∷ CZ03 ∷ []) (wl0092 c4)

-- nat 0 BOX(4;03): 3 steps
lem-nat-0-BOX⟨4·03⟩ : WsL → ⟪ (Sw01 ∷ Bx4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-13 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·03⟩ c4 = derive (Sw01 ∷ Bx4-03 ∷ []) (Bx4-13 ∷ Sw01 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw⁻ 0 (q225 c4) ∷
   re 0 1 (Bx4-13 ∷ []) ∷ []) Eq.refl

private
  q226 : WsL → Eqn
  q226 c4 = eqn (Sw01 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4)
  q227 : WsL → Eqn
  q227 c4 = eqn (Sw01 ∷ Toff014 ∷ []) (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4)
  q228 : WsL → Eqn
  q228 c4 = eqn (Sw01 ∷ Bx4-03 ∷ []) (Bx4-13 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·03⟩ c4)

-- nat 0 BOX(0;413): 8 steps
lem-nat-0-BOX⟨0·413⟩ : WsL → ⟪ (Sw01 ∷ Bx0-413 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-403 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·413⟩ c4 = derive (Sw01 ∷ Bx0-413 ∷ []) (Bx1-403 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ CCZ014 ∷ Bx4-03 ∷ []) ∷
   rw 0 (q226 c4) ∷
   rw 1 (q227 c4) ∷
   rw 2 (q228 c4) ∷
   rw 3 (q227 c4) ∷
   rw 4 (q226 c4) ∷
   rw 5 (q228 c4) ∷
   re 0 6 (Bx1-403 ∷ []) ∷ []) Eq.refl

private
  q229 : WsL → Eqn
  q229 c4 = eqn (Sw01 ∷ Toff402 ∷ []) (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4)
  q230 : WsL → Eqn
  q230 c4 = eqn (Sw01 ∷ Bx0-413 ∷ []) (Bx1-403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·413⟩ c4)

-- nat 0 BOX(4;0213): 8 steps
lem-nat-0-BOX⟨4·0213⟩ : WsL → ⟪ (Sw01 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·0213⟩ c4 = derive (Sw01 ∷ Bx4-0213 ∷ []) (Bx4-1203 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-413 ∷ Toff402 ∷ CCZ024 ∷ Bx0-413 ∷ []) ∷
   rw 0 (q175 c4) ∷
   rw 1 (q229 c4) ∷
   rw 2 (q230 c4) ∷
   rw 3 (q229 c4) ∷
   rw 4 (q175 c4) ∷
   rw 5 (q230 c4) ∷
   re 0 6 (Bx4-1203 ∷ []) ∷ []) Eq.refl

private
  q231 : WsL → Eqn
  q231 c4 = eqn (CZ03 ∷ Sw01 ∷ []) (Sw01 ∷ CZ13 ∷ []) (wl0088 c4)

-- nat 0 BOX(4;13): 3 steps
lem-nat-0-BOX⟨4·13⟩ : WsL → ⟪ (Sw01 ∷ Bx4-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-03 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·13⟩ c4 = derive (Sw01 ∷ Bx4-13 ∷ []) (Bx4-03 ∷ Sw01 ∷ [])
  (re 1 1 (CZ13 ∷ []) ∷
   rw⁻ 0 (q231 c4) ∷
   re 0 1 (Bx4-03 ∷ []) ∷ []) Eq.refl

-- nat 0 BOX(0;423): 8 steps
lem-nat-0-BOX⟨0·423⟩ : WsL → ⟪ (Sw01 ∷ Bx0-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-423 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·423⟩ c4 = derive (Sw01 ∷ Bx0-423 ∷ []) (Bx1-423 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) ∷
   rw 0 (q175 c4) ∷
   rw 1 (q176 c4) ∷
   rw 2 (q228 c4) ∷
   rw 3 (q176 c4) ∷
   rw 4 (q175 c4) ∷
   rw 5 (q228 c4) ∷
   re 0 6 (Bx1-423 ∷ []) ∷ []) Eq.refl

private
  q232 : WsL → Eqn
  q232 c4 = eqn (Sw01 ∷ Toff401 ∷ []) (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4)
  q233 : WsL → Eqn
  q233 c4 = eqn (Sw01 ∷ Bx0-423 ∷ []) (Bx1-423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·423⟩ c4)

-- nat 0 BOX(4;0123): 8 steps
lem-nat-0-BOX⟨4·0123⟩ : WsL → ⟪ (Sw01 ∷ Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·0123⟩ c4 = derive (Sw01 ∷ Bx4-0123 ∷ []) (Bx4-1023 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) ∷
   rw 0 (q226 c4) ∷
   rw 1 (q232 c4) ∷
   rw 2 (q233 c4) ∷
   rw 3 (q232 c4) ∷
   rw 4 (q226 c4) ∷
   rw 5 (q233 c4) ∷
   re 0 6 (Bx4-1023 ∷ []) ∷ []) Eq.refl

private
  q234 : WsL → Eqn
  q234 c4 = eqn (Sw01 ∷ Bx4-13 ∷ []) (Bx4-03 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·13⟩ c4)

-- nat 0 BOX(1;423): 8 steps
lem-nat-0-BOX⟨1·423⟩ : WsL → ⟪ (Sw01 ∷ Bx1-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-423 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·423⟩ c4 = derive (Sw01 ∷ Bx1-423 ∷ []) (Bx0-423 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) ∷
   rw 0 (q165 c4) ∷
   rw 1 (q166 c4) ∷
   rw 2 (q234 c4) ∷
   rw 3 (q166 c4) ∷
   rw 4 (q165 c4) ∷
   rw 5 (q234 c4) ∷
   re 0 6 (Bx0-423 ∷ []) ∷ []) Eq.refl

private
  q235 : WsL → Eqn
  q235 c4 = eqn (Sw01 ∷ Bx1-423 ∷ []) (Bx0-423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·423⟩ c4)

-- nat 0 BOX(4;1023): 8 steps
lem-nat-0-BOX⟨4·1023⟩ : WsL → ⟪ (Sw01 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·1023⟩ c4 = derive (Sw01 ∷ Bx4-1023 ∷ []) (Bx4-0123 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ []) ∷
   rw 0 (q226 c4) ∷
   rw 1 (q232 c4) ∷
   rw 2 (q235 c4) ∷
   rw 3 (q232 c4) ∷
   rw 4 (q226 c4) ∷
   rw 5 (q235 c4) ∷
   re 0 6 (Bx4-0123 ∷ []) ∷ []) Eq.refl

private
  q236 : WsL → Eqn
  q236 c4 = eqn (Sw23 ∷ Bx4-03 ∷ []) (Bx4-02 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·03⟩ c4)

-- nat 2 BOX(0;413): 8 steps
lem-nat-2-BOX⟨0·413⟩ : WsL → ⟪ (Sw23 ∷ Bx0-413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-412 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·413⟩ c4 = derive (Sw23 ∷ Bx0-413 ∷ []) (Bx0-412 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ CCZ014 ∷ Bx4-03 ∷ []) ∷
   rw 0 (q211 c4) ∷
   rw 1 (q212 c4) ∷
   rw 2 (q236 c4) ∷
   rw 3 (q212 c4) ∷
   rw 4 (q211 c4) ∷
   rw 5 (q236 c4) ∷
   re 0 6 (Bx0-412 ∷ []) ∷ []) Eq.refl

private
  q237 : WsL → Eqn
  q237 c4 = eqn (Sw23 ∷ Bx0-413 ∷ []) (Bx0-412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·413⟩ c4)

-- nat 2 BOX(4;0213): 8 steps
lem-nat-2-BOX⟨4·0213⟩ : WsL → ⟪ (Sw23 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·0213⟩ c4 = derive (Sw23 ∷ Bx4-0213 ∷ []) (Bx4-0312 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-413 ∷ Toff402 ∷ CCZ024 ∷ Bx0-413 ∷ []) ∷
   rw 0 (q21 c4) ∷
   rw 1 (q49 c4) ∷
   rw 2 (q237 c4) ∷
   rw 3 (q49 c4) ∷
   rw 4 (q21 c4) ∷
   rw 5 (q237 c4) ∷
   re 0 6 (Bx4-0312 ∷ []) ∷ []) Eq.refl

-- nat 3 BOX(3;14): 3 steps
lem-nat-3-BOX⟨3·14⟩ : WsL → ⟪ (Sw34 ∷ Bx3-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-13 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·14⟩ c4 = derive (Sw34 ∷ Bx3-14 ∷ []) (Bx4-13 ∷ Sw34 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   rw 0 (q54 c4) ∷
   re 0 1 (Bx4-13 ∷ []) ∷ []) Eq.refl

private
  q238 : WsL → Eqn
  q238 c4 = eqn (Sw34 ∷ CCZ123 ∷ []) (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4)
  q239 : WsL → Eqn
  q239 c4 = eqn (Sw34 ∷ Toff123 ∷ []) (Toff124 ∷ Sw34 ∷ []) (lem-nat-3-TOFF123 c4)
  q240 : WsL → Eqn
  q240 c4 = eqn (Sw34 ∷ Bx3-14 ∷ []) (Bx4-13 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·14⟩ c4)

-- nat 3 BOX(1;324): 8 steps
lem-nat-3-BOX⟨1·324⟩ : WsL → ⟪ (Sw34 ∷ Bx1-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-423 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·324⟩ c4 = derive (Sw34 ∷ Bx1-324 ∷ []) (Bx1-423 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) ∷
   rw 0 (q238 c4) ∷
   rw 1 (q239 c4) ∷
   rw 2 (q240 c4) ∷
   rw 3 (q239 c4) ∷
   rw 4 (q238 c4) ∷
   rw 5 (q240 c4) ∷
   re 0 6 (Bx1-423 ∷ []) ∷ []) Eq.refl

private
  q241 : WsL → Eqn
  q241 c4 = eqn (Sw34 ∷ Toff301 ∷ []) (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4)
  q242 : WsL → Eqn
  q242 c4 = eqn (Sw34 ∷ Bx1-324 ∷ []) (Bx1-423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·324⟩ c4)

-- nat 3 BOX(3;1024): 8 steps
lem-nat-3-BOX⟨3·1024⟩ : WsL → ⟪ (Sw34 ∷ Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·1024⟩ c4 = derive (Sw34 ∷ Bx3-1024 ∷ []) (Bx4-1023 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) ∷
   rw 0 (q106 c4) ∷
   rw 1 (q241 c4) ∷
   rw 2 (q242 c4) ∷
   rw 3 (q241 c4) ∷
   rw 4 (q106 c4) ∷
   rw 5 (q242 c4) ∷
   re 0 6 (Bx4-1023 ∷ []) ∷ []) Eq.refl

private
  q243 : WsL → Eqn
  q243 c4 = eqn (CZ23 ∷ Sw12 ∷ []) (Sw12 ∷ CZ13 ∷ []) (wl0029 c4)

-- nat 1 BOX(4;13): 3 steps
lem-nat-1-BOX⟨4·13⟩ : WsL → ⟪ (Sw12 ∷ Bx4-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-23 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·13⟩ c4 = derive (Sw12 ∷ Bx4-13 ∷ []) (Bx4-23 ∷ Sw12 ∷ [])
  (re 1 1 (CZ13 ∷ []) ∷
   rw⁻ 0 (q243 c4) ∷
   re 0 1 (Bx4-23 ∷ []) ∷ []) Eq.refl

private
  q244 : WsL → Eqn
  q244 c4 = eqn (CCZ124 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ124 ∷ []) (wl0078 c4)
  q245 : WsL → Eqn
  q245 c4 = eqn (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) (wl0095 c4)
  q246 : WsL → Eqn
  q246 c4 = eqn (Sw12 ∷ Bx4-13 ∷ []) (Bx4-23 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·13⟩ c4)

-- nat 1 BOX(1;423): 8 steps
lem-nat-1-BOX⟨1·423⟩ : WsL → ⟪ (Sw12 ∷ Bx1-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-413 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·423⟩ c4 = derive (Sw12 ∷ Bx1-423 ∷ []) (Bx2-413 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) ∷
   rw⁻ 0 (q244 c4) ∷
   rw 1 (q245 c4) ∷
   rw 2 (q246 c4) ∷
   rw 3 (q245 c4) ∷
   rw⁻ 4 (q244 c4) ∷
   rw 5 (q246 c4) ∷
   re 0 6 (Bx2-413 ∷ []) ∷ []) Eq.refl

private
  q247 : WsL → Eqn
  q247 c4 = eqn (Sw12 ∷ Bx1-423 ∷ []) (Bx2-413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·423⟩ c4)

-- nat 1 BOX(4;1023): 8 steps
lem-nat-1-BOX⟨4·1023⟩ : WsL → ⟪ (Sw12 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2013 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·1023⟩ c4 = derive (Sw12 ∷ Bx4-1023 ∷ []) (Bx4-2013 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ []) ∷
   rw 0 (q205 c4) ∷
   rw 1 (q223 c4) ∷
   rw 2 (q247 c4) ∷
   rw 3 (q223 c4) ∷
   rw 4 (q205 c4) ∷
   rw 5 (q247 c4) ∷
   re 0 6 (Bx4-2013 ∷ []) ∷ []) Eq.refl

private
  q248 : WsL → Eqn
  q248 c4 = eqn (CZ23 ∷ Sw23 ∷ []) (Sw23 ∷ CZ23 ∷ []) (wl0045 c4)

-- nat 2 BOX(4;23): 3 steps
lem-nat-2-BOX⟨4·23⟩ : WsL → ⟪ (Sw23 ∷ Bx4-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-32 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·23⟩ c4 = derive (Sw23 ∷ Bx4-23 ∷ []) (Bx4-32 ∷ Sw23 ∷ [])
  (re 1 1 (CZ23 ∷ []) ∷
   rw⁻ 0 (q248 c4) ∷
   re 0 1 (Bx4-32 ∷ []) ∷ []) Eq.refl

private
  q249 : WsL → Eqn
  q249 c4 = eqn (Sw23 ∷ CCZ124 ∷ []) (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4)
  q250 : WsL → Eqn
  q250 c4 = eqn (Sw23 ∷ Toff214 ∷ []) (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4)
  q251 : WsL → Eqn
  q251 c4 = eqn (Sw23 ∷ Bx4-23 ∷ []) (Bx4-32 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·23⟩ c4)

-- nat 2 BOX(2;413): 8 steps
lem-nat-2-BOX⟨2·413⟩ : WsL → ⟪ (Sw23 ∷ Bx2-413 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-412 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·413⟩ c4 = derive (Sw23 ∷ Bx2-413 ∷ []) (Bx3-412 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff214 ∷ Bx4-23 ∷ Toff214 ∷ CCZ124 ∷ Bx4-23 ∷ []) ∷
   rw 0 (q249 c4) ∷
   rw 1 (q250 c4) ∷
   rw 2 (q251 c4) ∷
   rw 3 (q250 c4) ∷
   rw 4 (q249 c4) ∷
   rw 5 (q251 c4) ∷
   re 0 6 (Bx3-412 ∷ []) ∷ []) Eq.refl

private
  q252 : WsL → Eqn
  q252 c4 = eqn (Sw23 ∷ Bx2-413 ∷ []) (Bx3-412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·413⟩ c4)

-- nat 2 BOX(4;2013): 8 steps
lem-nat-2-BOX⟨4·2013⟩ : WsL → ⟪ (Sw23 ∷ Bx4-2013 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·2013⟩ c4 = derive (Sw23 ∷ Bx4-2013 ∷ []) (Bx4-3012 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-413 ∷ Toff402 ∷ CCZ024 ∷ Bx2-413 ∷ []) ∷
   rw 0 (q21 c4) ∷
   rw 1 (q49 c4) ∷
   rw 2 (q252 c4) ∷
   rw 3 (q49 c4) ∷
   rw 4 (q21 c4) ∷
   rw 5 (q252 c4) ∷
   re 0 6 (Bx4-3012 ∷ []) ∷ []) Eq.refl

private
  q253 : WsL → Eqn
  q253 c4 = eqn (CZ13 ∷ Sw12 ∷ []) (Sw12 ∷ CZ23 ∷ []) (wl0026 c4)

-- nat 1 BOX(4;23): 3 steps
lem-nat-1-BOX⟨4·23⟩ : WsL → ⟪ (Sw12 ∷ Bx4-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-13 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·23⟩ c4 = derive (Sw12 ∷ Bx4-23 ∷ []) (Bx4-13 ∷ Sw12 ∷ [])
  (re 1 1 (CZ23 ∷ []) ∷
   rw⁻ 0 (q253 c4) ∷
   re 0 1 (Bx4-13 ∷ []) ∷ []) Eq.refl

private
  q254 : WsL → Eqn
  q254 c4 = eqn (Sw12 ∷ Toff214 ∷ []) (Toff124 ∷ Sw12 ∷ []) (wl0126 c4)
  q255 : WsL → Eqn
  q255 c4 = eqn (Sw12 ∷ Bx4-23 ∷ []) (Bx4-13 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·23⟩ c4)

-- nat 1 BOX(2;413): 8 steps
lem-nat-1-BOX⟨2·413⟩ : WsL → ⟪ (Sw12 ∷ Bx2-413 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-423 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·413⟩ c4 = derive (Sw12 ∷ Bx2-413 ∷ []) (Bx1-423 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff214 ∷ Bx4-23 ∷ Toff214 ∷ CCZ124 ∷ Bx4-23 ∷ []) ∷
   rw⁻ 0 (q244 c4) ∷
   rw 1 (q254 c4) ∷
   rw 2 (q255 c4) ∷
   rw 3 (q254 c4) ∷
   rw⁻ 4 (q244 c4) ∷
   rw 5 (q255 c4) ∷
   re 0 6 (Bx1-423 ∷ []) ∷ []) Eq.refl

private
  q256 : WsL → Eqn
  q256 c4 = eqn (Sw12 ∷ Bx2-413 ∷ []) (Bx1-423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·413⟩ c4)

-- nat 1 BOX(4;2013): 8 steps
lem-nat-1-BOX⟨4·2013⟩ : WsL → ⟪ (Sw12 ∷ Bx4-2013 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·2013⟩ c4 = derive (Sw12 ∷ Bx4-2013 ∷ []) (Bx4-1023 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-413 ∷ Toff402 ∷ CCZ024 ∷ Bx2-413 ∷ []) ∷
   rw 0 (q208 c4) ∷
   rw 1 (q209 c4) ∷
   rw 2 (q256 c4) ∷
   rw 3 (q209 c4) ∷
   rw 4 (q208 c4) ∷
   rw 5 (q256 c4) ∷
   re 0 6 (Bx4-1023 ∷ []) ∷ []) Eq.refl

private
  q257 : WsL → Eqn
  q257 c4 = eqn (CZ12 ∷ Sw12 ∷ []) (Sw12 ∷ CZ12 ∷ []) (wl0109 c4)

-- nat 1 BOX(4;12): 3 steps
lem-nat-1-BOX⟨4·12⟩ : WsL → ⟪ (Sw12 ∷ Bx4-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-21 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·12⟩ c4 = derive (Sw12 ∷ Bx4-12 ∷ []) (Bx4-21 ∷ Sw12 ∷ [])
  (re 1 1 (CZ12 ∷ []) ∷
   rw⁻ 0 (q257 c4) ∷
   re 0 1 (Bx4-21 ∷ []) ∷ []) Eq.refl

private
  q258 : WsL → Eqn
  q258 c4 = eqn (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) (wl0136 c4)
  q259 : WsL → Eqn
  q259 c4 = eqn (Sw12 ∷ Bx4-12 ∷ []) (Bx4-21 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·12⟩ c4)

-- nat 1 BOX(1;432): 8 steps
lem-nat-1-BOX⟨1·432⟩ : WsL → ⟪ (Sw12 ∷ Bx1-432 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-431 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·432⟩ c4 = derive (Sw12 ∷ Bx1-432 ∷ []) (Bx2-431 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-12 ∷ Toff134 ∷ CCZ134 ∷ Bx4-12 ∷ []) ∷
   rw⁻ 0 (q46 c4) ∷
   rw 1 (q258 c4) ∷
   rw 2 (q259 c4) ∷
   rw 3 (q258 c4) ∷
   rw⁻ 4 (q46 c4) ∷
   rw 5 (q259 c4) ∷
   re 0 6 (Bx2-431 ∷ []) ∷ []) Eq.refl

private
  q260 : WsL → Eqn
  q260 c4 = eqn (Sw12 ∷ Bx1-432 ∷ []) (Bx2-431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·432⟩ c4)

-- nat 1 BOX(4;1032): 8 steps
lem-nat-1-BOX⟨4·1032⟩ : WsL → ⟪ (Sw12 ∷ Bx4-1032 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·1032⟩ c4 = derive (Sw12 ∷ Bx4-1032 ∷ []) (Bx4-2031 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-432 ∷ Toff401 ∷ CCZ014 ∷ Bx1-432 ∷ []) ∷
   rw 0 (q205 c4) ∷
   rw 1 (q223 c4) ∷
   rw 2 (q260 c4) ∷
   rw 3 (q223 c4) ∷
   rw 4 (q205 c4) ∷
   rw 5 (q260 c4) ∷
   re 0 6 (Bx4-2031 ∷ []) ∷ []) Eq.refl

-- nat 2 BOX(4;32): 3 steps
lem-nat-2-BOX⟨4·32⟩ : WsL → ⟪ (Sw23 ∷ Bx4-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-23 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·32⟩ c4 = derive (Sw23 ∷ Bx4-32 ∷ []) (Bx4-23 ∷ Sw23 ∷ [])
  (re 1 1 (CZ23 ∷ []) ∷
   rw⁻ 0 (q248 c4) ∷
   re 0 1 (Bx4-23 ∷ []) ∷ []) Eq.refl

private
  q261 : WsL → Eqn
  q261 c4 = eqn (Sw23 ∷ CCZ134 ∷ []) (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4)
  q262 : WsL → Eqn
  q262 c4 = eqn (Sw23 ∷ Toff314 ∷ []) (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4)
  q263 : WsL → Eqn
  q263 c4 = eqn (Sw23 ∷ Bx4-32 ∷ []) (Bx4-23 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·32⟩ c4)

-- nat 2 BOX(3;412): 8 steps
lem-nat-2-BOX⟨3·412⟩ : WsL → ⟪ (Sw23 ∷ Bx3-412 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-413 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·412⟩ c4 = derive (Sw23 ∷ Bx3-412 ∷ []) (Bx2-413 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) ∷
   rw 0 (q261 c4) ∷
   rw 1 (q262 c4) ∷
   rw 2 (q263 c4) ∷
   rw 3 (q262 c4) ∷
   rw 4 (q261 c4) ∷
   rw 5 (q263 c4) ∷
   re 0 6 (Bx2-413 ∷ []) ∷ []) Eq.refl

private
  q264 : WsL → Eqn
  q264 c4 = eqn (Sw23 ∷ Bx3-412 ∷ []) (Bx2-413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·412⟩ c4)

-- nat 2 BOX(4;3012): 8 steps
lem-nat-2-BOX⟨4·3012⟩ : WsL → ⟪ (Sw23 ∷ Bx4-3012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2013 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·3012⟩ c4 = derive (Sw23 ∷ Bx4-3012 ∷ []) (Bx4-2013 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff403 ∷ Bx3-412 ∷ Toff403 ∷ CCZ034 ∷ Bx3-412 ∷ []) ∷
   rw 0 (q16 c4) ∷
   rw 1 (q214 c4) ∷
   rw 2 (q264 c4) ∷
   rw 3 (q214 c4) ∷
   rw 4 (q16 c4) ∷
   rw 5 (q264 c4) ∷
   re 0 6 (Bx4-2013 ∷ []) ∷ []) Eq.refl

private
  q265 : WsL → Eqn
  q265 c4 = eqn (Sw12 ∷ Toff104 ∷ []) (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4)

-- nat 1 BOX(1;403): 8 steps
lem-nat-1-BOX⟨1·403⟩ : WsL → ⟪ (Sw12 ∷ Bx1-403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-403 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·403⟩ c4 = derive (Sw12 ∷ Bx1-403 ∷ []) (Bx2-403 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ []) ∷
   rw 0 (q205 c4) ∷
   rw 1 (q265 c4) ∷
   rw 2 (q246 c4) ∷
   rw 3 (q265 c4) ∷
   rw 4 (q205 c4) ∷
   rw 5 (q246 c4) ∷
   re 0 6 (Bx2-403 ∷ []) ∷ []) Eq.refl

private
  q266 : WsL → Eqn
  q266 c4 = eqn (Sw12 ∷ Bx1-403 ∷ []) (Bx2-403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·403⟩ c4)

-- nat 1 BOX(4;1203): 8 steps
lem-nat-1-BOX⟨4·1203⟩ : WsL → ⟪ (Sw12 ∷ Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2103 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·1203⟩ c4 = derive (Sw12 ∷ Bx4-1203 ∷ []) (Bx4-2103 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-403 ∷ Toff412 ∷ CCZ124 ∷ Bx1-403 ∷ []) ∷
   rw⁻ 0 (q244 c4) ∷
   rw 1 (q114 c4) ∷
   rw 2 (q266 c4) ∷
   rw 3 (q114 c4) ∷
   rw⁻ 4 (q244 c4) ∷
   rw 5 (q266 c4) ∷
   re 0 6 (Bx4-2103 ∷ []) ∷ []) Eq.refl

-- nat 2 BOX(2;403): 8 steps
lem-nat-2-BOX⟨2·403⟩ : WsL → ⟪ (Sw23 ∷ Bx2-403 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-402 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·403⟩ c4 = derive (Sw23 ∷ Bx2-403 ∷ []) (Bx3-402 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-23 ∷ Toff204 ∷ CCZ024 ∷ Bx4-23 ∷ []) ∷
   rw 0 (q21 c4) ∷
   rw 1 (q22 c4) ∷
   rw 2 (q251 c4) ∷
   rw 3 (q22 c4) ∷
   rw 4 (q21 c4) ∷
   rw 5 (q251 c4) ∷
   re 0 6 (Bx3-402 ∷ []) ∷ []) Eq.refl

private
  q267 : WsL → Eqn
  q267 c4 = eqn (Sw23 ∷ Bx2-403 ∷ []) (Bx3-402 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·403⟩ c4)

-- nat 2 BOX(4;2103): 8 steps
lem-nat-2-BOX⟨4·2103⟩ : WsL → ⟪ (Sw23 ∷ Bx4-2103 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3102 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·2103⟩ c4 = derive (Sw23 ∷ Bx4-2103 ∷ []) (Bx4-3102 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-403 ∷ Toff412 ∷ CCZ124 ∷ Bx2-403 ∷ []) ∷
   rw 0 (q249 c4) ∷
   rw 1 (q139 c4) ∷
   rw 2 (q267 c4) ∷
   rw 3 (q139 c4) ∷
   rw 4 (q249 c4) ∷
   rw 5 (q267 c4) ∷
   re 0 6 (Bx4-3102 ∷ []) ∷ []) Eq.refl

private
  q268 : WsL → Eqn
  q268 c4 = eqn (Sw01 ∷ Bx4-32 ∷ []) (Bx4-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ))

-- nat 0 BOX(3;402): 8 steps
lem-nat-0-BOX⟨3·402⟩ : WsL → ⟪ (Sw01 ∷ Bx3-402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-412 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·402⟩ c4 = derive (Sw01 ∷ Bx3-402 ∷ []) (Bx3-412 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ []) ∷
   rw 0 (q191 c4) ∷
   rw 1 (q171 c4) ∷
   rw 2 (q268 c4) ∷
   rw 3 (q171 c4) ∷
   rw 4 (q191 c4) ∷
   rw 5 (q268 c4) ∷
   re 0 6 (Bx3-412 ∷ []) ∷ []) Eq.refl

private
  q269 : WsL → Eqn
  q269 c4 = eqn (Sw01 ∷ Bx3-402 ∷ []) (Bx3-412 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·402⟩ c4)

-- nat 0 BOX(4;3102): 8 steps
lem-nat-0-BOX⟨4·3102⟩ : WsL → ⟪ (Sw01 ∷ Bx4-3102 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·3102⟩ c4 = derive (Sw01 ∷ Bx4-3102 ∷ []) (Bx4-3012 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff413 ∷ Bx3-402 ∷ Toff413 ∷ CCZ134 ∷ Bx3-402 ∷ []) ∷
   rw 0 (q220 c4) ∷
   rw 1 (q221 c4) ∷
   rw 2 (q269 c4) ∷
   rw 3 (q221 c4) ∷
   rw 4 (q220 c4) ∷
   rw 5 (q269 c4) ∷
   re 0 6 (Bx4-3012 ∷ []) ∷ []) Eq.refl

-- nat 1 BOX(4;21): 3 steps
lem-nat-1-BOX⟨4·21⟩ : WsL → ⟪ (Sw12 ∷ Bx4-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-12 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·21⟩ c4 = derive (Sw12 ∷ Bx4-21 ∷ []) (Bx4-12 ∷ Sw12 ∷ [])
  (re 1 1 (CZ12 ∷ []) ∷
   rw⁻ 0 (q257 c4) ∷
   re 0 1 (Bx4-12 ∷ []) ∷ []) Eq.refl

private
  q270 : WsL → Eqn
  q270 c4 = eqn (CZ24 ∷ Sw12 ∷ []) (Sw12 ∷ CZ14 ∷ []) (wl0089 c4)

-- nat 1 BOX(2;14): 3 steps
lem-nat-1-BOX⟨2·14⟩ : WsL → ⟪ (Sw12 ∷ Bx2-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-24 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·14⟩ c4 = derive (Sw12 ∷ Bx2-14 ∷ []) (Bx1-24 ∷ Sw12 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   rw⁻ 0 (q270 c4) ∷
   re 0 1 (Bx1-24 ∷ []) ∷ []) Eq.refl

private
  q271 : WsL → Eqn
  q271 c4 = eqn (CCZ012 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ012 ∷ []) (wl0037 c4)
  q272 : WsL → Eqn
  q272 c4 = eqn (Sw12 ∷ Bx2-14 ∷ []) (Bx1-24 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·14⟩ c4)

-- nat 1 BOX(1;204): 8 steps
lem-nat-1-BOX⟨1·204⟩ : WsL → ⟪ (Sw12 ∷ Bx1-204 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-104 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·204⟩ c4 = derive (Sw12 ∷ Bx1-204 ∷ []) (Bx2-104 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) ∷
   rw⁻ 0 (q271 c4) ∷
   rw 1 (q75 c4) ∷
   rw 2 (q272 c4) ∷
   rw 3 (q75 c4) ∷
   rw⁻ 4 (q271 c4) ∷
   rw 5 (q272 c4) ∷
   re 0 6 (Bx2-104 ∷ []) ∷ []) Eq.refl

private
  q273 : WsL → Eqn
  q273 c4 = eqn (CCZ123 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ123 ∷ []) (wl0111 c4)
  q274 : WsL → Eqn
  q274 c4 = eqn (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) (wl0112 c4)
  q275 : WsL → Eqn
  q275 c4 = eqn (Sw12 ∷ Bx1-204 ∷ []) (Bx2-104 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·204⟩ c4)

-- nat 1 BOX(2;1304): 8 steps
lem-nat-1-BOX⟨2·1304⟩ : WsL → ⟪ (Sw12 ∷ Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·1304⟩ c4 = derive (Sw12 ∷ Bx2-1304 ∷ []) (Bx1-2304 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-204 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ []) ∷
   rw⁻ 0 (q273 c4) ∷
   rw 1 (q274 c4) ∷
   rw 2 (q275 c4) ∷
   rw 3 (q274 c4) ∷
   rw⁻ 4 (q273 c4) ∷
   rw 5 (q275 c4) ∷
   re 0 6 (Bx1-2304 ∷ []) ∷ []) Eq.refl

private
  q276 : WsL → Eqn
  q276 c4 = eqn (Sw12 ∷ Bx1-24 ∷ []) (Bx2-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·24⟩ c4)

-- nat 1 BOX(2;104): 8 steps
lem-nat-1-BOX⟨2·104⟩ : WsL → ⟪ (Sw12 ∷ Bx2-104 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-204 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·104⟩ c4 = derive (Sw12 ∷ Bx2-104 ∷ []) (Bx1-204 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-24 ∷ Toff201 ∷ CCZ012 ∷ Bx1-24 ∷ []) ∷
   rw⁻ 0 (q271 c4) ∷
   rw 1 (q81 c4) ∷
   rw 2 (q276 c4) ∷
   rw 3 (q81 c4) ∷
   rw⁻ 4 (q271 c4) ∷
   rw 5 (q276 c4) ∷
   re 0 6 (Bx1-204 ∷ []) ∷ []) Eq.refl

private
  q277 : WsL → Eqn
  q277 c4 = eqn (Sw12 ∷ Toff123 ∷ []) (Toff213 ∷ Sw12 ∷ []) (wl0146 c4)
  q278 : WsL → Eqn
  q278 c4 = eqn (Sw12 ∷ Bx2-104 ∷ []) (Bx1-204 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·104⟩ c4)

-- nat 1 BOX(1;2304): 8 steps
lem-nat-1-BOX⟨1·2304⟩ : WsL → ⟪ (Sw12 ∷ Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·2304⟩ c4 = derive (Sw12 ∷ Bx1-2304 ∷ []) (Bx2-1304 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-104 ∷ Toff123 ∷ CCZ123 ∷ Bx2-104 ∷ []) ∷
   rw⁻ 0 (q273 c4) ∷
   rw 1 (q277 c4) ∷
   rw 2 (q278 c4) ∷
   rw 3 (q277 c4) ∷
   rw⁻ 4 (q273 c4) ∷
   rw 5 (q278 c4) ∷
   re 0 6 (Bx2-1304 ∷ []) ∷ []) Eq.refl

-- nat 1 BOX(0;31): 3 steps
lem-nat-1-BOX⟨0·31⟩ : WsL → ⟪ (Sw12 ∷ Bx0-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-32 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·31⟩ c4 = derive (Sw12 ∷ Bx0-31 ∷ []) (Bx0-32 ∷ Sw12 ∷ [])
  (re 1 1 (CZ13 ∷ []) ∷
   rw⁻ 0 (q243 c4) ∷
   re 0 1 (Bx0-32 ∷ []) ∷ []) Eq.refl

private
  q279 : WsL → Eqn
  q279 c4 = eqn (Sw12 ∷ Bx0-31 ∷ []) (Bx0-32 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·31⟩ c4)

-- nat 1 BOX(3;041): 8 steps
lem-nat-1-BOX⟨3·041⟩ : WsL → ⟪ (Sw12 ∷ Bx3-041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-042 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·041⟩ c4 = derive (Sw12 ∷ Bx3-041 ∷ []) (Bx3-042 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) ∷
   rw 0 (q27 c4) ∷
   rw 1 (q28 c4) ∷
   rw 2 (q279 c4) ∷
   rw 3 (q28 c4) ∷
   rw 4 (q27 c4) ∷
   rw 5 (q279 c4) ∷
   re 0 6 (Bx3-042 ∷ []) ∷ []) Eq.refl

private
  q280 : WsL → Eqn
  q280 c4 = eqn (Sw12 ∷ Bx3-041 ∷ []) (Bx3-042 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·041⟩ c4)

-- nat 1 BOX(0;3241): 8 steps
lem-nat-1-BOX⟨0·3241⟩ : WsL → ⟪ (Sw12 ∷ Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·3241⟩ c4 = derive (Sw12 ∷ Bx0-3241 ∷ []) (Bx0-3142 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-041 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ []) ∷
   rw 0 (q24 c4) ∷
   rw 1 (q25 c4) ∷
   rw 2 (q280 c4) ∷
   rw 3 (q25 c4) ∷
   rw 4 (q24 c4) ∷
   rw 5 (q280 c4) ∷
   re 0 6 (Bx0-3142 ∷ []) ∷ []) Eq.refl

-- nat 1 BOX(0;32): 3 steps
lem-nat-1-BOX⟨0·32⟩ : WsL → ⟪ (Sw12 ∷ Bx0-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-31 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·32⟩ c4 = derive (Sw12 ∷ Bx0-32 ∷ []) (Bx0-31 ∷ Sw12 ∷ [])
  (re 1 1 (CZ23 ∷ []) ∷
   rw⁻ 0 (q253 c4) ∷
   re 0 1 (Bx0-31 ∷ []) ∷ []) Eq.refl
