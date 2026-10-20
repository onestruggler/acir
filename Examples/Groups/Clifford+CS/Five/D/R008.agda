{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R008 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0003 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0015 ; wl0016 ; wl0017 ; wl0018 ; wl0021 ; wl0022 ; wl0023 ; wl0024 ; wl0026 ; wl0029 ; wl0030 ; wl0032 ; wl0034 ; wl0037 ; wl0038 ; wl0043 ; wl0053 ; wl0057 ; wl0058 ; wl0061 ; wl0063 ; wl0064 ; wl0067 ; wl0068 ; wl0076 ; wl0081 ; wl0084 ; wl0087 ; wl0091 ; wl0096 ; wl0099 ; wl0100 ; wl0101 ; wl0102 ; wl0112 ; wl0114 ; wl0130 ; wl0132 ; wl0133 ; wl0137 ; wl0138 ; wl0139 ; wl0140 ; wl0141)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF024 ; lem-nat-1-TOFF203 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF013 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF102 ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-CCZ034 ; lem-nat-3-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF103 ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ014 ; lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF014 ; lem-nat-0-TOFF304 ; lem-nat-0-TOFF314 ; lem-nat-3-TOFF304)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-TOFF214 ; lem-nat-0-TOFF402 ; lem-nat-3-TOFF023 ; lem-nat-3-TOFF214 ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1234⟩ ; lem-nat-0-BOX⟨1·04⟩ ; lem-nat-1-BOX⟨2·04⟩ ; lem-nat-2-CZ04 ; lem-nat-3-BOX⟨2·0314⟩ ; lem-nat-3-CZ03 ; lem-nat-3-CZ04)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-BOX⟨1·0324⟩ ; lem-nat-1-CS01 ; lem-nat-1-CS02 ; lem-nat-1-CZ01 ; lem-nat-1-CZ02)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-CS14 ; lem-nat-1-BOX⟨2·1340⟩ ; lem-nat-1-CS04 ; lem-nat-1-CSd02 ; lem-nat-2-TOFF403)

private
  q1 : WsL → Eqn
  q1 c4 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (c₁ (K) (Swap ↑))
  q2 : WsL → Eqn
  q2 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 c4)
  q3 : WsL → Eqn
  q3 c4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap))
  q4 : WsL → Eqn
  q4 c4 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (c₁ (iI) (Swap ↑))
  q5 : WsL → Eqn
  q5 c4 = eqn (K0 ∷ Sw34 ∷ []) (Sw34 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑))
  q6 : WsL → Eqn
  q6 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 c4)
  q7 : WsL → Eqn
  q7 c4 = eqn (CX01 ∷ Sw34 ∷ []) (Sw34 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap ↑))
  q8 : WsL → Eqn
  q8 c4 = eqn (ι ∷ Sw34 ∷ []) (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑))
  q9 : WsL → Eqn
  q9 c4 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (c₁ (K) (Swap))
  q10 : WsL → Eqn
  q10 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0008 c4)
  q11 : WsL → Eqn
  q11 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 c4)
  q12 : WsL → Eqn
  q12 c4 = eqn (CS24⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS14⁻ ∷ []) (wl0009 c4)
  q13 : WsL → Eqn
  q13 c4 = eqn (Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap))
  q14 : WsL → Eqn
  q14 c4 = eqn (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) (wl0010 c4)
  q15 : WsL → Eqn
  q15 c4 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap))
  q16 : WsL → Eqn
  q16 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl0011 c4)
  q17 : WsL → Eqn
  q17 c4 = eqn (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) (wl0012 c4)
  q18 : WsL → Eqn
  q18 c4 = eqn (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4)
  q19 : WsL → Eqn
  q19 c4 = eqn (CS01 ∷ Sw34 ∷ []) (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑))
  q20 : WsL → Eqn
  q20 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q21 : WsL → Eqn
  q21 c4 = eqn (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) (wl0014 c4)
  q22 : WsL → Eqn
  q22 c4 = eqn (Sw12 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS))
  q23 : WsL → Eqn
  q23 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl0015 c4)
  q24 : WsL → Eqn
  q24 c4 = eqn (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) (wl0016 c4)
  q25 : WsL → Eqn
  q25 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl0017 c4)
  q26 : WsL → Eqn
  q26 c4 = eqn (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ []) (wl0018 c4)

-- nat 1 TOFF034: 134 steps
lem-nat-1-TOFF034 : WsL → ⟪ (Sw12 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF034 c4 = derive (Sw12 ∷ Toff034 ∷ []) (Toff034 ∷ Sw12 ∷ [])
  (re 1 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) ∷
   re 3 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   re 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 (q3 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 (q3 c4) ∷
   rw⁻ 11 (q2 c4) ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 (q1 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw 12 (q2 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CS14 ∷ []) ∷
   rw⁻ 5 (q7 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 6 3 (CS14⁻ ∷ []) ∷
   rw⁻ 7 (q7 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   re 8 3 (CS04 ∷ []) ∷
   rw⁻ 9 (q5 c4) ∷
   rw⁻ 10 (q8 c4) ∷
   rw 11 (q6 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   rw⁻ 6 (q11 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw⁻ 5 (q12 c4) ∷
   rw⁻ 8 (q11 c4) ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q13 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw 9 (q13 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q9 c4) ∷
   rw⁻ 9 (q15 c4) ∷
   rw 10 (q11 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q16 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (CX03 ∷ []) ∷
   rw⁻ 4 (q17 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (CX03 ∷ []) ∷
   re 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 6 (q18 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw⁻ 10 (q13 c4) ∷
   rw⁻ 11 (q18 c4) ∷
   re 6 7 (CS04 ∷ []) ∷
   rw⁻ 7 (q1 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw 9 (q2 c4) ∷
   rw⁻ 0 (q9 c4) ∷
   rw 1 (q20 c4) ∷
   rw⁻ 2 (q21 c4) ∷
   rw 3 (q22 c4) ∷
   rw⁻ 4 (q21 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q13 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw 7 (q13 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw⁻ 6 (q9 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q23 c4) ∷
   re 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 4 (q24 c4) ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 5 (q2 c4) ∷
   re 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 6 (q18 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw⁻ 10 (q13 c4) ∷
   rw⁻ 11 (q18 c4) ∷
   re 6 7 (CS04 ∷ []) ∷
   rw⁻ 7 (q1 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw⁻ 3 (q25 c4) ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 (q11 c4) ∷
   rw⁻ 5 (q26 c4) ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 (q11 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q13 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw 9 (q13 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q9 c4) ∷
   rw⁻ 9 (q15 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   re 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   re 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 8 (q6 c4) ∷
   rw⁻ 9 (q5 c4) ∷
   rw⁻ 10 (q8 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 (q2 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 (q2 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 (q2 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 3 3 (Toff013 ∷ []) ∷
   re 2 3 (Toff014 ∷ []) ∷
   re 1 3 (Toff024 ∷ []) ∷
   re 0 3 (Toff034 ∷ []) ∷ []) Eq.refl

private
  q27 : WsL → Eqn
  q27 c4 = eqn (Sw12 ∷ CS01 ∷ []) (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4)

-- nat 1 SBOX(2;1;0;4): 3 steps
lem-nat-1-SBOX⟨2·1·0·4⟩ : WsL → ⟪ (Sw12 ∷ Sb2-1-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-0-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·1·0·4⟩ c4 = derive (Sw12 ∷ Sb2-1-0-4 ∷ []) (Sb1-2-0-4 ∷ Sw12 ∷ [])
  (re 1 1 (CS01 ∷ []) ∷
   rw 0 (q27 c4) ∷
   re 0 1 (Sb1-2-0-4 ∷ []) ∷ []) Eq.refl

-- nat 1 CSd01: 2 steps
lem-nat-1-CSd01 : WsL → ⟪ (Sw12 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CSd01 c4 = derive (Sw12 ∷ CS01⁻ ∷ []) (CS02⁻ ∷ Sw12 ∷ [])
  (rw⁻ 2 (q11 c4) ∷
   re 0 3 (CS02⁻ ∷ []) ∷ []) Eq.refl

private
  q28 : WsL → Eqn
  q28 c4 = eqn (Sw12 ∷ CS01⁻ ∷ []) (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4)

-- nat 1 SBOXd(2;1;0;4): 3 steps
lem-nat-1-SBOXd⟨2·1·0·4⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-1-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-0-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·1·0·4⟩ c4 = derive (Sw12 ∷ Sb⁻2-1-0-4 ∷ []) (Sb⁻1-2-0-4 ∷ Sw12 ∷ [])
  (re 1 1 (CS01⁻ ∷ []) ∷
   rw 0 (q28 c4) ∷
   re 0 1 (Sb⁻1-2-0-4 ∷ []) ∷ []) Eq.refl

private
  q29 : WsL → Eqn
  q29 c4 = eqn (Sw12 ∷ Bx2-1340 ∷ []) (Bx1-2340 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1340⟩ c4)
  q30 : WsL → Eqn
  q30 c4 = eqn (Sw12 ∷ Toff034 ∷ []) (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4)
  q31 : WsL → Eqn
  q31 c4 = eqn (Sw12 ∷ Sb2-1-0-4 ∷ []) (Sb1-2-0-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·1·0·4⟩ c4)
  q32 : WsL → Eqn
  q32 c4 = eqn (Sw12 ∷ Sb⁻2-1-0-4 ∷ []) (Sb⁻1-2-0-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·1·0·4⟩ c4)

-- nat 1 SBOX(2;1;34;0): 7 steps
lem-nat-1-SBOX⟨2·1·34·0⟩ : WsL → ⟪ (Sw12 ∷ Sb2-1-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-34-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·1·34·0⟩ c4 = derive (Sw12 ∷ Sb2-1-34-0 ∷ []) (Sb1-2-34-0 ∷ Sw12 ∷ [])
  (re 1 1 (Bx2-1340 ∷ Toff034 ∷ Sb2-1-0-4 ∷ Toff034 ∷ Sb⁻2-1-0-4 ∷ []) ∷
   rw 0 (q29 c4) ∷
   rw 1 (q30 c4) ∷
   rw 2 (q31 c4) ∷
   rw 3 (q30 c4) ∷
   rw 4 (q32 c4) ∷
   re 0 5 (Sb1-2-34-0 ∷ []) ∷ []) Eq.refl

private
  q33 : WsL → Eqn
  q33 c4 = eqn (CZ12 ∷ Sw01 ∷ []) (Sw01 ∷ CZ02 ∷ []) (wl0137 c4)

-- nat 0 BOX(1;20): 3 steps
lem-nat-0-BOX⟨1·20⟩ : WsL → ⟪ (Sw01 ∷ Bx1-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-21 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·20⟩ c4 = derive (Sw01 ∷ Bx1-20 ∷ []) (Bx0-21 ∷ Sw01 ∷ [])
  (re 1 1 (CZ02 ∷ []) ∷
   rw⁻ 0 (q33 c4) ∷
   re 0 1 (Bx0-21 ∷ []) ∷ []) Eq.refl

private
  q34 : WsL → Eqn
  q34 c4 = eqn (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4)
  q35 : WsL → Eqn
  q35 c4 = eqn (Sw01 ∷ Toff214 ∷ []) (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4)
  q36 : WsL → Eqn
  q36 c4 = eqn (Sw01 ∷ Bx1-20 ∷ []) (Bx0-21 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·20⟩ c4)

-- nat 0 BOX(2;140): 8 steps
lem-nat-0-BOX⟨2·140⟩ : WsL → ⟪ (Sw01 ∷ Bx2-140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-041 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·140⟩ c4 = derive (Sw01 ∷ Bx2-140 ∷ []) (Bx2-041 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-20 ∷ Toff214 ∷ CCZ124 ∷ Bx1-20 ∷ []) ∷
   rw 0 (q34 c4) ∷
   rw 1 (q35 c4) ∷
   rw 2 (q36 c4) ∷
   rw 3 (q35 c4) ∷
   rw 4 (q34 c4) ∷
   rw 5 (q36 c4) ∷
   re 0 6 (Bx2-041 ∷ []) ∷ []) Eq.refl

private
  q37 : WsL → Eqn
  q37 c4 = eqn (CCZ023 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ123 ∷ []) (wl0003 c4)
  q38 : WsL → Eqn
  q38 c4 = eqn (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) (wl0053 c4)
  q39 : WsL → Eqn
  q39 c4 = eqn (Sw01 ∷ Bx2-140 ∷ []) (Bx2-041 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·140⟩ c4)

-- nat 0 BOX(1;2340): 8 steps
lem-nat-0-BOX⟨1·2340⟩ : WsL → ⟪ (Sw01 ∷ Bx1-2340 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·2340⟩ c4 = derive (Sw01 ∷ Bx1-2340 ∷ []) (Bx0-2341 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-140 ∷ Toff123 ∷ CCZ123 ∷ Bx2-140 ∷ []) ∷
   rw⁻ 0 (q37 c4) ∷
   rw 1 (q38 c4) ∷
   rw 2 (q39 c4) ∷
   rw 3 (q38 c4) ∷
   rw⁻ 4 (q37 c4) ∷
   rw 5 (q39 c4) ∷
   re 0 6 (Bx0-2341 ∷ []) ∷ []) Eq.refl

private
  q40 : WsL → Eqn
  q40 c4 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wl0076 c4)
  q41 : WsL → Eqn
  q41 c4 = eqn (Sw01 ∷ CS34 ∷ []) (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))
  q42 : WsL → Eqn
  q42 c4 = eqn (CX13 ∷ Sw01 ∷ []) (Sw01 ∷ CX03 ∷ []) (wl0081 c4)
  q43 : WsL → Eqn
  q43 c4 = eqn (Sw01 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑))
  q44 : WsL → Eqn
  q44 c4 = eqn (Sw01 ∷ Sw34 ∷ []) (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑))
  q45 : WsL → Eqn
  q45 c4 = eqn (CS13 ∷ Sw01 ∷ []) (Sw01 ∷ CS03 ∷ []) (wl0061 c4)
  q46 : WsL → Eqn
  q46 c4 = eqn (Sw01 ∷ ι ∷ []) (ι ∷ Sw01 ∷ []) (wl0030 c4)
  q47 : WsL → Eqn
  q47 c4 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (c₂ (K ↑) (Swap))
  q48 : WsL → Eqn
  q48 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl0021 c4)
  q49 : WsL → Eqn
  q49 c4 = eqn (K1 ∷ Sw34 ∷ []) (Sw34 ∷ K1 ∷ []) (c₂ (K ↑) (Swap ↑))
  q50 : WsL → Eqn
  q50 c4 = eqn (CX12 ∷ Sw34 ∷ []) (Sw34 ∷ CX12 ∷ []) (c₃ (CX₀₁ ↑) (Swap))
  q51 : WsL → Eqn
  q51 c4 = eqn (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wl0032 c4)

-- nat 0 TOFF034: 100 steps
lem-nat-0-TOFF034 : WsL → ⟪ (Sw01 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF034 c4 = derive (Sw01 ∷ Toff034 ∷ []) (Toff134 ∷ Sw01 ∷ [])
  (re 1 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) ∷
   re 3 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   re 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 (q3 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 (q3 c4) ∷
   rw⁻ 11 (q2 c4) ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 (q1 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw 12 (q2 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CS14 ∷ []) ∷
   rw⁻ 5 (q7 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 6 3 (CS14⁻ ∷ []) ∷
   rw⁻ 7 (q7 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   re 8 3 (CS04 ∷ []) ∷
   rw⁻ 9 (q5 c4) ∷
   rw⁻ 10 (q8 c4) ∷
   rw 11 (q6 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   rw⁻ 6 (q11 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw⁻ 5 (q12 c4) ∷
   rw⁻ 8 (q11 c4) ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q13 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw 9 (q13 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q9 c4) ∷
   rw⁻ 9 (q15 c4) ∷
   rw 10 (q11 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q16 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (CX03 ∷ []) ∷
   rw⁻ 4 (q17 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (CX03 ∷ []) ∷
   re 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 6 (q18 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw⁻ 10 (q13 c4) ∷
   rw⁻ 11 (q18 c4) ∷
   re 6 7 (CS04 ∷ []) ∷
   rw⁻ 7 (q1 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw 9 (q2 c4) ∷
   rw⁻ 0 (q40 c4) ∷
   rw 1 (q41 c4) ∷
   rw⁻ 2 (q42 c4) ∷
   rw 3 (q43 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q44 c4) ∷
   rw⁻ 6 (q45 c4) ∷
   rw 7 (q44 c4) ∷
   re 5 3 (CS14 ∷ []) ∷
   rw⁻ 6 (q40 c4) ∷
   rw 7 (q46 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw⁻ 1 (q47 c4) ∷
   rw⁻ 2 (q23 c4) ∷
   re 4 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 4 (q24 c4) ∷
   re 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 5 (q2 c4) ∷
   rw⁻ 6 (q48 c4) ∷
   rw⁻ 7 (q47 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw⁻ 2 (q49 c4) ∷
   re 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q50 c4) ∷
   re 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q50 c4) ∷
   re 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 7 (q6 c4) ∷
   rw⁻ 8 (q49 c4) ∷
   rw⁻ 9 (q8 c4) ∷
   rw 2 (q51 c4) ∷
   re 2 8 (Toff123 ∷ []) ∷
   re 1 3 (Toff124 ∷ []) ∷
   re 0 3 (Toff134 ∷ []) ∷ []) Eq.refl

private
  q52 : WsL → Eqn
  q52 c4 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wl0138 c4)

-- nat 0 SBOX(1;2;0;4): 3 steps
lem-nat-0-SBOX⟨1·2·0·4⟩ : WsL → ⟪ (Sw01 ∷ Sb1-2-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·2·0·4⟩ c4 = derive (Sw01 ∷ Sb1-2-0-4 ∷ []) (Sb0-2-1-4 ∷ Sw01 ∷ [])
  (re 1 1 (CS02 ∷ []) ∷
   rw⁻ 0 (q52 c4) ∷
   re 0 1 (Sb0-2-1-4 ∷ []) ∷ []) Eq.refl

private
  q53 : WsL → Eqn
  q53 c4 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wl0139 c4)

-- nat 0 SBOXd(1;2;0;4): 3 steps
lem-nat-0-SBOXd⟨1·2·0·4⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻1-2-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·2·0·4⟩ c4 = derive (Sw01 ∷ Sb⁻1-2-0-4 ∷ []) (Sb⁻0-2-1-4 ∷ Sw01 ∷ [])
  (re 1 1 (CS02⁻ ∷ []) ∷
   rw⁻ 0 (q53 c4) ∷
   re 0 1 (Sb⁻0-2-1-4 ∷ []) ∷ []) Eq.refl

private
  q54 : WsL → Eqn
  q54 c4 = eqn (Sw01 ∷ Bx1-2340 ∷ []) (Bx0-2341 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2340⟩ c4)
  q55 : WsL → Eqn
  q55 c4 = eqn (Sw01 ∷ Toff034 ∷ []) (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4)
  q56 : WsL → Eqn
  q56 c4 = eqn (Sw01 ∷ Sb1-2-0-4 ∷ []) (Sb0-2-1-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·0·4⟩ c4)
  q57 : WsL → Eqn
  q57 c4 = eqn (Sw01 ∷ Sb⁻1-2-0-4 ∷ []) (Sb⁻0-2-1-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·2·0·4⟩ c4)

-- nat 0 SBOX(1;2;34;0): 7 steps
lem-nat-0-SBOX⟨1·2·34·0⟩ : WsL → ⟪ (Sw01 ∷ Sb1-2-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-34-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·2·34·0⟩ c4 = derive (Sw01 ∷ Sb1-2-34-0 ∷ []) (Sb0-2-34-1 ∷ Sw01 ∷ [])
  (re 1 1 (Bx1-2340 ∷ Toff034 ∷ Sb1-2-0-4 ∷ Toff034 ∷ Sb⁻1-2-0-4 ∷ []) ∷
   rw 0 (q54 c4) ∷
   rw 1 (q55 c4) ∷
   rw 2 (q56 c4) ∷
   rw 3 (q55 c4) ∷
   rw 4 (q57 c4) ∷
   re 0 5 (Sb0-2-34-1 ∷ []) ∷ []) Eq.refl

private
  q58 : WsL → Eqn
  q58 c4 = eqn (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) (wl0140 c4)
  q59 : WsL → Eqn
  q59 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 c4)
  q60 : WsL → Eqn
  q60 c4 = eqn (Sw01 ∷ Toff234 ∷ []) (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff))

-- resp TOFF134 at 2: 4 steps
lem-resp-TOFF134-at-2 : WsL → ⟪ (Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff234 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF134-at-2 c4 = derive (Toff134 ∷ []) (Sw12 ∷ Sw01 ∷ Toff234 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q11 c4) ∷
   rw⁻ 0 (q58 c4) ∷
   rw⁻ 2 (q59 c4) ∷
   rw⁻ 1 (q60 c4) ∷ []) Eq.refl

private
  q61 : WsL → Eqn
  q61 c4 = eqn (Sw01 ∷ Bx1-32 ∷ []) (Bx1-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ))

-- nat 0 BOX(1;32): 2 steps
lem-nat-0-BOX⟨1·32⟩ : WsL → ⟪ (Sw01 ∷ Bx1-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-32 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·32⟩ c4 = derive (Sw01 ∷ Bx1-32 ∷ []) (Bx0-32 ∷ Sw01 ∷ [])
  (rw 0 (q61 c4) ∷
   re 0 1 (Bx0-32 ∷ []) ∷ []) Eq.refl

private
  q62 : WsL → Eqn
  q62 c4 = eqn (Sw01 ∷ CCZ134 ∷ []) (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4)
  q63 : WsL → Eqn
  q63 c4 = eqn (Sw01 ∷ Toff314 ∷ []) (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4)
  q64 : WsL → Eqn
  q64 c4 = eqn (Sw01 ∷ Bx1-32 ∷ []) (Bx0-32 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·32⟩ c4)

-- nat 0 BOX(3;142): 8 steps
lem-nat-0-BOX⟨3·142⟩ : WsL → ⟪ (Sw01 ∷ Bx3-142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-042 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·142⟩ c4 = derive (Sw01 ∷ Bx3-142 ∷ []) (Bx3-042 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-32 ∷ Toff314 ∷ CCZ134 ∷ Bx1-32 ∷ []) ∷
   rw 0 (q62 c4) ∷
   rw 1 (q63 c4) ∷
   rw 2 (q64 c4) ∷
   rw 3 (q63 c4) ∷
   rw 4 (q62 c4) ∷
   rw 5 (q64 c4) ∷
   re 0 6 (Bx3-042 ∷ []) ∷ []) Eq.refl

private
  q65 : WsL → Eqn
  q65 c4 = eqn (CCZ013 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ013 ∷ []) (wl0100 c4)
  q66 : WsL → Eqn
  q66 c4 = eqn (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) (wl0102 c4)
  q67 : WsL → Eqn
  q67 c4 = eqn (Sw01 ∷ Bx3-142 ∷ []) (Bx3-042 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·142⟩ c4)

-- nat 0 BOX(1;3042): 8 steps
lem-nat-0-BOX⟨1·3042⟩ : WsL → ⟪ (Sw01 ∷ Bx1-3042 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·3042⟩ c4 = derive (Sw01 ∷ Bx1-3042 ∷ []) (Bx0-3142 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-142 ∷ Toff103 ∷ CCZ013 ∷ Bx3-142 ∷ []) ∷
   rw⁻ 0 (q65 c4) ∷
   rw 1 (q66 c4) ∷
   rw 2 (q67 c4) ∷
   rw 3 (q66 c4) ∷
   rw⁻ 4 (q65 c4) ∷
   rw 5 (q67 c4) ∷
   re 0 6 (Bx0-3142 ∷ []) ∷ []) Eq.refl

private
  q68 : WsL → Eqn
  q68 c4 = eqn (CZ23 ∷ Sw12 ∷ []) (Sw12 ∷ CZ13 ∷ []) (wl0029 c4)

-- nat 1 BOX(2;31): 3 steps
lem-nat-1-BOX⟨2·31⟩ : WsL → ⟪ (Sw12 ∷ Bx2-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-32 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·31⟩ c4 = derive (Sw12 ∷ Bx2-31 ∷ []) (Bx1-32 ∷ Sw12 ∷ [])
  (re 1 1 (CZ13 ∷ []) ∷
   rw⁻ 0 (q68 c4) ∷
   re 0 1 (Bx1-32 ∷ []) ∷ []) Eq.refl

private
  q69 : WsL → Eqn
  q69 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl0034 c4)
  q70 : WsL → Eqn
  q70 c4 = eqn (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) (wl0063 c4)
  q71 : WsL → Eqn
  q71 c4 = eqn (Sw12 ∷ Bx2-31 ∷ []) (Bx1-32 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·31⟩ c4)

-- nat 1 BOX(3;241): 8 steps
lem-nat-1-BOX⟨3·241⟩ : WsL → ⟪ (Sw12 ∷ Bx3-241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-142 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·241⟩ c4 = derive (Sw12 ∷ Bx3-241 ∷ []) (Bx3-142 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ []) ∷
   rw⁻ 0 (q69 c4) ∷
   rw 1 (q70 c4) ∷
   rw 2 (q71 c4) ∷
   rw 3 (q70 c4) ∷
   rw⁻ 4 (q69 c4) ∷
   rw 5 (q71 c4) ∷
   re 0 6 (Bx3-142 ∷ []) ∷ []) Eq.refl

private
  q72 : WsL → Eqn
  q72 c4 = eqn (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4)
  q73 : WsL → Eqn
  q73 c4 = eqn (Sw12 ∷ Toff203 ∷ []) (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4)
  q74 : WsL → Eqn
  q74 c4 = eqn (Sw12 ∷ Bx3-241 ∷ []) (Bx3-142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·241⟩ c4)

-- nat 1 BOX(2;3041): 8 steps
lem-nat-1-BOX⟨2·3041⟩ : WsL → ⟪ (Sw12 ∷ Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3042 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·3041⟩ c4 = derive (Sw12 ∷ Bx2-3041 ∷ []) (Bx1-3042 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-241 ∷ Toff203 ∷ CCZ023 ∷ Bx3-241 ∷ []) ∷
   rw 0 (q72 c4) ∷
   rw 1 (q73 c4) ∷
   rw 2 (q74 c4) ∷
   rw 3 (q73 c4) ∷
   rw 4 (q72 c4) ∷
   rw 5 (q74 c4) ∷
   re 0 6 (Bx1-3042 ∷ []) ∷ []) Eq.refl

private
  q75 : WsL → Eqn
  q75 c4 = eqn (Sw12 ∷ CZ02 ∷ []) (CZ01 ∷ Sw12 ∷ []) (lem-nat-1-CZ02 c4)

-- nat 1 BOX(1;02): 3 steps
lem-nat-1-BOX⟨1·02⟩ : WsL → ⟪ (Sw12 ∷ Bx1-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-01 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·02⟩ c4 = derive (Sw12 ∷ Bx1-02 ∷ []) (Bx2-01 ∷ Sw12 ∷ [])
  (re 1 1 (CZ02 ∷ []) ∷
   rw 0 (q75 c4) ∷
   re 0 1 (Bx2-01 ∷ []) ∷ []) Eq.refl

private
  q76 : WsL → Eqn
  q76 c4 = eqn (Sw12 ∷ CCZ014 ∷ []) (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4)
  q77 : WsL → Eqn
  q77 c4 = eqn (Sw12 ∷ Toff014 ∷ []) (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4)
  q78 : WsL → Eqn
  q78 c4 = eqn (Sw12 ∷ Bx1-02 ∷ []) (Bx2-01 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·02⟩ c4)

-- nat 1 BOX(0;142): 8 steps
lem-nat-1-BOX⟨0·142⟩ : WsL → ⟪ (Sw12 ∷ Bx0-142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-241 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·142⟩ c4 = derive (Sw12 ∷ Bx0-142 ∷ []) (Bx0-241 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-02 ∷ Toff014 ∷ CCZ014 ∷ Bx1-02 ∷ []) ∷
   rw 0 (q76 c4) ∷
   rw 1 (q77 c4) ∷
   rw 2 (q78 c4) ∷
   rw 3 (q77 c4) ∷
   rw 4 (q76 c4) ∷
   rw 5 (q78 c4) ∷
   re 0 6 (Bx0-241 ∷ []) ∷ []) Eq.refl

private
  q79 : WsL → Eqn
  q79 c4 = eqn (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4)
  q80 : WsL → Eqn
  q80 c4 = eqn (Sw12 ∷ Toff103 ∷ []) (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4)
  q81 : WsL → Eqn
  q81 c4 = eqn (Sw12 ∷ Bx0-142 ∷ []) (Bx0-241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·142⟩ c4)

-- nat 1 BOX(1;0342): 8 steps
lem-nat-1-BOX⟨1·0342⟩ : WsL → ⟪ (Sw12 ∷ Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·0342⟩ c4 = derive (Sw12 ∷ Bx1-0342 ∷ []) (Bx2-0341 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-142 ∷ Toff103 ∷ CCZ013 ∷ Bx0-142 ∷ []) ∷
   rw 0 (q79 c4) ∷
   rw 1 (q80 c4) ∷
   rw 2 (q81 c4) ∷
   rw 3 (q80 c4) ∷
   rw 4 (q79 c4) ∷
   rw 5 (q81 c4) ∷
   re 0 6 (Bx2-0341 ∷ []) ∷ []) Eq.refl

-- nat 0 BOX(1;02): 3 steps
lem-nat-0-BOX⟨1·02⟩ : WsL → ⟪ (Sw01 ∷ Bx1-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-12 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·02⟩ c4 = derive (Sw01 ∷ Bx1-02 ∷ []) (Bx0-12 ∷ Sw01 ∷ [])
  (re 1 1 (CZ02 ∷ []) ∷
   rw⁻ 0 (q33 c4) ∷
   re 0 1 (Bx0-12 ∷ []) ∷ []) Eq.refl

private
  q82 : WsL → Eqn
  q82 c4 = eqn (Sw01 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4)
  q83 : WsL → Eqn
  q83 c4 = eqn (Sw01 ∷ Toff014 ∷ []) (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4)
  q84 : WsL → Eqn
  q84 c4 = eqn (Sw01 ∷ Bx1-02 ∷ []) (Bx0-12 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·02⟩ c4)

-- nat 0 BOX(0;142): 8 steps
lem-nat-0-BOX⟨0·142⟩ : WsL → ⟪ (Sw01 ∷ Bx0-142 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-042 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·142⟩ c4 = derive (Sw01 ∷ Bx0-142 ∷ []) (Bx1-042 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-02 ∷ Toff014 ∷ CCZ014 ∷ Bx1-02 ∷ []) ∷
   rw 0 (q82 c4) ∷
   rw 1 (q83 c4) ∷
   rw 2 (q84 c4) ∷
   rw 3 (q83 c4) ∷
   rw 4 (q82 c4) ∷
   rw 5 (q84 c4) ∷
   re 0 6 (Bx1-042 ∷ []) ∷ []) Eq.refl

private
  q85 : WsL → Eqn
  q85 c4 = eqn (Sw01 ∷ Bx0-142 ∷ []) (Bx1-042 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·142⟩ c4)

-- nat 0 BOX(1;0342): 8 steps
lem-nat-0-BOX⟨1·0342⟩ : WsL → ⟪ (Sw01 ∷ Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·0342⟩ c4 = derive (Sw01 ∷ Bx1-0342 ∷ []) (Bx0-1342 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-142 ∷ Toff103 ∷ CCZ013 ∷ Bx0-142 ∷ []) ∷
   rw⁻ 0 (q65 c4) ∷
   rw 1 (q66 c4) ∷
   rw 2 (q85 c4) ∷
   rw 3 (q66 c4) ∷
   rw⁻ 4 (q65 c4) ∷
   rw 5 (q85 c4) ∷
   re 0 6 (Bx0-1342 ∷ []) ∷ []) Eq.refl

private
  q86 : WsL → Eqn
  q86 c4 = eqn (Sw12 ∷ CZ01 ∷ []) (CZ02 ∷ Sw12 ∷ []) (lem-nat-1-CZ01 c4)

-- nat 1 BOX(2;01): 3 steps
lem-nat-1-BOX⟨2·01⟩ : WsL → ⟪ (Sw12 ∷ Bx2-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-02 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·01⟩ c4 = derive (Sw12 ∷ Bx2-01 ∷ []) (Bx1-02 ∷ Sw12 ∷ [])
  (re 1 1 (CZ01 ∷ []) ∷
   rw 0 (q86 c4) ∷
   re 0 1 (Bx1-02 ∷ []) ∷ []) Eq.refl

private
  q87 : WsL → Eqn
  q87 c4 = eqn (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4)
  q88 : WsL → Eqn
  q88 c4 = eqn (Sw12 ∷ Toff024 ∷ []) (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4)
  q89 : WsL → Eqn
  q89 c4 = eqn (Sw12 ∷ Bx2-01 ∷ []) (Bx1-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·01⟩ c4)

-- nat 1 BOX(0;241): 8 steps
lem-nat-1-BOX⟨0·241⟩ : WsL → ⟪ (Sw12 ∷ Bx0-241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-142 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·241⟩ c4 = derive (Sw12 ∷ Bx0-241 ∷ []) (Bx0-142 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) ∷
   rw 0 (q87 c4) ∷
   rw 1 (q88 c4) ∷
   rw 2 (q89 c4) ∷
   rw 3 (q88 c4) ∷
   rw 4 (q87 c4) ∷
   rw 5 (q89 c4) ∷
   re 0 6 (Bx0-142 ∷ []) ∷ []) Eq.refl

private
  q90 : WsL → Eqn
  q90 c4 = eqn (Sw12 ∷ Bx0-241 ∷ []) (Bx0-142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·241⟩ c4)

-- nat 1 BOX(2;0341): 8 steps
lem-nat-1-BOX⟨2·0341⟩ : WsL → ⟪ (Sw12 ∷ Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0342 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·0341⟩ c4 = derive (Sw12 ∷ Bx2-0341 ∷ []) (Bx1-0342 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-241 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ []) ∷
   rw 0 (q72 c4) ∷
   rw 1 (q73 c4) ∷
   rw 2 (q90 c4) ∷
   rw 3 (q73 c4) ∷
   rw 4 (q72 c4) ∷
   rw 5 (q90 c4) ∷
   re 0 6 (Bx1-0342 ∷ []) ∷ []) Eq.refl

private
  q91 : WsL → Eqn
  q91 c4 = eqn (CCZ012 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ012 ∷ []) (wl0096 c4)
  q92 : WsL → Eqn
  q92 c4 = eqn (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) (wl0099 c4)
  q93 : WsL → Eqn
  q93 c4 = eqn (Sw01 ∷ Bx1-04 ∷ []) (Bx0-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·04⟩ c4)

-- nat 0 BOX(0;124): 8 steps
lem-nat-0-BOX⟨0·124⟩ : WsL → ⟪ (Sw01 ∷ Bx0-124 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-024 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·124⟩ c4 = derive (Sw01 ∷ Bx0-124 ∷ []) (Bx1-024 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-04 ∷ Toff012 ∷ CCZ012 ∷ Bx1-04 ∷ []) ∷
   rw⁻ 0 (q91 c4) ∷
   rw 1 (q92 c4) ∷
   rw 2 (q93 c4) ∷
   rw 3 (q92 c4) ∷
   rw⁻ 4 (q91 c4) ∷
   rw 5 (q93 c4) ∷
   re 0 6 (Bx1-024 ∷ []) ∷ []) Eq.refl

private
  q94 : WsL → Eqn
  q94 c4 = eqn (Sw01 ∷ Bx0-124 ∷ []) (Bx1-024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·124⟩ c4)

-- nat 0 BOX(1;0324): 8 steps
lem-nat-0-BOX⟨1·0324⟩ : WsL → ⟪ (Sw01 ∷ Bx1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·0324⟩ c4 = derive (Sw01 ∷ Bx1-0324 ∷ []) (Bx0-1324 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-124 ∷ Toff103 ∷ CCZ013 ∷ Bx0-124 ∷ []) ∷
   rw⁻ 0 (q65 c4) ∷
   rw 1 (q66 c4) ∷
   rw 2 (q94 c4) ∷
   rw 3 (q66 c4) ∷
   rw⁻ 4 (q65 c4) ∷
   rw 5 (q94 c4) ∷
   re 0 6 (Bx0-1324 ∷ []) ∷ []) Eq.refl

private
  q95 : WsL → Eqn
  q95 c4 = eqn (CCZ012 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ012 ∷ []) (wl0037 c4)
  q96 : WsL → Eqn
  q96 c4 = eqn (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) (wl0038 c4)
  q97 : WsL → Eqn
  q97 c4 = eqn (Sw12 ∷ Bx2-04 ∷ []) (Bx1-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·04⟩ c4)

-- nat 1 BOX(0;214): 8 steps
lem-nat-1-BOX⟨0·214⟩ : WsL → ⟪ (Sw12 ∷ Bx0-214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-124 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·214⟩ c4 = derive (Sw12 ∷ Bx0-214 ∷ []) (Bx0-124 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) ∷
   rw⁻ 0 (q95 c4) ∷
   rw 1 (q96 c4) ∷
   rw 2 (q97 c4) ∷
   rw 3 (q96 c4) ∷
   rw⁻ 4 (q95 c4) ∷
   rw 5 (q97 c4) ∷
   re 0 6 (Bx0-124 ∷ []) ∷ []) Eq.refl

private
  q98 : WsL → Eqn
  q98 c4 = eqn (Sw12 ∷ Bx0-214 ∷ []) (Bx0-124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·214⟩ c4)

-- nat 1 BOX(2;0314): 8 steps
lem-nat-1-BOX⟨2·0314⟩ : WsL → ⟪ (Sw12 ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·0314⟩ c4 = derive (Sw12 ∷ Bx2-0314 ∷ []) (Bx1-0324 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ []) ∷
   rw 0 (q72 c4) ∷
   rw 1 (q73 c4) ∷
   rw 2 (q98 c4) ∷
   rw 3 (q73 c4) ∷
   rw 4 (q72 c4) ∷
   rw 5 (q98 c4) ∷
   re 0 6 (Bx1-0324 ∷ []) ∷ []) Eq.refl

private
  q99 : WsL → Eqn
  q99 c4 = eqn (Sw01 ∷ Bx0-32 ∷ []) (Bx0-32 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ))

-- nat 0 BOX(0;32): 2 steps
lem-nat-0-BOX⟨0·32⟩ : WsL → ⟪ (Sw01 ∷ Bx0-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-32 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·32⟩ c4 = derive (Sw01 ∷ Bx0-32 ∷ []) (Bx1-32 ∷ Sw01 ∷ [])
  (rw 0 (q99 c4) ∷
   re 0 1 (Bx1-32 ∷ []) ∷ []) Eq.refl

private
  q100 : WsL → Eqn
  q100 c4 = eqn (Sw01 ∷ CCZ034 ∷ []) (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4)
  q101 : WsL → Eqn
  q101 c4 = eqn (Sw01 ∷ Toff304 ∷ []) (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4)
  q102 : WsL → Eqn
  q102 c4 = eqn (Sw01 ∷ Bx0-32 ∷ []) (Bx1-32 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·32⟩ c4)

-- nat 0 BOX(3;042): 8 steps
lem-nat-0-BOX⟨3·042⟩ : WsL → ⟪ (Sw01 ∷ Bx3-042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-142 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·042⟩ c4 = derive (Sw01 ∷ Bx3-042 ∷ []) (Bx3-142 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) ∷
   rw 0 (q100 c4) ∷
   rw 1 (q101 c4) ∷
   rw 2 (q102 c4) ∷
   rw 3 (q101 c4) ∷
   rw 4 (q100 c4) ∷
   rw 5 (q102 c4) ∷
   re 0 6 (Bx3-142 ∷ []) ∷ []) Eq.refl

private
  q103 : WsL → Eqn
  q103 c4 = eqn (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) (wl0101 c4)
  q104 : WsL → Eqn
  q104 c4 = eqn (Sw01 ∷ Bx3-042 ∷ []) (Bx3-142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·042⟩ c4)

-- nat 0 BOX(0;3142): 8 steps
lem-nat-0-BOX⟨0·3142⟩ : WsL → ⟪ (Sw01 ∷ Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3042 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·3142⟩ c4 = derive (Sw01 ∷ Bx0-3142 ∷ []) (Bx1-3042 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) ∷
   rw⁻ 0 (q65 c4) ∷
   rw 1 (q103 c4) ∷
   rw 2 (q104 c4) ∷
   rw 3 (q103 c4) ∷
   rw⁻ 4 (q65 c4) ∷
   rw 5 (q104 c4) ∷
   re 0 6 (Bx1-3042 ∷ []) ∷ []) Eq.refl

private
  q105 : WsL → Eqn
  q105 c4 = eqn (CZ13 ∷ Sw12 ∷ []) (Sw12 ∷ CZ23 ∷ []) (wl0026 c4)

-- nat 1 BOX(1;32): 3 steps
lem-nat-1-BOX⟨1·32⟩ : WsL → ⟪ (Sw12 ∷ Bx1-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-31 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·32⟩ c4 = derive (Sw12 ∷ Bx1-32 ∷ []) (Bx2-31 ∷ Sw12 ∷ [])
  (re 1 1 (CZ23 ∷ []) ∷
   rw⁻ 0 (q105 c4) ∷
   re 0 1 (Bx2-31 ∷ []) ∷ []) Eq.refl

private
  q106 : WsL → Eqn
  q106 c4 = eqn (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) (wl0084 c4)
  q107 : WsL → Eqn
  q107 c4 = eqn (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) (wl0064 c4)
  q108 : WsL → Eqn
  q108 c4 = eqn (Sw12 ∷ Bx1-32 ∷ []) (Bx2-31 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·32⟩ c4)

-- nat 1 BOX(3;142): 8 steps
lem-nat-1-BOX⟨3·142⟩ : WsL → ⟪ (Sw12 ∷ Bx3-142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-241 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·142⟩ c4 = derive (Sw12 ∷ Bx3-142 ∷ []) (Bx3-241 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-32 ∷ Toff314 ∷ CCZ134 ∷ Bx1-32 ∷ []) ∷
   rw⁻ 0 (q106 c4) ∷
   rw 1 (q107 c4) ∷
   rw 2 (q108 c4) ∷
   rw 3 (q107 c4) ∷
   rw⁻ 4 (q106 c4) ∷
   rw 5 (q108 c4) ∷
   re 0 6 (Bx3-241 ∷ []) ∷ []) Eq.refl

private
  q109 : WsL → Eqn
  q109 c4 = eqn (Sw12 ∷ Bx3-142 ∷ []) (Bx3-241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·142⟩ c4)

-- nat 1 BOX(1;3042): 8 steps
lem-nat-1-BOX⟨1·3042⟩ : WsL → ⟪ (Sw12 ∷ Bx1-3042 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·3042⟩ c4 = derive (Sw12 ∷ Bx1-3042 ∷ []) (Bx2-3041 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-142 ∷ Toff103 ∷ CCZ013 ∷ Bx3-142 ∷ []) ∷
   rw 0 (q79 c4) ∷
   rw 1 (q80 c4) ∷
   rw 2 (q109 c4) ∷
   rw 3 (q80 c4) ∷
   rw 4 (q79 c4) ∷
   rw 5 (q109 c4) ∷
   re 0 6 (Bx2-3041 ∷ []) ∷ []) Eq.refl

-- nat 3 TOFF412: 2 steps
lem-nat-3-TOFF412 : WsL → ⟪ (Sw34 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF412 c4 = derive (Sw34 ∷ Toff412 ∷ []) (Toff312 ∷ Sw34 ∷ [])
  (re 1 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) ∷
   rw 0 (q6 c4) ∷ []) Eq.refl

-- nat 3 CS04: 2 steps
lem-nat-3-CS04 : WsL → ⟪ (Sw34 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CS04 c4 = derive (Sw34 ∷ CS04 ∷ []) (CS03 ∷ Sw34 ∷ [])
  (re 1 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 0 (q6 c4) ∷ []) Eq.refl

private
  q110 : WsL → Eqn
  q110 c4 = eqn (Sw34 ∷ CS04 ∷ []) (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 c4)

-- nat 3 SBOX(2;0;4;1): 3 steps
lem-nat-3-SBOX⟨2·0·4·1⟩ : WsL → ⟪ (Sw34 ∷ Sb2-0-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-3-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·0·4·1⟩ c4 = derive (Sw34 ∷ Sb2-0-4-1 ∷ []) (Sb2-0-3-1 ∷ Sw34 ∷ [])
  (re 1 1 (CS04 ∷ []) ∷
   rw 0 (q110 c4) ∷
   re 0 1 (Sb2-0-3-1 ∷ []) ∷ []) Eq.refl

-- nat 3 CSd04: 2 steps
lem-nat-3-CSd04 : WsL → ⟪ (Sw34 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CSd04 c4 = derive (Sw34 ∷ CS04⁻ ∷ []) (CS03⁻ ∷ Sw34 ∷ [])
  (re 1 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw 0 (q6 c4) ∷ []) Eq.refl

private
  q111 : WsL → Eqn
  q111 c4 = eqn (Sw34 ∷ CS04⁻ ∷ []) (CS03⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd04 c4)

-- nat 3 SBOXd(2;0;4;1): 3 steps
lem-nat-3-SBOXd⟨2·0·4·1⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻2-0-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-3-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·0·4·1⟩ c4 = derive (Sw34 ∷ Sb⁻2-0-4-1 ∷ []) (Sb⁻2-0-3-1 ∷ Sw34 ∷ [])
  (re 1 1 (CS04⁻ ∷ []) ∷
   rw 0 (q111 c4) ∷
   re 0 1 (Sb⁻2-0-3-1 ∷ []) ∷ []) Eq.refl

private
  q112 : WsL → Eqn
  q112 c4 = eqn (Sw34 ∷ Bx2-0314 ∷ []) (Bx2-0413 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·0314⟩ c4)
  q113 : WsL → Eqn
  q113 c4 = eqn (Sw34 ∷ Toff413 ∷ []) (Toff314 ∷ Sw34 ∷ []) (wl0141 c4)
  q114 : WsL → Eqn
  q114 c4 = eqn (Sw34 ∷ Sb2-0-4-1 ∷ []) (Sb2-0-3-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·4·1⟩ c4)
  q115 : WsL → Eqn
  q115 c4 = eqn (Sw34 ∷ Sb⁻2-0-4-1 ∷ []) (Sb⁻2-0-3-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·4·1⟩ c4)

-- nat 3 SBOX(2;0;31;4): 7 steps
lem-nat-3-SBOX⟨2·0·31·4⟩ : WsL → ⟪ (Sw34 ∷ Sb2-0-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·0·31·4⟩ c4 = derive (Sw34 ∷ Sb2-0-31-4 ∷ []) (Sb2-0-41-3 ∷ Sw34 ∷ [])
  (re 1 1 (Bx2-0314 ∷ Toff413 ∷ Sb2-0-4-1 ∷ Toff413 ∷ Sb⁻2-0-4-1 ∷ []) ∷
   rw 0 (q112 c4) ∷
   rw 1 (q113 c4) ∷
   rw 2 (q114 c4) ∷
   rw 3 (q113 c4) ∷
   rw 4 (q115 c4) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q116 : WsL → Eqn
  q116 c4 = eqn (Bx3-02 ∷ Sw34 ∷ []) (Sw34 ∷ Bx3-02 ∷ []) (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))

-- nat 3 BOX(3;02): 2 steps
lem-nat-3-BOX⟨3·02⟩ : WsL → ⟪ (Sw34 ∷ Bx3-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-02 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·02⟩ c4 = derive (Sw34 ∷ Bx3-02 ∷ []) (Bx4-02 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q116 c4) ∷
   re 0 1 (Bx4-02 ∷ []) ∷ []) Eq.refl

private
  q117 : WsL → Eqn
  q117 c4 = eqn (Sw34 ∷ CCZ013 ∷ []) (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4)
  q118 : WsL → Eqn
  q118 c4 = eqn (Sw34 ∷ Toff013 ∷ []) (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4)
  q119 : WsL → Eqn
  q119 c4 = eqn (Sw34 ∷ Bx3-02 ∷ []) (Bx4-02 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·02⟩ c4)

-- nat 3 BOX(0;312): 8 steps
lem-nat-3-BOX⟨0·312⟩ : WsL → ⟪ (Sw34 ∷ Bx0-312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-412 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·312⟩ c4 = derive (Sw34 ∷ Bx0-312 ∷ []) (Bx0-412 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) ∷
   rw 0 (q117 c4) ∷
   rw 1 (q118 c4) ∷
   rw 2 (q119 c4) ∷
   rw 3 (q118 c4) ∷
   rw 4 (q117 c4) ∷
   rw 5 (q119 c4) ∷
   re 0 6 (Bx0-412 ∷ []) ∷ []) Eq.refl

private
  q120 : WsL → Eqn
  q120 c4 = eqn (Sw34 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4)
  q121 : WsL → Eqn
  q121 c4 = eqn (Sw34 ∷ Toff304 ∷ []) (Toff403 ∷ Sw34 ∷ []) (lem-nat-3-TOFF304 c4)
  q122 : WsL → Eqn
  q122 c4 = eqn (Sw34 ∷ Bx0-312 ∷ []) (Bx0-412 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·312⟩ c4)

-- nat 3 BOX(3;0412): 8 steps
lem-nat-3-BOX⟨3·0412⟩ : WsL → ⟪ (Sw34 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0312 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·0412⟩ c4 = derive (Sw34 ∷ Bx3-0412 ∷ []) (Bx4-0312 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) ∷
   rw 0 (q120 c4) ∷
   rw 1 (q121 c4) ∷
   rw 2 (q122 c4) ∷
   rw 3 (q121 c4) ∷
   rw 4 (q120 c4) ∷
   rw 5 (q122 c4) ∷
   re 0 6 (Bx4-0312 ∷ []) ∷ []) Eq.refl

private
  q123 : WsL → Eqn
  q123 c4 = eqn (Sb3-0-2-1 ∷ Sw34 ∷ []) (Sw34 ∷ Sb3-0-2-1 ∷ []) (c₃ (Swap ↑ • CS • Swap ↑) (Swap))

-- nat 3 SBOX(3;0;2;1): 2 steps
lem-nat-3-SBOX⟨3·0·2·1⟩ : WsL → ⟪ (Sw34 ∷ Sb3-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-2-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨3·0·2·1⟩ c4 = derive (Sw34 ∷ Sb3-0-2-1 ∷ []) (Sb4-0-2-1 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q123 c4) ∷
   re 0 1 (Sb4-0-2-1 ∷ []) ∷ []) Eq.refl

private
  q124 : WsL → Eqn
  q124 c4 = eqn (Sb⁻3-0-2-1 ∷ Sw34 ∷ []) (Sw34 ∷ Sb⁻3-0-2-1 ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (Swap))

-- nat 3 SBOXd(3;0;2;1): 2 steps
lem-nat-3-SBOXd⟨3·0·2·1⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻3-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-2-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨3·0·2·1⟩ c4 = derive (Sw34 ∷ Sb⁻3-0-2-1 ∷ []) (Sb⁻4-0-2-1 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q124 c4) ∷
   re 0 1 (Sb⁻4-0-2-1 ∷ []) ∷ []) Eq.refl

private
  q125 : WsL → Eqn
  q125 c4 = eqn (Sw34 ∷ Bx3-0412 ∷ []) (Bx4-0312 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·0412⟩ c4)
  q126 : WsL → Eqn
  q126 c4 = eqn (Sw34 ∷ Toff214 ∷ []) (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 c4)
  q127 : WsL → Eqn
  q127 c4 = eqn (Sw34 ∷ Sb3-0-2-1 ∷ []) (Sb4-0-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨3·0·2·1⟩ c4)
  q128 : WsL → Eqn
  q128 c4 = eqn (Sw34 ∷ Sb⁻3-0-2-1 ∷ []) (Sb⁻4-0-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨3·0·2·1⟩ c4)

-- nat 3 SBOX(3;0;41;2): 7 steps
lem-nat-3-SBOX⟨3·0·41·2⟩ : WsL → ⟪ (Sw34 ∷ Sb3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-31-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨3·0·41·2⟩ c4 = derive (Sw34 ∷ Sb3-0-41-2 ∷ []) (Sb4-0-31-2 ∷ Sw34 ∷ [])
  (re 1 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   rw 0 (q125 c4) ∷
   rw 1 (q126 c4) ∷
   rw 2 (q127 c4) ∷
   rw 3 (q126 c4) ∷
   rw 4 (q128 c4) ∷
   re 0 5 (Sb4-0-31-2 ∷ []) ∷ []) Eq.refl

private
  q129 : WsL → Eqn
  q129 c4 = eqn (Sw12 ∷ CS04 ∷ []) (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 c4)

-- nat 1 SBOX(1;0;4;2): 3 steps
lem-nat-1-SBOX⟨1·0·4·2⟩ : WsL → ⟪ (Sw12 ∷ Sb1-0-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-4-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·0·4·2⟩ c4 = derive (Sw12 ∷ Sb1-0-4-2 ∷ []) (Sb2-0-4-1 ∷ Sw12 ∷ [])
  (re 1 1 (CS04 ∷ []) ∷
   rw 0 (q129 c4) ∷
   re 0 1 (Sb2-0-4-1 ∷ []) ∷ []) Eq.refl

private
  q130 : WsL → Eqn
  q130 c4 = eqn (CS03⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS03⁻ ∷ []) (wl0023 c4)

-- nat 1 CSd04: 5 steps
lem-nat-1-CSd04 : WsL → ⟪ (Sw12 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CSd04 c4 = derive (Sw12 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Sw12 ∷ [])
  (re 1 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw 0 (q13 c4) ∷
   rw⁻ 1 (q130 c4) ∷
   rw 2 (q13 c4) ∷
   re 0 3 (CS04⁻ ∷ []) ∷ []) Eq.refl

private
  q131 : WsL → Eqn
  q131 c4 = eqn (Sw12 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd04 c4)

-- nat 1 SBOXd(1;0;4;2): 3 steps
lem-nat-1-SBOXd⟨1·0·4·2⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-0-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-4-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·0·4·2⟩ c4 = derive (Sw12 ∷ Sb⁻1-0-4-2 ∷ []) (Sb⁻2-0-4-1 ∷ Sw12 ∷ [])
  (re 1 1 (CS04⁻ ∷ []) ∷
   rw 0 (q131 c4) ∷
   re 0 1 (Sb⁻2-0-4-1 ∷ []) ∷ []) Eq.refl

private
  q132 : WsL → Eqn
  q132 c4 = eqn (Sw12 ∷ Bx1-0324 ∷ []) (Bx2-0314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0324⟩ c4)
  q133 : WsL → Eqn
  q133 c4 = eqn (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) (wl0091 c4)
  q134 : WsL → Eqn
  q134 c4 = eqn (Sw12 ∷ Sb1-0-4-2 ∷ []) (Sb2-0-4-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·4·2⟩ c4)
  q135 : WsL → Eqn
  q135 c4 = eqn (Sw12 ∷ Sb⁻1-0-4-2 ∷ []) (Sb⁻2-0-4-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·4·2⟩ c4)

-- nat 1 SBOX(1;0;32;4): 7 steps
lem-nat-1-SBOX⟨1·0·32·4⟩ : WsL → ⟪ (Sw12 ∷ Sb1-0-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-31-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·0·32·4⟩ c4 = derive (Sw12 ∷ Sb1-0-32-4 ∷ []) (Sb2-0-31-4 ∷ Sw12 ∷ [])
  (re 1 1 (Bx1-0324 ∷ Toff423 ∷ Sb1-0-4-2 ∷ Toff423 ∷ Sb⁻1-0-4-2 ∷ []) ∷
   rw 0 (q132 c4) ∷
   rw 1 (q133 c4) ∷
   rw 2 (q134 c4) ∷
   rw 3 (q133 c4) ∷
   rw 4 (q135 c4) ∷
   re 0 5 (Sb2-0-31-4 ∷ []) ∷ []) Eq.refl

private
  q136 : WsL → Eqn
  q136 c4 = eqn (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ []) (wl0057 c4)
  q137 : WsL → Eqn
  q137 c4 = eqn (K4 ∷ Sw34 ∷ []) (Sw34 ∷ K3 ∷ []) (wl0067 c4)
  q138 : WsL → Eqn
  q138 c4 = eqn (Sw12 ∷ K4 ∷ []) (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑))
  q139 : WsL → Eqn
  q139 c4 = eqn (Sw23 ∷ K4 ∷ []) (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K))
  q140 : WsL → Eqn
  q140 c4 = eqn (K3 ∷ Sw34 ∷ []) (Sw34 ∷ K4 ∷ []) (wl0068 c4)
  q141 : WsL → Eqn
  q141 c4 = eqn (K2 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ []) (wl0058 c4)

-- nat 1 TOFF403: 134 steps
lem-nat-1-TOFF403 : WsL → ⟪ (Sw12 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF403 c4 = derive (Sw12 ∷ Toff403 ∷ []) (Toff403 ∷ Sw12 ∷ [])
  (re 1 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) ∷
   re 3 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) ∷
   re 4 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 5 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw⁻ 4 (q136 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 (q3 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 (q3 c4) ∷
   rw⁻ 11 (q2 c4) ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 (q136 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw 12 (q2 c4) ∷
   rw⁻ 3 (q137 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CS14 ∷ []) ∷
   rw⁻ 5 (q7 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 6 3 (CS14⁻ ∷ []) ∷
   rw⁻ 7 (q7 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   re 8 3 (CS04 ∷ []) ∷
   rw⁻ 9 (q137 c4) ∷
   rw⁻ 10 (q8 c4) ∷
   rw 11 (q6 c4) ∷
   rw 2 (q138 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   rw⁻ 6 (q11 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw⁻ 5 (q12 c4) ∷
   rw⁻ 8 (q11 c4) ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q13 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw 9 (q13 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw 8 (q138 c4) ∷
   rw⁻ 9 (q15 c4) ∷
   rw 10 (q11 c4) ∷
   rw 1 (q139 c4) ∷
   rw⁻ 2 (q16 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (CX03 ∷ []) ∷
   rw⁻ 4 (q17 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (CX03 ∷ []) ∷
   re 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 6 (q18 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw⁻ 10 (q13 c4) ∷
   rw⁻ 11 (q18 c4) ∷
   re 6 7 (CS04 ∷ []) ∷
   rw 7 (q139 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw 9 (q2 c4) ∷
   rw 0 (q138 c4) ∷
   rw 1 (q20 c4) ∷
   rw⁻ 2 (q21 c4) ∷
   rw 3 (q22 c4) ∷
   rw⁻ 4 (q21 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q13 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw 7 (q13 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw 6 (q138 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw 1 (q139 c4) ∷
   rw⁻ 2 (q23 c4) ∷
   re 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 4 (q24 c4) ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 5 (q2 c4) ∷
   re 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 6 (q18 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw⁻ 10 (q13 c4) ∷
   rw⁻ 11 (q18 c4) ∷
   re 6 7 (CS04 ∷ []) ∷
   rw 7 (q139 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   rw 2 (q138 c4) ∷
   rw⁻ 3 (q25 c4) ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 (q11 c4) ∷
   rw⁻ 5 (q26 c4) ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 (q11 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q13 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw 9 (q13 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw 8 (q138 c4) ∷
   rw⁻ 9 (q15 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw⁻ 3 (q140 c4) ∷
   re 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   re 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 8 (q6 c4) ∷
   rw⁻ 9 (q140 c4) ∷
   rw⁻ 10 (q8 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 4 (q141 c4) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 (q2 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 (q2 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 (q2 c4) ∷
   rw⁻ 10 (q141 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   re 4 8 (Toff201 ∷ []) ∷
   re 3 3 (Toff301 ∷ []) ∷
   re 2 3 (Toff401 ∷ []) ∷
   re 1 3 (Toff402 ∷ []) ∷
   re 0 3 (Toff403 ∷ []) ∷ []) Eq.refl

-- nat 1 BOX(4;02): 3 steps
lem-nat-1-BOX⟨4·02⟩ : WsL → ⟪ (Sw12 ∷ Bx4-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-01 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·02⟩ c4 = derive (Sw12 ∷ Bx4-02 ∷ []) (Bx4-01 ∷ Sw12 ∷ [])
  (re 1 1 (CZ02 ∷ []) ∷
   rw 0 (q75 c4) ∷
   re 0 1 (Bx4-01 ∷ []) ∷ []) Eq.refl

private
  q142 : WsL → Eqn
  q142 c4 = eqn (Sw12 ∷ Bx4-02 ∷ []) (Bx4-01 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·02⟩ c4)

-- nat 1 BOX(0;412): 8 steps
lem-nat-1-BOX⟨0·412⟩ : WsL → ⟪ (Sw12 ∷ Bx0-412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-421 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·412⟩ c4 = derive (Sw12 ∷ Bx0-412 ∷ []) (Bx0-421 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) ∷
   rw 0 (q76 c4) ∷
   rw 1 (q77 c4) ∷
   rw 2 (q142 c4) ∷
   rw 3 (q77 c4) ∷
   rw 4 (q76 c4) ∷
   rw 5 (q142 c4) ∷
   re 0 6 (Bx0-421 ∷ []) ∷ []) Eq.refl

private
  q143 : WsL → Eqn
  q143 c4 = eqn (Sw12 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4)
  q144 : WsL → Eqn
  q144 c4 = eqn (Sw12 ∷ Toff403 ∷ []) (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4)
  q145 : WsL → Eqn
  q145 c4 = eqn (Sw12 ∷ Bx0-412 ∷ []) (Bx0-421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·412⟩ c4)

-- nat 1 BOX(4;0312): 8 steps
lem-nat-1-BOX⟨4·0312⟩ : WsL → ⟪ (Sw12 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0321 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·0312⟩ c4 = derive (Sw12 ∷ Bx4-0312 ∷ []) (Bx4-0321 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-412 ∷ Toff403 ∷ CCZ034 ∷ Bx0-412 ∷ []) ∷
   rw 0 (q143 c4) ∷
   rw 1 (q144 c4) ∷
   rw 2 (q145 c4) ∷
   rw 3 (q144 c4) ∷
   rw 4 (q143 c4) ∷
   rw 5 (q145 c4) ∷
   re 0 6 (Bx4-0321 ∷ []) ∷ []) Eq.refl

private
  q146 : WsL → Eqn
  q146 c4 = eqn (Sw12 ∷ CS02 ∷ []) (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4)

-- nat 1 SBOX(4;0;2;1): 3 steps
lem-nat-1-SBOX⟨4·0·2·1⟩ : WsL → ⟪ (Sw12 ∷ Sb4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-1-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨4·0·2·1⟩ c4 = derive (Sw12 ∷ Sb4-0-2-1 ∷ []) (Sb4-0-1-2 ∷ Sw12 ∷ [])
  (re 1 1 (CS02 ∷ []) ∷
   rw 0 (q146 c4) ∷
   re 0 1 (Sb4-0-1-2 ∷ []) ∷ []) Eq.refl

private
  q147 : WsL → Eqn
  q147 c4 = eqn (Sw12 ∷ CS02⁻ ∷ []) (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4)

-- nat 1 SBOXd(4;0;2;1): 3 steps
lem-nat-1-SBOXd⟨4·0·2·1⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-1-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨4·0·2·1⟩ c4 = derive (Sw12 ∷ Sb⁻4-0-2-1 ∷ []) (Sb⁻4-0-1-2 ∷ Sw12 ∷ [])
  (re 1 1 (CS02⁻ ∷ []) ∷
   rw 0 (q147 c4) ∷
   re 0 1 (Sb⁻4-0-1-2 ∷ []) ∷ []) Eq.refl

private
  q148 : WsL → Eqn
  q148 c4 = eqn (Sw12 ∷ Bx4-0312 ∷ []) (Bx4-0321 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·0312⟩ c4)
  q149 : WsL → Eqn
  q149 c4 = eqn (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) (wl0112 c4)
  q150 : WsL → Eqn
  q150 c4 = eqn (Sw12 ∷ Sb4-0-2-1 ∷ []) (Sb4-0-1-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨4·0·2·1⟩ c4)
  q151 : WsL → Eqn
  q151 c4 = eqn (Sw12 ∷ Sb⁻4-0-2-1 ∷ []) (Sb⁻4-0-1-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨4·0·2·1⟩ c4)

-- nat 1 SBOX(4;0;31;2): 7 steps
lem-nat-1-SBOX⟨4·0·31·2⟩ : WsL → ⟪ (Sw12 ∷ Sb4-0-31-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-32-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨4·0·31·2⟩ c4 = derive (Sw12 ∷ Sb4-0-31-2 ∷ []) (Sb4-0-32-1 ∷ Sw12 ∷ [])
  (re 1 1 (Bx4-0312 ∷ Toff213 ∷ Sb4-0-2-1 ∷ Toff213 ∷ Sb⁻4-0-2-1 ∷ []) ∷
   rw 0 (q148 c4) ∷
   rw 1 (q149 c4) ∷
   rw 2 (q150 c4) ∷
   rw 3 (q149 c4) ∷
   rw 4 (q151 c4) ∷
   re 0 5 (Sb4-0-32-1 ∷ []) ∷ []) Eq.refl

private
  q152 : WsL → Eqn
  q152 c4 = eqn (Sw23 ∷ CZ04 ∷ []) (CZ04 ∷ Sw23 ∷ []) (lem-nat-2-CZ04 c4)

-- nat 2 BOX(1;04): 3 steps
lem-nat-2-BOX⟨1·04⟩ : WsL → ⟪ (Sw23 ∷ Bx1-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-04 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·04⟩ c4 = derive (Sw23 ∷ Bx1-04 ∷ []) (Bx1-04 ∷ Sw23 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   rw 0 (q152 c4) ∷
   re 0 1 (Bx1-04 ∷ []) ∷ []) Eq.refl

private
  q153 : WsL → Eqn
  q153 c4 = eqn (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4)
  q154 : WsL → Eqn
  q154 c4 = eqn (Sw23 ∷ Toff013 ∷ []) (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4)
  q155 : WsL → Eqn
  q155 c4 = eqn (Sw23 ∷ Bx1-04 ∷ []) (Bx1-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·04⟩ c4)

-- nat 2 BOX(0;134): 8 steps
lem-nat-2-BOX⟨0·134⟩ : WsL → ⟪ (Sw23 ∷ Bx0-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-124 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·134⟩ c4 = derive (Sw23 ∷ Bx0-134 ∷ []) (Bx0-124 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-04 ∷ Toff013 ∷ CCZ013 ∷ Bx1-04 ∷ []) ∷
   rw 0 (q153 c4) ∷
   rw 1 (q154 c4) ∷
   rw 2 (q155 c4) ∷
   rw 3 (q154 c4) ∷
   rw 4 (q153 c4) ∷
   rw 5 (q155 c4) ∷
   re 0 6 (Bx0-124 ∷ []) ∷ []) Eq.refl

private
  q156 : WsL → Eqn
  q156 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4)
  q157 : WsL → Eqn
  q157 c4 = eqn (Sw23 ∷ Toff102 ∷ []) (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4)
  q158 : WsL → Eqn
  q158 c4 = eqn (Sw23 ∷ Bx0-134 ∷ []) (Bx0-124 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·134⟩ c4)

-- nat 2 BOX(1;0234): 8 steps
lem-nat-2-BOX⟨1·0234⟩ : WsL → ⟪ (Sw23 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0324 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·0234⟩ c4 = derive (Sw23 ∷ Bx1-0234 ∷ []) (Bx1-0324 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-134 ∷ Toff102 ∷ CCZ012 ∷ Bx0-134 ∷ []) ∷
   rw 0 (q156 c4) ∷
   rw 1 (q157 c4) ∷
   rw 2 (q158 c4) ∷
   rw 3 (q157 c4) ∷
   rw 4 (q156 c4) ∷
   rw 5 (q158 c4) ∷
   re 0 6 (Bx1-0324 ∷ []) ∷ []) Eq.refl

-- nat 2 CS04: 7 steps
lem-nat-2-CS04 : WsL → ⟪ (Sw23 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CS04 c4 = derive (Sw23 ∷ CS04 ∷ []) (CS04 ∷ Sw23 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 0 (q18 c4) ∷
   rw⁻ 2 (q13 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw⁻ 5 (q18 c4) ∷
   re 0 7 (CS04 ∷ []) ∷ []) Eq.refl

private
  q159 : WsL → Eqn
  q159 c4 = eqn (Sw23 ∷ CS04 ∷ []) (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 c4)

-- nat 2 SBOX(1;0;4;3): 3 steps
lem-nat-2-SBOX⟨1·0·4·3⟩ : WsL → ⟪ (Sw23 ∷ Sb1-0-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-4-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·0·4·3⟩ c4 = derive (Sw23 ∷ Sb1-0-4-3 ∷ []) (Sb1-0-4-2 ∷ Sw23 ∷ [])
  (re 1 1 (CS04 ∷ []) ∷
   rw 0 (q159 c4) ∷
   re 0 1 (Sb1-0-4-2 ∷ []) ∷ []) Eq.refl

private
  q160 : WsL → Eqn
  q160 c4 = eqn (CS01⁻ ∷ Sw34 ∷ []) (Sw34 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Swap ↑))

-- nat 2 CSd04: 7 steps
lem-nat-2-CSd04 : WsL → ⟪ (Sw23 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CSd04 c4 = derive (Sw23 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Sw23 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 0 (q18 c4) ∷
   rw⁻ 2 (q13 c4) ∷
   rw⁻ 3 (q160 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw⁻ 5 (q18 c4) ∷
   re 0 7 (CS04⁻ ∷ []) ∷ []) Eq.refl

private
  q161 : WsL → Eqn
  q161 c4 = eqn (Sw23 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 c4)

-- nat 2 SBOXd(1;0;4;3): 3 steps
lem-nat-2-SBOXd⟨1·0·4·3⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-0-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-4-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·4·3⟩ c4 = derive (Sw23 ∷ Sb⁻1-0-4-3 ∷ []) (Sb⁻1-0-4-2 ∷ Sw23 ∷ [])
  (re 1 1 (CS04⁻ ∷ []) ∷
   rw 0 (q161 c4) ∷
   re 0 1 (Sb⁻1-0-4-2 ∷ []) ∷ []) Eq.refl

private
  q162 : WsL → Eqn
  q162 c4 = eqn (Sw23 ∷ Bx1-0234 ∷ []) (Bx1-0324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0234⟩ c4)
  q163 : WsL → Eqn
  q163 c4 = eqn (Sw23 ∷ Toff423 ∷ []) (Toff423 ∷ Sw23 ∷ []) (wl0087 c4)
  q164 : WsL → Eqn
  q164 c4 = eqn (Sw23 ∷ Sb1-0-4-3 ∷ []) (Sb1-0-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·4·3⟩ c4)
  q165 : WsL → Eqn
  q165 c4 = eqn (Sw23 ∷ Sb⁻1-0-4-3 ∷ []) (Sb⁻1-0-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·4·3⟩ c4)

-- nat 2 SBOX(1;0;23;4): 7 steps
lem-nat-2-SBOX⟨1·0·23·4⟩ : WsL → ⟪ (Sw23 ∷ Sb1-0-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-32-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·0·23·4⟩ c4 = derive (Sw23 ∷ Sb1-0-23-4 ∷ []) (Sb1-0-32-4 ∷ Sw23 ∷ [])
  (re 1 1 (Bx1-0234 ∷ Toff423 ∷ Sb1-0-4-3 ∷ Toff423 ∷ Sb⁻1-0-4-3 ∷ []) ∷
   rw 0 (q162 c4) ∷
   rw 1 (q163 c4) ∷
   rw 2 (q164 c4) ∷
   rw 3 (q163 c4) ∷
   rw 4 (q165 c4) ∷
   re 0 5 (Sb1-0-32-4 ∷ []) ∷ []) Eq.refl

private
  q166 : WsL → Eqn
  q166 c4 = eqn (Sw23 ∷ CCZ024 ∷ []) (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4)
  q167 : WsL → Eqn
  q167 c4 = eqn (Sw23 ∷ Toff024 ∷ []) (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4)
  q168 : WsL → Eqn
  q168 c4 = eqn (Bx4-01 ∷ Sw23 ∷ []) (Sw23 ∷ Bx4-01 ∷ []) (c₂ (CZ) (Swap))

-- nat 2 BOX(0;421): 8 steps
lem-nat-2-BOX⟨0·421⟩ : WsL → ⟪ (Sw23 ∷ Bx0-421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-431 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·421⟩ c4 = derive (Sw23 ∷ Bx0-421 ∷ []) (Bx0-431 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ []) ∷
   rw 0 (q166 c4) ∷
   rw 1 (q167 c4) ∷
   rw⁻ 2 (q168 c4) ∷
   rw 3 (q167 c4) ∷
   rw 4 (q166 c4) ∷
   rw⁻ 5 (q168 c4) ∷
   re 0 6 (Bx0-431 ∷ []) ∷ []) Eq.refl

private
  q169 : WsL → Eqn
  q169 c4 = eqn (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4)
  q170 : WsL → Eqn
  q170 c4 = eqn (Sw23 ∷ Toff403 ∷ []) (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4)
  q171 : WsL → Eqn
  q171 c4 = eqn (Sw23 ∷ Bx0-421 ∷ []) (Bx0-431 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·421⟩ c4)

-- nat 2 BOX(4;0321): 8 steps
lem-nat-2-BOX⟨4·0321⟩ : WsL → ⟪ (Sw23 ∷ Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·0321⟩ c4 = derive (Sw23 ∷ Bx4-0321 ∷ []) (Bx4-0231 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-421 ∷ Toff403 ∷ CCZ034 ∷ Bx0-421 ∷ []) ∷
   rw 0 (q169 c4) ∷
   rw 1 (q170 c4) ∷
   rw 2 (q171 c4) ∷
   rw 3 (q170 c4) ∷
   rw 4 (q169 c4) ∷
   rw 5 (q171 c4) ∷
   re 0 6 (Bx4-0231 ∷ []) ∷ []) Eq.refl

private
  q172 : WsL → Eqn
  q172 c4 = eqn (Sb4-0-1-2 ∷ Sw23 ∷ []) (Sw23 ∷ Sb4-0-1-2 ∷ []) (c₂ (CS) (Swap))

-- nat 2 SBOX(4;0;1;2): 2 steps
lem-nat-2-SBOX⟨4·0·1·2⟩ : WsL → ⟪ (Sw23 ∷ Sb4-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-1-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨4·0·1·2⟩ c4 = derive (Sw23 ∷ Sb4-0-1-2 ∷ []) (Sb4-0-1-3 ∷ Sw23 ∷ [])
  (rw⁻ 0 (q172 c4) ∷
   re 0 1 (Sb4-0-1-3 ∷ []) ∷ []) Eq.refl

private
  q173 : WsL → Eqn
  q173 c4 = eqn (Sb⁻4-0-1-2 ∷ Sw23 ∷ []) (Sw23 ∷ Sb⁻4-0-1-2 ∷ []) (c₂ (CS • CS • CS) (Swap))

-- nat 2 SBOXd(4;0;1;2): 2 steps
lem-nat-2-SBOXd⟨4·0·1·2⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻4-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-1-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨4·0·1·2⟩ c4 = derive (Sw23 ∷ Sb⁻4-0-1-2 ∷ []) (Sb⁻4-0-1-3 ∷ Sw23 ∷ [])
  (rw⁻ 0 (q173 c4) ∷
   re 0 1 (Sb⁻4-0-1-3 ∷ []) ∷ []) Eq.refl

private
  q174 : WsL → Eqn
  q174 c4 = eqn (Sw23 ∷ Bx4-0321 ∷ []) (Bx4-0231 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0321⟩ c4)
  q175 : WsL → Eqn
  q175 c4 = eqn (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ []) (wl0114 c4)
  q176 : WsL → Eqn
  q176 c4 = eqn (Sw23 ∷ Sb4-0-1-2 ∷ []) (Sb4-0-1-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·0·1·2⟩ c4)
  q177 : WsL → Eqn
  q177 c4 = eqn (Sw23 ∷ Sb⁻4-0-1-2 ∷ []) (Sb⁻4-0-1-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨4·0·1·2⟩ c4)

-- nat 2 SBOX(4;0;32;1): 7 steps
lem-nat-2-SBOX⟨4·0·32·1⟩ : WsL → ⟪ (Sw23 ∷ Sb4-0-32-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-23-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨4·0·32·1⟩ c4 = derive (Sw23 ∷ Sb4-0-32-1 ∷ []) (Sb4-0-23-1 ∷ Sw23 ∷ [])
  (re 1 1 (Bx4-0321 ∷ Toff123 ∷ Sb4-0-1-2 ∷ Toff123 ∷ Sb⁻4-0-1-2 ∷ []) ∷
   rw 0 (q174 c4) ∷
   rw 1 (q175 c4) ∷
   rw 2 (q176 c4) ∷
   rw 3 (q175 c4) ∷
   rw 4 (q177 c4) ∷
   re 0 5 (Sb4-0-23-1 ∷ []) ∷ []) Eq.refl

private
  q178 : WsL → Eqn
  q178 c4 = eqn (Sw01 ∷ CS14 ∷ []) (CS04 ∷ Sw01 ∷ []) (lem-nat-0-CS14 c4)

-- nat 0 SBOX(0;1;4;3): 3 steps
lem-nat-0-SBOX⟨0·1·4·3⟩ : WsL → ⟪ (Sw01 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-4-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·1·4·3⟩ c4 = derive (Sw01 ∷ Sb0-1-4-3 ∷ []) (Sb1-0-4-3 ∷ Sw01 ∷ [])
  (re 1 1 (CS14 ∷ []) ∷
   rw 0 (q178 c4) ∷
   re 0 1 (Sb1-0-4-3 ∷ []) ∷ []) Eq.refl

private
  q179 : WsL → Eqn
  q179 c4 = eqn (CS03⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS13⁻ ∷ []) (wl0022 c4)

-- nat 0 CSd14: 5 steps
lem-nat-0-CSd14 : WsL → ⟪ (Sw01 ∷ CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CSd14 c4 = derive (Sw01 ∷ CS14⁻ ∷ []) (CS04⁻ ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 0 (q44 c4) ∷
   rw⁻ 1 (q179 c4) ∷
   rw 2 (q44 c4) ∷
   re 0 3 (CS04⁻ ∷ []) ∷ []) Eq.refl

private
  q180 : WsL → Eqn
  q180 c4 = eqn (Sw01 ∷ CS14⁻ ∷ []) (CS04⁻ ∷ Sw01 ∷ []) (lem-nat-0-CSd14 c4)

-- nat 0 SBOXd(0;1;4;3): 3 steps
lem-nat-0-SBOXd⟨0·1·4·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-4-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·1·4·3⟩ c4 = derive (Sw01 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻1-0-4-3 ∷ Sw01 ∷ [])
  (re 1 1 (CS14⁻ ∷ []) ∷
   rw 0 (q180 c4) ∷
   re 0 1 (Sb⁻1-0-4-3 ∷ []) ∷ []) Eq.refl

private
  q181 : WsL → Eqn
  q181 c4 = eqn (Sw01 ∷ Bx0-1234 ∷ []) (Bx1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1234⟩ c4)
  q182 : WsL → Eqn
  q182 c4 = eqn (Sw01 ∷ Toff423 ∷ []) (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ))
  q183 : WsL → Eqn
  q183 c4 = eqn (Sw01 ∷ Sb0-1-4-3 ∷ []) (Sb1-0-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·4·3⟩ c4)
  q184 : WsL → Eqn
  q184 c4 = eqn (Sw01 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻1-0-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·4·3⟩ c4)

-- nat 0 SBOX(0;1;23;4): 7 steps
lem-nat-0-SBOX⟨0·1·23·4⟩ : WsL → ⟪ (Sw01 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-23-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·1·23·4⟩ c4 = derive (Sw01 ∷ Sb0-1-23-4 ∷ []) (Sb1-0-23-4 ∷ Sw01 ∷ [])
  (re 1 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   rw 0 (q181 c4) ∷
   rw 1 (q182 c4) ∷
   rw 2 (q183 c4) ∷
   rw 3 (q182 c4) ∷
   rw 4 (q184 c4) ∷
   re 0 5 (Sb1-0-23-4 ∷ []) ∷ []) Eq.refl

private
  q185 : WsL → Eqn
  q185 c4 = eqn (CZ01 ∷ Sw01 ∷ []) (Sw01 ∷ CZ01 ∷ []) (wl0130 c4)

-- nat 0 BOX(4;01): 3 steps
lem-nat-0-BOX⟨4·01⟩ : WsL → ⟪ (Sw01 ∷ Bx4-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-10 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·01⟩ c4 = derive (Sw01 ∷ Bx4-01 ∷ []) (Bx4-10 ∷ Sw01 ∷ [])
  (re 1 1 (CZ01 ∷ []) ∷
   rw⁻ 0 (q185 c4) ∷
   re 0 1 (Bx4-10 ∷ []) ∷ []) Eq.refl

private
  q186 : WsL → Eqn
  q186 c4 = eqn (Sw01 ∷ Bx4-01 ∷ []) (Bx4-10 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·01⟩ c4)

-- nat 0 BOX(0;431): 8 steps
lem-nat-0-BOX⟨0·431⟩ : WsL → ⟪ (Sw01 ∷ Bx0-431 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-430 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·431⟩ c4 = derive (Sw01 ∷ Bx0-431 ∷ []) (Bx1-430 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ []) ∷
   rw 0 (q100 c4) ∷
   rw 1 (q55 c4) ∷
   rw 2 (q186 c4) ∷
   rw 3 (q55 c4) ∷
   rw 4 (q100 c4) ∷
   rw 5 (q186 c4) ∷
   re 0 6 (Bx1-430 ∷ []) ∷ []) Eq.refl

private
  q187 : WsL → Eqn
  q187 c4 = eqn (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4)
  q188 : WsL → Eqn
  q188 c4 = eqn (Sw01 ∷ Toff402 ∷ []) (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4)
  q189 : WsL → Eqn
  q189 c4 = eqn (Sw01 ∷ Bx0-431 ∷ []) (Bx1-430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·431⟩ c4)

-- nat 0 BOX(4;0231): 8 steps
lem-nat-0-BOX⟨4·0231⟩ : WsL → ⟪ (Sw01 ∷ Bx4-0231 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·0231⟩ c4 = derive (Sw01 ∷ Bx4-0231 ∷ []) (Bx4-1230 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-431 ∷ Toff402 ∷ CCZ024 ∷ Bx0-431 ∷ []) ∷
   rw 0 (q187 c4) ∷
   rw 1 (q188 c4) ∷
   rw 2 (q189 c4) ∷
   rw 3 (q188 c4) ∷
   rw 4 (q187 c4) ∷
   rw 5 (q189 c4) ∷
   re 0 6 (Bx4-1230 ∷ []) ∷ []) Eq.refl

private
  q190 : WsL → Eqn
  q190 c4 = eqn (CS01 ∷ Sw01 ∷ []) (Sw01 ∷ CS01 ∷ []) (wl0132 c4)

-- nat 0 SBOX(4;0;1;3): 3 steps
lem-nat-0-SBOX⟨4·0·1·3⟩ : WsL → ⟪ (Sw01 ∷ Sb4-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-0-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨4·0·1·3⟩ c4 = derive (Sw01 ∷ Sb4-0-1-3 ∷ []) (Sb4-1-0-3 ∷ Sw01 ∷ [])
  (re 1 1 (CS01 ∷ []) ∷
   rw⁻ 0 (q190 c4) ∷
   re 0 1 (Sb4-1-0-3 ∷ []) ∷ []) Eq.refl

private
  q191 : WsL → Eqn
  q191 c4 = eqn (CS01⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS01⁻ ∷ []) (wl0133 c4)

-- nat 0 SBOXd(4;0;1;3): 3 steps
lem-nat-0-SBOXd⟨4·0·1·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻4-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-1-0-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨4·0·1·3⟩ c4 = derive (Sw01 ∷ Sb⁻4-0-1-3 ∷ []) (Sb⁻4-1-0-3 ∷ Sw01 ∷ [])
  (re 1 1 (CS01⁻ ∷ []) ∷
   rw⁻ 0 (q191 c4) ∷
   re 0 1 (Sb⁻4-1-0-3 ∷ []) ∷ []) Eq.refl

private
  q192 : WsL → Eqn
  q192 c4 = eqn (Sw01 ∷ Bx4-0231 ∷ []) (Bx4-1230 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·0231⟩ c4)
  q193 : WsL → Eqn
  q193 c4 = eqn (Sw01 ∷ Sb4-0-1-3 ∷ []) (Sb4-1-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨4·0·1·3⟩ c4)
  q194 : WsL → Eqn
  q194 c4 = eqn (Sw01 ∷ Sb⁻4-0-1-3 ∷ []) (Sb⁻4-1-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨4·0·1·3⟩ c4)

-- nat 0 SBOX(4;0;23;1): 7 steps
lem-nat-0-SBOX⟨4·0·23·1⟩ : WsL → ⟪ (Sw01 ∷ Sb4-0-23-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-23-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨4·0·23·1⟩ c4 = derive (Sw01 ∷ Sb4-0-23-1 ∷ []) (Sb4-1-23-0 ∷ Sw01 ∷ [])
  (re 1 1 (Bx4-0231 ∷ Toff123 ∷ Sb4-0-1-3 ∷ Toff123 ∷ Sb⁻4-0-1-3 ∷ []) ∷
   rw 0 (q192 c4) ∷
   rw 1 (q38 c4) ∷
   rw 2 (q193 c4) ∷
   rw 3 (q38 c4) ∷
   rw 4 (q194 c4) ∷
   re 0 5 (Sb4-1-23-0 ∷ []) ∷ []) Eq.refl

-- nat 3 TOFF401: 2 steps
lem-nat-3-TOFF401 : WsL → ⟪ (Sw34 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF401 c4 = derive (Sw34 ∷ Toff401 ∷ []) (Toff301 ∷ Sw34 ∷ [])
  (re 1 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) ∷
   rw 0 (q6 c4) ∷ []) Eq.refl

private
  q195 : WsL → Eqn
  q195 c4 = eqn (CX02 ∷ Sw34 ∷ []) (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))
  q196 : WsL → Eqn
  q196 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl0024 c4)
  q197 : WsL → Eqn
  q197 c4 = eqn (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) (wl0043 c4)

-- nat 3 TOFF024: 80 steps
lem-nat-3-TOFF024 : WsL → ⟪ (Sw34 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF024 c4 = derive (Sw34 ∷ Toff024 ∷ []) (Toff023 ∷ Sw34 ∷ [])
  (re 1 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 (q1 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q3 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q3 c4) ∷
   rw⁻ 10 (q2 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw 11 (q2 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q7 c4) ∷
   rw⁻ 9 (q6 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 9 (q8 c4) ∷
   rw 10 (q6 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   rw⁻ 2 (q10 c4) ∷
   rw⁻ 5 (q11 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q12 c4) ∷
   rw⁻ 7 (q11 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q13 c4) ∷
   rw⁻ 7 (q14 c4) ∷
   rw 8 (q13 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q9 c4) ∷
   rw⁻ 8 (q15 c4) ∷
   rw 9 (q11 c4) ∷
   rw⁻ 0 (q5 c4) ∷
   re 2 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 1 (q6 c4) ∷
   rw⁻ 2 (q195 c4) ∷
   re 4 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q195 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw⁻ 7 (q8 c4) ∷
   rw⁻ 0 (q11 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   rw⁻ 2 (q196 c4) ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 3 (q11 c4) ∷
   rw⁻ 4 (q197 c4) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 (q11 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw⁻ 7 (q9 c4) ∷
   rw⁻ 8 (q15 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 (q2 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   re 0 3 (Toff023 ∷ []) ∷ []) Eq.refl

private
  q198 : WsL → Eqn
  q198 c4 = eqn (Sw34 ∷ CZ03 ∷ []) (CZ04 ∷ Sw34 ∷ []) (lem-nat-3-CZ03 c4)

-- nat 3 BOX(4;03): 3 steps
lem-nat-3-BOX⟨4·03⟩ : WsL → ⟪ (Sw34 ∷ Bx4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-04 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·03⟩ c4 = derive (Sw34 ∷ Bx4-03 ∷ []) (Bx3-04 ∷ Sw34 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw 0 (q198 c4) ∷
   re 0 1 (Bx3-04 ∷ []) ∷ []) Eq.refl

private
  q199 : WsL → Eqn
  q199 c4 = eqn (Sw34 ∷ CCZ024 ∷ []) (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4)
  q200 : WsL → Eqn
  q200 c4 = eqn (Sw34 ∷ Toff024 ∷ []) (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4)
  q201 : WsL → Eqn
  q201 c4 = eqn (Sw34 ∷ Bx4-03 ∷ []) (Bx3-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·03⟩ c4)

-- nat 3 BOX(0;423): 8 steps
lem-nat-3-BOX⟨0·423⟩ : WsL → ⟪ (Sw34 ∷ Bx0-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-324 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·423⟩ c4 = derive (Sw34 ∷ Bx0-423 ∷ []) (Bx0-324 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) ∷
   rw 0 (q199 c4) ∷
   rw 1 (q200 c4) ∷
   rw 2 (q201 c4) ∷
   rw 3 (q200 c4) ∷
   rw 4 (q199 c4) ∷
   rw 5 (q201 c4) ∷
   re 0 6 (Bx0-324 ∷ []) ∷ []) Eq.refl

private
  q202 : WsL → Eqn
  q202 c4 = eqn (Sw34 ∷ CCZ014 ∷ []) (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4)
  q203 : WsL → Eqn
  q203 c4 = eqn (Sw34 ∷ Toff401 ∷ []) (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4)
  q204 : WsL → Eqn
  q204 c4 = eqn (Sw34 ∷ Bx0-423 ∷ []) (Bx0-324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·423⟩ c4)

-- nat 3 BOX(4;0123): 8 steps
lem-nat-3-BOX⟨4·0123⟩ : WsL → ⟪ (Sw34 ∷ Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·0123⟩ c4 = derive (Sw34 ∷ Bx4-0123 ∷ []) (Bx3-0124 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) ∷
   rw 0 (q202 c4) ∷
   rw 1 (q203 c4) ∷
   rw 2 (q204 c4) ∷
   rw 3 (q203 c4) ∷
   rw 4 (q202 c4) ∷
   rw 5 (q204 c4) ∷
   re 0 6 (Bx3-0124 ∷ []) ∷ []) Eq.refl

private
  q205 : WsL → Eqn
  q205 c4 = eqn (Sw34 ∷ CZ04 ∷ []) (CZ03 ∷ Sw34 ∷ []) (lem-nat-3-CZ04 c4)

-- nat 3 BOX(3;04): 3 steps
lem-nat-3-BOX⟨3·04⟩ : WsL → ⟪ (Sw34 ∷ Bx3-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-03 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·04⟩ c4 = derive (Sw34 ∷ Bx3-04 ∷ []) (Bx4-03 ∷ Sw34 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   rw 0 (q205 c4) ∷
   re 0 1 (Bx4-03 ∷ []) ∷ []) Eq.refl

private
  q206 : WsL → Eqn
  q206 c4 = eqn (Sw34 ∷ CCZ023 ∷ []) (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4)
  q207 : WsL → Eqn
  q207 c4 = eqn (Sw34 ∷ Toff023 ∷ []) (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4)
  q208 : WsL → Eqn
  q208 c4 = eqn (Sw34 ∷ Bx3-04 ∷ []) (Bx4-03 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·04⟩ c4)

-- nat 3 BOX(0;324): 8 steps
lem-nat-3-BOX⟨0·324⟩ : WsL → ⟪ (Sw34 ∷ Bx0-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-423 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·324⟩ c4 = derive (Sw34 ∷ Bx0-324 ∷ []) (Bx0-423 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) ∷
   rw 0 (q206 c4) ∷
   rw 1 (q207 c4) ∷
   rw 2 (q208 c4) ∷
   rw 3 (q207 c4) ∷
   rw 4 (q206 c4) ∷
   rw 5 (q208 c4) ∷
   re 0 6 (Bx0-423 ∷ []) ∷ []) Eq.refl

private
  q209 : WsL → Eqn
  q209 c4 = eqn (Sw34 ∷ Toff301 ∷ []) (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4)
  q210 : WsL → Eqn
  q210 c4 = eqn (Sw34 ∷ Bx0-324 ∷ []) (Bx0-423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·324⟩ c4)

-- nat 3 BOX(3;0124): 8 steps
lem-nat-3-BOX⟨3·0124⟩ : WsL → ⟪ (Sw34 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·0124⟩ c4 = derive (Sw34 ∷ Bx3-0124 ∷ []) (Bx4-0123 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) ∷
   rw 0 (q117 c4) ∷
   rw 1 (q209 c4) ∷
   rw 2 (q210 c4) ∷
   rw 3 (q209 c4) ∷
   rw 4 (q117 c4) ∷
   rw 5 (q210 c4) ∷
   re 0 6 (Bx4-0123 ∷ []) ∷ []) Eq.refl
