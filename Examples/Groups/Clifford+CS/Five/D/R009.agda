{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R009 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0003 ; wl0004 ; wl0006 ; wl0007 ; wl0013 ; wl0015 ; wl0018 ; wl0021 ; wl0022 ; wl0033 ; wl0034 ; wl0037 ; wl0038 ; wl0044 ; wl0047 ; wl0049 ; wl0050 ; wl0051 ; wl0052 ; wl0053 ; wl0057 ; wl0058 ; wl0065 ; wl0067 ; wl0068 ; wl0084 ; wl0085 ; wl0087 ; wl0091 ; wl0093 ; wl0096 ; wl0097 ; wl0099 ; wl0100 ; wl0101 ; wl0102 ; wl0103 ; wl0104 ; wl0107 ; wl0108 ; wl0110 ; wl0111 ; wl0112 ; wl0114 ; wl0116 ; wl0121 ; wl0130 ; wl0141 ; wl0142 ; wl0143)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF203 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF034 ; lem-nat-2-TOFF102 ; lem-nat-2-TOFF103 ; lem-nat-2-TOFF301 ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-CCZ034 ; lem-nat-3-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF103 ; lem-nat-2-TOFF201 ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023 ; lem-nat-3-TOFF203)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF412 ; lem-nat-3-TOFF304)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CZ04 ; lem-nat-0-CZ14 ; lem-nat-0-TOFF402 ; lem-nat-1-TOFF013 ; lem-nat-3-TOFF023 ; lem-nat-3-TOFF214 ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-1-BOX⟨2·0134⟩ ; lem-nat-1-CZ04 ; lem-nat-1-TOFF023 ; lem-nat-1-TOFF401 ; lem-nat-2-CCZ014 ; lem-nat-2-CZ02 ; lem-nat-2-CZ03 ; lem-nat-2-CZ04 ; lem-nat-3-BOX⟨2·03⟩ ; lem-nat-3-CZ03 ; lem-nat-3-CZ04)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-CZ01 ; lem-nat-1-CZ02 ; lem-nat-2-BOX⟨0·13⟩ ; lem-nat-2-BOXd⟨0·1324⟩ ; lem-nat-2-BOXd⟨0·14⟩ ; lem-nat-2-CS12 ; lem-nat-2-CS13 ; lem-nat-2-CSd12 ; lem-nat-2-CSd13)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-CS04 ; lem-nat-0-TOFF134 ; lem-nat-1-CS04 ; lem-nat-2-SBOX⟨0·1·4·2⟩ ; lem-nat-2-SBOX⟨0·1·4·3⟩ ; lem-nat-2-SBOXd⟨0·1·4·2⟩ ; lem-nat-2-SBOXd⟨0·1·4·3⟩ ; lem-nat-2-TOFF014 ; lem-nat-2-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨1·0324⟩ ; lem-nat-0-SBOX⟨0·1·4·3⟩ ; lem-nat-0-SBOX⟨4·0·1·3⟩ ; lem-nat-0-SBOXd⟨0·1·4·3⟩ ; lem-nat-0-SBOXd⟨4·0·1·3⟩ ; lem-nat-0-TOFF034 ; lem-nat-1-BOX⟨4·02⟩ ; lem-nat-1-CSd04 ; lem-nat-1-SBOX⟨1·0·4·2⟩ ; lem-nat-1-SBOX⟨4·0·2·1⟩ ; lem-nat-1-SBOXd⟨1·0·4·2⟩ ; lem-nat-1-SBOXd⟨4·0·2·1⟩ ; lem-nat-1-TOFF034 ; lem-nat-1-TOFF403 ; lem-nat-2-SBOX⟨1·0·4·3⟩ ; lem-nat-2-SBOX⟨4·0·1·2⟩ ; lem-nat-2-SBOXd⟨1·0·4·3⟩ ; lem-nat-2-SBOXd⟨4·0·1·2⟩ ; lem-nat-3-SBOX⟨2·0·4·1⟩ ; lem-nat-3-SBOX⟨3·0·2·1⟩ ; lem-nat-3-SBOXd⟨2·0·4·1⟩ ; lem-nat-3-SBOXd⟨3·0·2·1⟩ ; lem-nat-3-TOFF024 ; lem-nat-3-TOFF401)

private
  q1 : WsL → Eqn
  q1 c4 = eqn (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ []) (wl0057 c4)
  q2 : WsL → Eqn
  q2 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 c4)
  q3 : WsL → Eqn
  q3 c4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap))
  q4 : WsL → Eqn
  q4 c4 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (c₁ (iI) (Swap ↑))
  q5 : WsL → Eqn
  q5 c4 = eqn (K4 ∷ Sw34 ∷ []) (Sw34 ∷ K3 ∷ []) (wl0067 c4)
  q6 : WsL → Eqn
  q6 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 c4)
  q7 : WsL → Eqn
  q7 c4 = eqn (CX01 ∷ Sw34 ∷ []) (Sw34 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap ↑))
  q8 : WsL → Eqn
  q8 c4 = eqn (ι ∷ Sw34 ∷ []) (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑))
  q9 : WsL → Eqn
  q9 c4 = eqn (Sw23 ∷ K4 ∷ []) (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K))
  q10 : WsL → Eqn
  q10 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl0021 c4)
  q11 : WsL → Eqn
  q11 c4 = eqn (CS14⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS14⁻ ∷ []) (wl0033 c4)
  q12 : WsL → Eqn
  q12 c4 = eqn (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4)
  q13 : WsL → Eqn
  q13 c4 = eqn (Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap))
  q14 : WsL → Eqn
  q14 c4 = eqn (CS01 ∷ Sw34 ∷ []) (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑))
  q15 : WsL → Eqn
  q15 c4 = eqn (K3 ∷ Sw34 ∷ []) (Sw34 ∷ K4 ∷ []) (wl0068 c4)
  q16 : WsL → Eqn
  q16 c4 = eqn (K2 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ []) (wl0058 c4)

-- nat 2 TOFF401: 68 steps
lem-nat-2-TOFF401 : WsL → ⟪ (Sw23 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF401 c4 = derive (Sw23 ∷ Toff401 ∷ []) (Toff401 ∷ Sw23 ∷ [])
  (re 1 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) ∷
   re 2 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 (q3 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q3 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw 10 (q2 c4) ∷
   rw⁻ 1 (q5 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (CS14 ∷ []) ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CS14⁻ ∷ []) ∷
   rw⁻ 5 (q7 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw 9 (q6 c4) ∷
   rw 0 (q9 c4) ∷
   rw⁻ 1 (q10 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 3 (q11 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q12 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw⁻ 10 (q12 c4) ∷
   re 5 7 (CS04 ∷ []) ∷
   rw 6 (q9 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   rw⁻ 1 (q15 c4) ∷
   re 3 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 2 (q6 c4) ∷
   rw⁻ 3 (q7 c4) ∷
   re 5 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   rw⁻ 2 (q16 c4) ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 (q2 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 (q2 c4) ∷
   rw⁻ 8 (q16 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   re 2 8 (Toff201 ∷ []) ∷
   re 1 3 (Toff301 ∷ []) ∷
   re 0 3 (Toff401 ∷ []) ∷ []) Eq.refl

private
  q17 : WsL → Eqn
  q17 c4 = eqn (Sw23 ∷ CZ02 ∷ []) (CZ03 ∷ Sw23 ∷ []) (lem-nat-2-CZ02 c4)

-- nat 2 BOX(4;02): 3 steps
lem-nat-2-BOX⟨4·02⟩ : WsL → ⟪ (Sw23 ∷ Bx4-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-03 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·02⟩ c4 = derive (Sw23 ∷ Bx4-02 ∷ []) (Bx4-03 ∷ Sw23 ∷ [])
  (re 1 1 (CZ02 ∷ []) ∷
   rw 0 (q17 c4) ∷
   re 0 1 (Bx4-03 ∷ []) ∷ []) Eq.refl

private
  q18 : WsL → Eqn
  q18 c4 = eqn (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4)
  q19 : WsL → Eqn
  q19 c4 = eqn (Sw23 ∷ Toff034 ∷ []) (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4)
  q20 : WsL → Eqn
  q20 c4 = eqn (Sw23 ∷ Bx4-02 ∷ []) (Bx4-03 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·02⟩ c4)

-- nat 2 BOX(0;432): 8 steps
lem-nat-2-BOX⟨0·432⟩ : WsL → ⟪ (Sw23 ∷ Bx0-432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-423 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·432⟩ c4 = derive (Sw23 ∷ Bx0-432 ∷ []) (Bx0-423 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-02 ∷ Toff034 ∷ CCZ034 ∷ Bx4-02 ∷ []) ∷
   rw 0 (q18 c4) ∷
   rw 1 (q19 c4) ∷
   rw 2 (q20 c4) ∷
   rw 3 (q19 c4) ∷
   rw 4 (q18 c4) ∷
   rw 5 (q20 c4) ∷
   re 0 6 (Bx0-423 ∷ []) ∷ []) Eq.refl

private
  q21 : WsL → Eqn
  q21 c4 = eqn (Sw23 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4)
  q22 : WsL → Eqn
  q22 c4 = eqn (Sw23 ∷ Toff401 ∷ []) (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4)
  q23 : WsL → Eqn
  q23 c4 = eqn (Sw23 ∷ Bx0-432 ∷ []) (Bx0-423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·432⟩ c4)

-- nat 2 BOX(4;0132): 8 steps
lem-nat-2-BOX⟨4·0132⟩ : WsL → ⟪ (Sw23 ∷ Bx4-0132 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·0132⟩ c4 = derive (Sw23 ∷ Bx4-0132 ∷ []) (Bx4-0123 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-432 ∷ Toff401 ∷ CCZ014 ∷ Bx0-432 ∷ []) ∷
   rw 0 (q21 c4) ∷
   rw 1 (q22 c4) ∷
   rw 2 (q23 c4) ∷
   rw 3 (q22 c4) ∷
   rw 4 (q21 c4) ∷
   rw 5 (q23 c4) ∷
   re 0 6 (Bx4-0123 ∷ []) ∷ []) Eq.refl

private
  q24 : WsL → Eqn
  q24 c4 = eqn (Sw23 ∷ CZ03 ∷ []) (CZ02 ∷ Sw23 ∷ []) (lem-nat-2-CZ03 c4)

-- nat 2 BOX(4;03): 3 steps
lem-nat-2-BOX⟨4·03⟩ : WsL → ⟪ (Sw23 ∷ Bx4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-02 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·03⟩ c4 = derive (Sw23 ∷ Bx4-03 ∷ []) (Bx4-02 ∷ Sw23 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw 0 (q24 c4) ∷
   re 0 1 (Bx4-02 ∷ []) ∷ []) Eq.refl

private
  q25 : WsL → Eqn
  q25 c4 = eqn (Sw23 ∷ CCZ024 ∷ []) (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4)
  q26 : WsL → Eqn
  q26 c4 = eqn (Sw23 ∷ Toff024 ∷ []) (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4)
  q27 : WsL → Eqn
  q27 c4 = eqn (Sw23 ∷ Bx4-03 ∷ []) (Bx4-02 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·03⟩ c4)

-- nat 2 BOX(0;423): 8 steps
lem-nat-2-BOX⟨0·423⟩ : WsL → ⟪ (Sw23 ∷ Bx0-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-432 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·423⟩ c4 = derive (Sw23 ∷ Bx0-423 ∷ []) (Bx0-432 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) ∷
   rw 0 (q25 c4) ∷
   rw 1 (q26 c4) ∷
   rw 2 (q27 c4) ∷
   rw 3 (q26 c4) ∷
   rw 4 (q25 c4) ∷
   rw 5 (q27 c4) ∷
   re 0 6 (Bx0-432 ∷ []) ∷ []) Eq.refl

private
  q28 : WsL → Eqn
  q28 c4 = eqn (Sw23 ∷ Bx0-423 ∷ []) (Bx0-432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·423⟩ c4)

-- nat 2 BOX(4;0123): 8 steps
lem-nat-2-BOX⟨4·0123⟩ : WsL → ⟪ (Sw23 ∷ Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0132 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·0123⟩ c4 = derive (Sw23 ∷ Bx4-0123 ∷ []) (Bx4-0132 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) ∷
   rw 0 (q21 c4) ∷
   rw 1 (q22 c4) ∷
   rw 2 (q28 c4) ∷
   rw 3 (q22 c4) ∷
   rw 4 (q21 c4) ∷
   rw 5 (q28 c4) ∷
   re 0 6 (Bx4-0132 ∷ []) ∷ []) Eq.refl

private
  q29 : WsL → Eqn
  q29 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 c4)

-- nat 1 TOFF402: 2 steps
lem-nat-1-TOFF402 : WsL → ⟪ (Sw12 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF402 c4 = derive (Sw12 ∷ Toff402 ∷ []) (Toff401 ∷ Sw12 ∷ [])
  (re 1 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) ∷
   rw 0 (q29 c4) ∷ []) Eq.refl

private
  q30 : WsL → Eqn
  q30 c4 = eqn (Sw12 ∷ CZ01 ∷ []) (CZ02 ∷ Sw12 ∷ []) (lem-nat-1-CZ01 c4)

-- nat 1 BOX(4;01): 3 steps
lem-nat-1-BOX⟨4·01⟩ : WsL → ⟪ (Sw12 ∷ Bx4-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-02 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·01⟩ c4 = derive (Sw12 ∷ Bx4-01 ∷ []) (Bx4-02 ∷ Sw12 ∷ [])
  (re 1 1 (CZ01 ∷ []) ∷
   rw 0 (q30 c4) ∷
   re 0 1 (Bx4-02 ∷ []) ∷ []) Eq.refl

private
  q31 : WsL → Eqn
  q31 c4 = eqn (Sw12 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4)
  q32 : WsL → Eqn
  q32 c4 = eqn (Sw12 ∷ Toff034 ∷ []) (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4)
  q33 : WsL → Eqn
  q33 c4 = eqn (Sw12 ∷ Bx4-01 ∷ []) (Bx4-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·01⟩ c4)

-- nat 1 BOX(0;431): 8 steps
lem-nat-1-BOX⟨0·431⟩ : WsL → ⟪ (Sw12 ∷ Bx0-431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-432 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·431⟩ c4 = derive (Sw12 ∷ Bx0-431 ∷ []) (Bx0-432 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ []) ∷
   rw 0 (q31 c4) ∷
   rw 1 (q32 c4) ∷
   rw 2 (q33 c4) ∷
   rw 3 (q32 c4) ∷
   rw 4 (q31 c4) ∷
   rw 5 (q33 c4) ∷
   re 0 6 (Bx0-432 ∷ []) ∷ []) Eq.refl

private
  q34 : WsL → Eqn
  q34 c4 = eqn (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4)
  q35 : WsL → Eqn
  q35 c4 = eqn (Sw12 ∷ Toff402 ∷ []) (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4)
  q36 : WsL → Eqn
  q36 c4 = eqn (Sw12 ∷ Bx0-431 ∷ []) (Bx0-432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·431⟩ c4)

-- nat 1 BOX(4;0231): 8 steps
lem-nat-1-BOX⟨4·0231⟩ : WsL → ⟪ (Sw12 ∷ Bx4-0231 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0132 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·0231⟩ c4 = derive (Sw12 ∷ Bx4-0231 ∷ []) (Bx4-0132 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-431 ∷ Toff402 ∷ CCZ024 ∷ Bx0-431 ∷ []) ∷
   rw 0 (q34 c4) ∷
   rw 1 (q35 c4) ∷
   rw 2 (q36 c4) ∷
   rw 3 (q35 c4) ∷
   rw 4 (q34 c4) ∷
   rw 5 (q36 c4) ∷
   re 0 6 (Bx4-0132 ∷ []) ∷ []) Eq.refl

private
  q37 : WsL → Eqn
  q37 c4 = eqn (Sw12 ∷ Bx4-02 ∷ []) (Bx4-01 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·02⟩ c4)

-- nat 1 BOX(0;432): 8 steps
lem-nat-1-BOX⟨0·432⟩ : WsL → ⟪ (Sw12 ∷ Bx0-432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-431 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·432⟩ c4 = derive (Sw12 ∷ Bx0-432 ∷ []) (Bx0-431 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-02 ∷ Toff034 ∷ CCZ034 ∷ Bx4-02 ∷ []) ∷
   rw 0 (q31 c4) ∷
   rw 1 (q32 c4) ∷
   rw 2 (q37 c4) ∷
   rw 3 (q32 c4) ∷
   rw 4 (q31 c4) ∷
   rw 5 (q37 c4) ∷
   re 0 6 (Bx0-431 ∷ []) ∷ []) Eq.refl

private
  q38 : WsL → Eqn
  q38 c4 = eqn (Sw12 ∷ CCZ014 ∷ []) (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4)
  q39 : WsL → Eqn
  q39 c4 = eqn (Sw12 ∷ Toff401 ∷ []) (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4)
  q40 : WsL → Eqn
  q40 c4 = eqn (Sw12 ∷ Bx0-432 ∷ []) (Bx0-431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·432⟩ c4)

-- nat 1 BOX(4;0132): 8 steps
lem-nat-1-BOX⟨4·0132⟩ : WsL → ⟪ (Sw12 ∷ Bx4-0132 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·0132⟩ c4 = derive (Sw12 ∷ Bx4-0132 ∷ []) (Bx4-0231 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-432 ∷ Toff401 ∷ CCZ014 ∷ Bx0-432 ∷ []) ∷
   rw 0 (q38 c4) ∷
   rw 1 (q39 c4) ∷
   rw 2 (q40 c4) ∷
   rw 3 (q39 c4) ∷
   rw 4 (q38 c4) ∷
   rw 5 (q40 c4) ∷
   re 0 6 (Bx4-0231 ∷ []) ∷ []) Eq.refl

private
  q41 : WsL → Eqn
  q41 c4 = eqn (CZ01 ∷ Sw01 ∷ []) (Sw01 ∷ CZ01 ∷ []) (wl0130 c4)

-- nat 0 BOX(4;10): 3 steps
lem-nat-0-BOX⟨4·10⟩ : WsL → ⟪ (Sw01 ∷ Bx4-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-01 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·10⟩ c4 = derive (Sw01 ∷ Bx4-10 ∷ []) (Bx4-01 ∷ Sw01 ∷ [])
  (re 1 1 (CZ01 ∷ []) ∷
   rw⁻ 0 (q41 c4) ∷
   re 0 1 (Bx4-01 ∷ []) ∷ []) Eq.refl

private
  q42 : WsL → Eqn
  q42 c4 = eqn (Sw01 ∷ CCZ134 ∷ []) (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4)
  q43 : WsL → Eqn
  q43 c4 = eqn (Sw01 ∷ Toff134 ∷ []) (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4)
  q44 : WsL → Eqn
  q44 c4 = eqn (Sw01 ∷ Bx4-10 ∷ []) (Bx4-01 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·10⟩ c4)

-- nat 0 BOX(1;430): 8 steps
lem-nat-0-BOX⟨1·430⟩ : WsL → ⟪ (Sw01 ∷ Bx1-430 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-431 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·430⟩ c4 = derive (Sw01 ∷ Bx1-430 ∷ []) (Bx0-431 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) ∷
   rw 0 (q42 c4) ∷
   rw 1 (q43 c4) ∷
   rw 2 (q44 c4) ∷
   rw 3 (q43 c4) ∷
   rw 4 (q42 c4) ∷
   rw 5 (q44 c4) ∷
   re 0 6 (Bx0-431 ∷ []) ∷ []) Eq.refl

private
  q45 : WsL → Eqn
  q45 c4 = eqn (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4)
  q46 : WsL → Eqn
  q46 c4 = eqn (Sw01 ∷ Toff412 ∷ []) (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4)
  q47 : WsL → Eqn
  q47 c4 = eqn (Sw01 ∷ Bx1-430 ∷ []) (Bx0-431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·430⟩ c4)

-- nat 0 BOX(4;1230): 8 steps
lem-nat-0-BOX⟨4·1230⟩ : WsL → ⟪ (Sw01 ∷ Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·1230⟩ c4 = derive (Sw01 ∷ Bx4-1230 ∷ []) (Bx4-0231 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ []) ∷
   rw 0 (q45 c4) ∷
   rw 1 (q46 c4) ∷
   rw 2 (q47 c4) ∷
   rw 3 (q46 c4) ∷
   rw 4 (q45 c4) ∷
   rw 5 (q47 c4) ∷
   re 0 6 (Bx4-0231 ∷ []) ∷ []) Eq.refl

private
  q48 : WsL → Eqn
  q48 c4 = eqn (Sw34 ∷ CCZ024 ∷ []) (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4)
  q49 : WsL → Eqn
  q49 c4 = eqn (Sw34 ∷ Toff024 ∷ []) (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4)
  q50 : WsL → Eqn
  q50 c4 = eqn (Sw34 ∷ Bx2-03 ∷ []) (Bx2-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·03⟩ c4)

-- nat 3 BOX(0;243): 8 steps
lem-nat-3-BOX⟨0·243⟩ : WsL → ⟪ (Sw34 ∷ Bx0-243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-234 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·243⟩ c4 = derive (Sw34 ∷ Bx0-243 ∷ []) (Bx0-234 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) ∷
   rw 0 (q48 c4) ∷
   rw 1 (q49 c4) ∷
   rw 2 (q50 c4) ∷
   rw 3 (q49 c4) ∷
   rw 4 (q48 c4) ∷
   rw 5 (q50 c4) ∷
   re 0 6 (Bx0-234 ∷ []) ∷ []) Eq.refl

private
  q51 : WsL → Eqn
  q51 c4 = eqn (CCZ012 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (Swap))
  q52 : WsL → Eqn
  q52 c4 = eqn (Toff201 ∷ Sw34 ∷ []) (Sw34 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (Swap))
  q53 : WsL → Eqn
  q53 c4 = eqn (Sw34 ∷ Bx0-243 ∷ []) (Bx0-234 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·243⟩ c4)

-- nat 3 BOX(2;0143): 8 steps
lem-nat-3-BOX⟨2·0143⟩ : WsL → ⟪ (Sw34 ∷ Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·0143⟩ c4 = derive (Sw34 ∷ Bx2-0143 ∷ []) (Bx2-0134 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ []) ∷
   rw⁻ 0 (q51 c4) ∷
   rw⁻ 1 (q52 c4) ∷
   rw 2 (q53 c4) ∷
   rw⁻ 3 (q52 c4) ∷
   rw⁻ 4 (q51 c4) ∷
   rw 5 (q53 c4) ∷
   re 0 6 (Bx2-0134 ∷ []) ∷ []) Eq.refl

-- nat 3 CS03: 2 steps
lem-nat-3-CS03 : WsL → ⟪ (Sw34 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CS03 c4 = derive (Sw34 ∷ CS03 ∷ []) (CS04 ∷ Sw34 ∷ [])
  (rw⁻ 2 (q6 c4) ∷
   re 0 3 (CS04 ∷ []) ∷ []) Eq.refl

private
  q54 : WsL → Eqn
  q54 c4 = eqn (Sw34 ∷ CS03 ∷ []) (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 c4)

-- nat 3 SBOX(2;0;3;4): 3 steps
lem-nat-3-SBOX⟨2·0·3·4⟩ : WsL → ⟪ (Sw34 ∷ Sb2-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-4-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·0·3·4⟩ c4 = derive (Sw34 ∷ Sb2-0-3-4 ∷ []) (Sb2-0-4-3 ∷ Sw34 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   rw 0 (q54 c4) ∷
   re 0 1 (Sb2-0-4-3 ∷ []) ∷ []) Eq.refl

-- nat 3 CSd03: 2 steps
lem-nat-3-CSd03 : WsL → ⟪ (Sw34 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS04⁻ ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CSd03 c4 = derive (Sw34 ∷ CS03⁻ ∷ []) (CS04⁻ ∷ Sw34 ∷ [])
  (rw⁻ 2 (q6 c4) ∷
   re 0 3 (CS04⁻ ∷ []) ∷ []) Eq.refl

private
  q55 : WsL → Eqn
  q55 c4 = eqn (Sw34 ∷ CS03⁻ ∷ []) (CS04⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd03 c4)

-- nat 3 SBOXd(2;0;3;4): 3 steps
lem-nat-3-SBOXd⟨2·0·3·4⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻2-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-4-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·0·3·4⟩ c4 = derive (Sw34 ∷ Sb⁻2-0-3-4 ∷ []) (Sb⁻2-0-4-3 ∷ Sw34 ∷ [])
  (re 1 1 (CS03⁻ ∷ []) ∷
   rw 0 (q55 c4) ∷
   re 0 1 (Sb⁻2-0-4-3 ∷ []) ∷ []) Eq.refl

private
  q56 : WsL → Eqn
  q56 c4 = eqn (Sw34 ∷ Bx2-0143 ∷ []) (Bx2-0134 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·0143⟩ c4)
  q57 : WsL → Eqn
  q57 c4 = eqn (Sw34 ∷ Toff314 ∷ []) (Toff413 ∷ Sw34 ∷ []) (wl0142 c4)
  q58 : WsL → Eqn
  q58 c4 = eqn (Sw34 ∷ Sb2-0-3-4 ∷ []) (Sb2-0-4-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·3·4⟩ c4)
  q59 : WsL → Eqn
  q59 c4 = eqn (Sw34 ∷ Sb⁻2-0-3-4 ∷ []) (Sb⁻2-0-4-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·3·4⟩ c4)

-- nat 3 SBOX(2;0;14;3): 7 steps
lem-nat-3-SBOX⟨2·0·14·3⟩ : WsL → ⟪ (Sw34 ∷ Sb2-0-14-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-13-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·0·14·3⟩ c4 = derive (Sw34 ∷ Sb2-0-14-3 ∷ []) (Sb2-0-13-4 ∷ Sw34 ∷ [])
  (re 1 1 (Bx2-0143 ∷ Toff314 ∷ Sb2-0-3-4 ∷ Toff314 ∷ Sb⁻2-0-3-4 ∷ []) ∷
   rw 0 (q56 c4) ∷
   rw 1 (q57 c4) ∷
   rw 2 (q58 c4) ∷
   rw 3 (q57 c4) ∷
   rw 4 (q59 c4) ∷
   re 0 5 (Sb2-0-13-4 ∷ []) ∷ []) Eq.refl

private
  q60 : WsL → Eqn
  q60 c4 = eqn (Sw12 ∷ CS04 ∷ []) (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 c4)

-- nat 1 SBOX(2;0;4;3): 3 steps
lem-nat-1-SBOX⟨2·0·4·3⟩ : WsL → ⟪ (Sw12 ∷ Sb2-0-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-4-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·0·4·3⟩ c4 = derive (Sw12 ∷ Sb2-0-4-3 ∷ []) (Sb1-0-4-3 ∷ Sw12 ∷ [])
  (re 1 1 (CS04 ∷ []) ∷
   rw 0 (q60 c4) ∷
   re 0 1 (Sb1-0-4-3 ∷ []) ∷ []) Eq.refl

private
  q61 : WsL → Eqn
  q61 c4 = eqn (Sw12 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd04 c4)

-- nat 1 SBOXd(2;0;4;3): 3 steps
lem-nat-1-SBOXd⟨2·0·4·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-0-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-4-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·0·4·3⟩ c4 = derive (Sw12 ∷ Sb⁻2-0-4-3 ∷ []) (Sb⁻1-0-4-3 ∷ Sw12 ∷ [])
  (re 1 1 (CS04⁻ ∷ []) ∷
   rw 0 (q61 c4) ∷
   re 0 1 (Sb⁻1-0-4-3 ∷ []) ∷ []) Eq.refl

private
  q62 : WsL → Eqn
  q62 c4 = eqn (Sw12 ∷ Bx2-0134 ∷ []) (Bx1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0134⟩ c4)
  q63 : WsL → Eqn
  q63 c4 = eqn (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) (wl0085 c4)
  q64 : WsL → Eqn
  q64 c4 = eqn (Sw12 ∷ Sb2-0-4-3 ∷ []) (Sb1-0-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·4·3⟩ c4)
  q65 : WsL → Eqn
  q65 c4 = eqn (Sw12 ∷ Sb⁻2-0-4-3 ∷ []) (Sb⁻1-0-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·4·3⟩ c4)

-- nat 1 SBOX(2;0;13;4): 7 steps
lem-nat-1-SBOX⟨2·0·13·4⟩ : WsL → ⟪ (Sw12 ∷ Sb2-0-13-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-23-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·0·13·4⟩ c4 = derive (Sw12 ∷ Sb2-0-13-4 ∷ []) (Sb1-0-23-4 ∷ Sw12 ∷ [])
  (re 1 1 (Bx2-0134 ∷ Toff413 ∷ Sb2-0-4-3 ∷ Toff413 ∷ Sb⁻2-0-4-3 ∷ []) ∷
   rw 0 (q62 c4) ∷
   rw 1 (q63 c4) ∷
   rw 2 (q64 c4) ∷
   rw 3 (q63 c4) ∷
   rw 4 (q65 c4) ∷
   re 0 5 (Sb1-0-23-4 ∷ []) ∷ []) Eq.refl

private
  q66 : WsL → Eqn
  q66 c4 = eqn (Sw01 ∷ CS04 ∷ []) (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 c4)

-- nat 0 SBOX(1;0;4;2): 3 steps
lem-nat-0-SBOX⟨1·0·4·2⟩ : WsL → ⟪ (Sw01 ∷ Sb1-0-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-4-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·0·4·2⟩ c4 = derive (Sw01 ∷ Sb1-0-4-2 ∷ []) (Sb0-1-4-2 ∷ Sw01 ∷ [])
  (re 1 1 (CS04 ∷ []) ∷
   rw 0 (q66 c4) ∷
   re 0 1 (Sb0-1-4-2 ∷ []) ∷ []) Eq.refl

private
  q67 : WsL → Eqn
  q67 c4 = eqn (Sw01 ∷ Sw34 ∷ []) (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑))
  q68 : WsL → Eqn
  q68 c4 = eqn (CS13⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS03⁻ ∷ []) (wl0121 c4)

-- nat 0 CSd04: 5 steps
lem-nat-0-CSd04 : WsL → ⟪ (Sw01 ∷ CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS14⁻ ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CSd04 c4 = derive (Sw01 ∷ CS04⁻ ∷ []) (CS14⁻ ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw 0 (q67 c4) ∷
   rw⁻ 1 (q68 c4) ∷
   rw 2 (q67 c4) ∷
   re 0 3 (CS14⁻ ∷ []) ∷ []) Eq.refl

private
  q69 : WsL → Eqn
  q69 c4 = eqn (Sw01 ∷ CS04⁻ ∷ []) (CS14⁻ ∷ Sw01 ∷ []) (lem-nat-0-CSd04 c4)

-- nat 0 SBOXd(1;0;4;2): 3 steps
lem-nat-0-SBOXd⟨1·0·4·2⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻1-0-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-4-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·0·4·2⟩ c4 = derive (Sw01 ∷ Sb⁻1-0-4-2 ∷ []) (Sb⁻0-1-4-2 ∷ Sw01 ∷ [])
  (re 1 1 (CS04⁻ ∷ []) ∷
   rw 0 (q69 c4) ∷
   re 0 1 (Sb⁻0-1-4-2 ∷ []) ∷ []) Eq.refl

private
  q70 : WsL → Eqn
  q70 c4 = eqn (Sw01 ∷ Bx1-0324 ∷ []) (Bx0-1324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0324⟩ c4)
  q71 : WsL → Eqn
  q71 c4 = eqn (Sw01 ∷ Toff423 ∷ []) (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ))
  q72 : WsL → Eqn
  q72 c4 = eqn (Sw01 ∷ Sb1-0-4-2 ∷ []) (Sb0-1-4-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·4·2⟩ c4)
  q73 : WsL → Eqn
  q73 c4 = eqn (Sw01 ∷ Sb⁻1-0-4-2 ∷ []) (Sb⁻0-1-4-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·4·2⟩ c4)

-- nat 0 SBOX(1;0;32;4): 7 steps
lem-nat-0-SBOX⟨1·0·32·4⟩ : WsL → ⟪ (Sw01 ∷ Sb1-0-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-32-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·0·32·4⟩ c4 = derive (Sw01 ∷ Sb1-0-32-4 ∷ []) (Sb0-1-32-4 ∷ Sw01 ∷ [])
  (re 1 1 (Bx1-0324 ∷ Toff423 ∷ Sb1-0-4-2 ∷ Toff423 ∷ Sb⁻1-0-4-2 ∷ []) ∷
   rw 0 (q70 c4) ∷
   rw 1 (q71 c4) ∷
   rw 2 (q72 c4) ∷
   rw 3 (q71 c4) ∷
   rw 4 (q73 c4) ∷
   re 0 5 (Sb0-1-32-4 ∷ []) ∷ []) Eq.refl

private
  q74 : WsL → Eqn
  q74 c4 = eqn (Sw34 ∷ CZ04 ∷ []) (CZ03 ∷ Sw34 ∷ []) (lem-nat-3-CZ04 c4)

-- nat 3 BOXd(2;04): 3 steps
lem-nat-3-BOXd⟨2·04⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻2-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-03 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨2·04⟩ c4 = derive (Sw34 ∷ Bx⁻2-04 ∷ []) (Bx⁻2-03 ∷ Sw34 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   rw 0 (q74 c4) ∷
   re 0 1 (Bx⁻2-03 ∷ []) ∷ []) Eq.refl

private
  q75 : WsL → Eqn
  q75 c4 = eqn (Sw34 ∷ Bx⁻2-04 ∷ []) (Bx⁻2-03 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨2·04⟩ c4)
  q76 : WsL → Eqn
  q76 c4 = eqn (Toff012 ∷ Sw34 ∷ []) (Sw34 ∷ Toff012 ∷ []) (c₃ (Toff) (Swap))

-- nat 3 BOXd(0;214): 8 steps
lem-nat-3-BOXd⟨0·214⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻0-214 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-213 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·214⟩ c4 = derive (Sw34 ∷ Bx⁻0-214 ∷ []) (Bx⁻0-213 ∷ Sw34 ∷ [])
  (re 1 1 (Bx⁻2-04 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-04 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   rw 0 (q75 c4) ∷
   rw⁻ 1 (q51 c4) ∷
   rw⁻ 2 (q76 c4) ∷
   rw 3 (q75 c4) ∷
   rw⁻ 4 (q76 c4) ∷
   rw⁻ 5 (q51 c4) ∷
   re 0 6 (Bx⁻0-213 ∷ []) ∷ []) Eq.refl

private
  q77 : WsL → Eqn
  q77 c4 = eqn (Sw34 ∷ Bx⁻0-214 ∷ []) (Bx⁻0-213 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·214⟩ c4)
  q78 : WsL → Eqn
  q78 c4 = eqn (Sw34 ∷ CCZ023 ∷ []) (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4)
  q79 : WsL → Eqn
  q79 c4 = eqn (Sw34 ∷ Toff203 ∷ []) (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4)

-- nat 3 BOXd(2;0314): 8 steps
lem-nat-3-BOXd⟨2·0314⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0413 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨2·0314⟩ c4 = derive (Sw34 ∷ Bx⁻2-0314 ∷ []) (Bx⁻2-0413 ∷ Sw34 ∷ [])
  (re 1 1 (Bx⁻0-214 ∷ CCZ023 ∷ Toff203 ∷ Bx⁻0-214 ∷ Toff203 ∷ CCZ023 ∷ []) ∷
   rw 0 (q77 c4) ∷
   rw 1 (q78 c4) ∷
   rw 2 (q79 c4) ∷
   rw 3 (q77 c4) ∷
   rw 4 (q79 c4) ∷
   rw 5 (q78 c4) ∷
   re 0 6 (Bx⁻2-0413 ∷ []) ∷ []) Eq.refl

private
  q80 : WsL → Eqn
  q80 c4 = eqn (Sw34 ∷ Sb2-0-4-1 ∷ []) (Sb2-0-3-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·4·1⟩ c4)
  q81 : WsL → Eqn
  q81 c4 = eqn (Sw34 ∷ Toff413 ∷ []) (Toff314 ∷ Sw34 ∷ []) (wl0141 c4)
  q82 : WsL → Eqn
  q82 c4 = eqn (Sw34 ∷ Sb⁻2-0-4-1 ∷ []) (Sb⁻2-0-3-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·4·1⟩ c4)
  q83 : WsL → Eqn
  q83 c4 = eqn (Sw34 ∷ Bx⁻2-0314 ∷ []) (Bx⁻2-0413 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨2·0314⟩ c4)

-- nat 3 SBOXd(2;0;31;4): 7 steps
lem-nat-3-SBOXd⟨2·0·31·4⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻2-0-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-41-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·0·31·4⟩ c4 = derive (Sw34 ∷ Sb⁻2-0-31-4 ∷ []) (Sb⁻2-0-41-3 ∷ Sw34 ∷ [])
  (re 1 1 (Sb2-0-4-1 ∷ Toff413 ∷ Sb⁻2-0-4-1 ∷ Toff413 ∷ Bx⁻2-0314 ∷ []) ∷
   rw 0 (q80 c4) ∷
   rw 1 (q81 c4) ∷
   rw 2 (q82 c4) ∷
   rw 3 (q81 c4) ∷
   rw 4 (q83 c4) ∷
   re 0 5 (Sb⁻2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q84 : WsL → Eqn
  q84 c4 = eqn (Sw34 ∷ CZ03 ∷ []) (CZ04 ∷ Sw34 ∷ []) (lem-nat-3-CZ03 c4)

-- nat 3 BOXd(2;03): 3 steps
lem-nat-3-BOXd⟨2·03⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻2-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-04 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨2·03⟩ c4 = derive (Sw34 ∷ Bx⁻2-03 ∷ []) (Bx⁻2-04 ∷ Sw34 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw 0 (q84 c4) ∷
   re 0 1 (Bx⁻2-04 ∷ []) ∷ []) Eq.refl

private
  q85 : WsL → Eqn
  q85 c4 = eqn (Sw34 ∷ Bx⁻2-03 ∷ []) (Bx⁻2-04 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨2·03⟩ c4)

-- nat 3 BOXd(0;243): 8 steps
lem-nat-3-BOXd⟨0·243⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻0-243 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-234 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·243⟩ c4 = derive (Sw34 ∷ Bx⁻0-243 ∷ []) (Bx⁻0-234 ∷ Sw34 ∷ [])
  (re 1 1 (Bx⁻2-03 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻2-03 ∷ Toff024 ∷ CCZ024 ∷ []) ∷
   rw 0 (q85 c4) ∷
   rw 1 (q48 c4) ∷
   rw 2 (q49 c4) ∷
   rw 3 (q85 c4) ∷
   rw 4 (q49 c4) ∷
   rw 5 (q48 c4) ∷
   re 0 6 (Bx⁻0-234 ∷ []) ∷ []) Eq.refl

private
  q86 : WsL → Eqn
  q86 c4 = eqn (Sw34 ∷ Bx⁻0-243 ∷ []) (Bx⁻0-234 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·243⟩ c4)

-- nat 3 BOXd(2;0143): 8 steps
lem-nat-3-BOXd⟨2·0143⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0134 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨2·0143⟩ c4 = derive (Sw34 ∷ Bx⁻2-0143 ∷ []) (Bx⁻2-0134 ∷ Sw34 ∷ [])
  (re 1 1 (Bx⁻0-243 ∷ CCZ012 ∷ Toff201 ∷ Bx⁻0-243 ∷ Toff201 ∷ CCZ012 ∷ []) ∷
   rw 0 (q86 c4) ∷
   rw⁻ 1 (q51 c4) ∷
   rw⁻ 2 (q52 c4) ∷
   rw 3 (q86 c4) ∷
   rw⁻ 4 (q52 c4) ∷
   rw⁻ 5 (q51 c4) ∷
   re 0 6 (Bx⁻2-0134 ∷ []) ∷ []) Eq.refl

private
  q87 : WsL → Eqn
  q87 c4 = eqn (Sw34 ∷ Bx⁻2-0143 ∷ []) (Bx⁻2-0134 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨2·0143⟩ c4)

-- nat 3 SBOXd(2;0;14;3): 7 steps
lem-nat-3-SBOXd⟨2·0·14·3⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻2-0-14-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-13-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·0·14·3⟩ c4 = derive (Sw34 ∷ Sb⁻2-0-14-3 ∷ []) (Sb⁻2-0-13-4 ∷ Sw34 ∷ [])
  (re 1 1 (Sb2-0-3-4 ∷ Toff314 ∷ Sb⁻2-0-3-4 ∷ Toff314 ∷ Bx⁻2-0143 ∷ []) ∷
   rw 0 (q58 c4) ∷
   rw 1 (q57 c4) ∷
   rw 2 (q59 c4) ∷
   rw 3 (q57 c4) ∷
   rw 4 (q87 c4) ∷
   re 0 5 (Sb⁻2-0-13-4 ∷ []) ∷ []) Eq.refl

private
  q88 : WsL → Eqn
  q88 c4 = eqn (Sw12 ∷ CZ04 ∷ []) (CZ04 ∷ Sw12 ∷ []) (lem-nat-1-CZ04 c4)

-- nat 1 BOXd(1;04): 3 steps
lem-nat-1-BOXd⟨1·04⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻1-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-04 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·04⟩ c4 = derive (Sw12 ∷ Bx⁻1-04 ∷ []) (Bx⁻2-04 ∷ Sw12 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   rw 0 (q88 c4) ∷
   re 0 1 (Bx⁻2-04 ∷ []) ∷ []) Eq.refl

private
  q89 : WsL → Eqn
  q89 c4 = eqn (Sw12 ∷ Bx⁻1-04 ∷ []) (Bx⁻2-04 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·04⟩ c4)
  q90 : WsL → Eqn
  q90 c4 = eqn (CCZ012 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ012 ∷ []) (wl0037 c4)
  q91 : WsL → Eqn
  q91 c4 = eqn (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) (wl0038 c4)

-- nat 1 BOXd(0;124): 8 steps
lem-nat-1-BOXd⟨0·124⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻0-124 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-214 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·124⟩ c4 = derive (Sw12 ∷ Bx⁻0-124 ∷ []) (Bx⁻0-214 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻1-04 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-04 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   rw 0 (q89 c4) ∷
   rw⁻ 1 (q90 c4) ∷
   rw 2 (q91 c4) ∷
   rw 3 (q89 c4) ∷
   rw 4 (q91 c4) ∷
   rw⁻ 5 (q90 c4) ∷
   re 0 6 (Bx⁻0-214 ∷ []) ∷ []) Eq.refl

private
  q92 : WsL → Eqn
  q92 c4 = eqn (Sw12 ∷ Bx⁻0-124 ∷ []) (Bx⁻0-214 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·124⟩ c4)
  q93 : WsL → Eqn
  q93 c4 = eqn (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4)
  q94 : WsL → Eqn
  q94 c4 = eqn (Sw12 ∷ Toff103 ∷ []) (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4)

-- nat 1 BOXd(1;0324): 8 steps
lem-nat-1-BOXd⟨1·0324⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0314 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·0324⟩ c4 = derive (Sw12 ∷ Bx⁻1-0324 ∷ []) (Bx⁻2-0314 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻0-124 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-124 ∷ Toff103 ∷ CCZ013 ∷ []) ∷
   rw 0 (q92 c4) ∷
   rw 1 (q93 c4) ∷
   rw 2 (q94 c4) ∷
   rw 3 (q92 c4) ∷
   rw 4 (q94 c4) ∷
   rw 5 (q93 c4) ∷
   re 0 6 (Bx⁻2-0314 ∷ []) ∷ []) Eq.refl

private
  q95 : WsL → Eqn
  q95 c4 = eqn (Sw12 ∷ Sb1-0-4-2 ∷ []) (Sb2-0-4-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·4·2⟩ c4)
  q96 : WsL → Eqn
  q96 c4 = eqn (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) (wl0091 c4)
  q97 : WsL → Eqn
  q97 c4 = eqn (Sw12 ∷ Sb⁻1-0-4-2 ∷ []) (Sb⁻2-0-4-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·4·2⟩ c4)
  q98 : WsL → Eqn
  q98 c4 = eqn (Sw12 ∷ Bx⁻1-0324 ∷ []) (Bx⁻2-0314 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·0324⟩ c4)

-- nat 1 SBOXd(1;0;32;4): 7 steps
lem-nat-1-SBOXd⟨1·0·32·4⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-0-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-31-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·0·32·4⟩ c4 = derive (Sw12 ∷ Sb⁻1-0-32-4 ∷ []) (Sb⁻2-0-31-4 ∷ Sw12 ∷ [])
  (re 1 1 (Sb1-0-4-2 ∷ Toff423 ∷ Sb⁻1-0-4-2 ∷ Toff423 ∷ Bx⁻1-0324 ∷ []) ∷
   rw 0 (q95 c4) ∷
   rw 1 (q96 c4) ∷
   rw 2 (q97 c4) ∷
   rw 3 (q96 c4) ∷
   rw 4 (q98 c4) ∷
   re 0 5 (Sb⁻2-0-31-4 ∷ []) ∷ []) Eq.refl

-- nat 1 BOXd(2;04): 3 steps
lem-nat-1-BOXd⟨2·04⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻2-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-04 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·04⟩ c4 = derive (Sw12 ∷ Bx⁻2-04 ∷ []) (Bx⁻1-04 ∷ Sw12 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   rw 0 (q88 c4) ∷
   re 0 1 (Bx⁻1-04 ∷ []) ∷ []) Eq.refl

private
  q99 : WsL → Eqn
  q99 c4 = eqn (Sw12 ∷ Bx⁻2-04 ∷ []) (Bx⁻1-04 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·04⟩ c4)
  q100 : WsL → Eqn
  q100 c4 = eqn (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4)
  q101 : WsL → Eqn
  q101 c4 = eqn (Sw12 ∷ Toff023 ∷ []) (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4)

-- nat 1 BOXd(0;234): 8 steps
lem-nat-1-BOXd⟨0·234⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻0-234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-134 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·234⟩ c4 = derive (Sw12 ∷ Bx⁻0-234 ∷ []) (Bx⁻0-134 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻2-04 ∷ CCZ023 ∷ Toff023 ∷ Bx⁻2-04 ∷ Toff023 ∷ CCZ023 ∷ []) ∷
   rw 0 (q99 c4) ∷
   rw 1 (q100 c4) ∷
   rw 2 (q101 c4) ∷
   rw 3 (q99 c4) ∷
   rw 4 (q101 c4) ∷
   rw 5 (q100 c4) ∷
   re 0 6 (Bx⁻0-134 ∷ []) ∷ []) Eq.refl

private
  q102 : WsL → Eqn
  q102 c4 = eqn (Sw12 ∷ Bx⁻0-234 ∷ []) (Bx⁻0-134 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·234⟩ c4)
  q103 : WsL → Eqn
  q103 c4 = eqn (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) (wl0044 c4)

-- nat 1 BOXd(2;0134): 8 steps
lem-nat-1-BOXd⟨2·0134⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0234 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·0134⟩ c4 = derive (Sw12 ∷ Bx⁻2-0134 ∷ []) (Bx⁻1-0234 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻0-234 ∷ CCZ012 ∷ Toff201 ∷ Bx⁻0-234 ∷ Toff201 ∷ CCZ012 ∷ []) ∷
   rw 0 (q102 c4) ∷
   rw⁻ 1 (q90 c4) ∷
   rw 2 (q103 c4) ∷
   rw 3 (q102 c4) ∷
   rw 4 (q103 c4) ∷
   rw⁻ 5 (q90 c4) ∷
   re 0 6 (Bx⁻1-0234 ∷ []) ∷ []) Eq.refl

private
  q104 : WsL → Eqn
  q104 c4 = eqn (Sw12 ∷ Bx⁻2-0134 ∷ []) (Bx⁻1-0234 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·0134⟩ c4)

-- nat 1 SBOXd(2;0;13;4): 7 steps
lem-nat-1-SBOXd⟨2·0·13·4⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-0-13-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-23-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·0·13·4⟩ c4 = derive (Sw12 ∷ Sb⁻2-0-13-4 ∷ []) (Sb⁻1-0-23-4 ∷ Sw12 ∷ [])
  (re 1 1 (Sb2-0-4-3 ∷ Toff413 ∷ Sb⁻2-0-4-3 ∷ Toff413 ∷ Bx⁻2-0134 ∷ []) ∷
   rw 0 (q64 c4) ∷
   rw 1 (q63 c4) ∷
   rw 2 (q65 c4) ∷
   rw 3 (q63 c4) ∷
   rw 4 (q104 c4) ∷
   re 0 5 (Sb⁻1-0-23-4 ∷ []) ∷ []) Eq.refl

private
  q105 : WsL → Eqn
  q105 c4 = eqn (Sw23 ∷ CZ04 ∷ []) (CZ04 ∷ Sw23 ∷ []) (lem-nat-2-CZ04 c4)

-- nat 2 BOXd(1;04): 3 steps
lem-nat-2-BOXd⟨1·04⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-04 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·04⟩ c4 = derive (Sw23 ∷ Bx⁻1-04 ∷ []) (Bx⁻1-04 ∷ Sw23 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   rw 0 (q105 c4) ∷
   re 0 1 (Bx⁻1-04 ∷ []) ∷ []) Eq.refl

private
  q106 : WsL → Eqn
  q106 c4 = eqn (Sw23 ∷ Bx⁻1-04 ∷ []) (Bx⁻1-04 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·04⟩ c4)
  q107 : WsL → Eqn
  q107 c4 = eqn (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4)
  q108 : WsL → Eqn
  q108 c4 = eqn (Sw23 ∷ Toff013 ∷ []) (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4)

-- nat 2 BOXd(0;134): 8 steps
lem-nat-2-BOXd⟨0·134⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-124 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·134⟩ c4 = derive (Sw23 ∷ Bx⁻0-134 ∷ []) (Bx⁻0-124 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻1-04 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-04 ∷ Toff013 ∷ CCZ013 ∷ []) ∷
   rw 0 (q106 c4) ∷
   rw 1 (q107 c4) ∷
   rw 2 (q108 c4) ∷
   rw 3 (q106 c4) ∷
   rw 4 (q108 c4) ∷
   rw 5 (q107 c4) ∷
   re 0 6 (Bx⁻0-124 ∷ []) ∷ []) Eq.refl

private
  q109 : WsL → Eqn
  q109 c4 = eqn (Sw23 ∷ Bx⁻0-134 ∷ []) (Bx⁻0-124 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·134⟩ c4)
  q110 : WsL → Eqn
  q110 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4)
  q111 : WsL → Eqn
  q111 c4 = eqn (Sw23 ∷ Toff102 ∷ []) (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4)

-- nat 2 BOXd(1;0234): 8 steps
lem-nat-2-BOXd⟨1·0234⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0324 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·0234⟩ c4 = derive (Sw23 ∷ Bx⁻1-0234 ∷ []) (Bx⁻1-0324 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻0-134 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-134 ∷ Toff102 ∷ CCZ012 ∷ []) ∷
   rw 0 (q109 c4) ∷
   rw 1 (q110 c4) ∷
   rw 2 (q111 c4) ∷
   rw 3 (q109 c4) ∷
   rw 4 (q111 c4) ∷
   rw 5 (q110 c4) ∷
   re 0 6 (Bx⁻1-0324 ∷ []) ∷ []) Eq.refl

private
  q112 : WsL → Eqn
  q112 c4 = eqn (Sw23 ∷ Sb1-0-4-3 ∷ []) (Sb1-0-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·4·3⟩ c4)
  q113 : WsL → Eqn
  q113 c4 = eqn (Sw23 ∷ Toff423 ∷ []) (Toff423 ∷ Sw23 ∷ []) (wl0087 c4)
  q114 : WsL → Eqn
  q114 c4 = eqn (Sw23 ∷ Sb⁻1-0-4-3 ∷ []) (Sb⁻1-0-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·4·3⟩ c4)
  q115 : WsL → Eqn
  q115 c4 = eqn (Sw23 ∷ Bx⁻1-0234 ∷ []) (Bx⁻1-0324 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·0234⟩ c4)

-- nat 2 SBOXd(1;0;23;4): 7 steps
lem-nat-2-SBOXd⟨1·0·23·4⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-0-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-32-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·23·4⟩ c4 = derive (Sw23 ∷ Sb⁻1-0-23-4 ∷ []) (Sb⁻1-0-32-4 ∷ Sw23 ∷ [])
  (re 1 1 (Sb1-0-4-3 ∷ Toff423 ∷ Sb⁻1-0-4-3 ∷ Toff423 ∷ Bx⁻1-0234 ∷ []) ∷
   rw 0 (q112 c4) ∷
   rw 1 (q113 c4) ∷
   rw 2 (q114 c4) ∷
   rw 3 (q113 c4) ∷
   rw 4 (q115 c4) ∷
   re 0 5 (Sb⁻1-0-32-4 ∷ []) ∷ []) Eq.refl

private
  q116 : WsL → Eqn
  q116 c4 = eqn (Sw01 ∷ CZ14 ∷ []) (CZ04 ∷ Sw01 ∷ []) (lem-nat-0-CZ14 c4)

-- nat 0 BOXd(0;14): 3 steps
lem-nat-0-BOXd⟨0·14⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻0-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-04 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·14⟩ c4 = derive (Sw01 ∷ Bx⁻0-14 ∷ []) (Bx⁻1-04 ∷ Sw01 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   rw 0 (q116 c4) ∷
   re 0 1 (Bx⁻1-04 ∷ []) ∷ []) Eq.refl

private
  q117 : WsL → Eqn
  q117 c4 = eqn (Sw01 ∷ Bx⁻0-14 ∷ []) (Bx⁻1-04 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·14⟩ c4)
  q118 : WsL → Eqn
  q118 c4 = eqn (CCZ013 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ013 ∷ []) (wl0100 c4)
  q119 : WsL → Eqn
  q119 c4 = eqn (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) (wl0102 c4)

-- nat 0 BOXd(1;034): 8 steps
lem-nat-0-BOXd⟨1·034⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻1-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-134 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·034⟩ c4 = derive (Sw01 ∷ Bx⁻1-034 ∷ []) (Bx⁻0-134 ∷ Sw01 ∷ [])
  (re 1 1 (Bx⁻0-14 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-14 ∷ Toff103 ∷ CCZ013 ∷ []) ∷
   rw 0 (q117 c4) ∷
   rw⁻ 1 (q118 c4) ∷
   rw 2 (q119 c4) ∷
   rw 3 (q117 c4) ∷
   rw 4 (q119 c4) ∷
   rw⁻ 5 (q118 c4) ∷
   re 0 6 (Bx⁻0-134 ∷ []) ∷ []) Eq.refl

private
  q120 : WsL → Eqn
  q120 c4 = eqn (Sw01 ∷ Bx⁻1-034 ∷ []) (Bx⁻0-134 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·034⟩ c4)
  q121 : WsL → Eqn
  q121 c4 = eqn (CCZ012 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ012 ∷ []) (wl0096 c4)
  q122 : WsL → Eqn
  q122 c4 = eqn (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) (wl0099 c4)

-- nat 0 BOXd(0;1234): 8 steps
lem-nat-0-BOXd⟨0·1234⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0234 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·1234⟩ c4 = derive (Sw01 ∷ Bx⁻0-1234 ∷ []) (Bx⁻1-0234 ∷ Sw01 ∷ [])
  (re 1 1 (Bx⁻1-034 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-034 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   rw 0 (q120 c4) ∷
   rw⁻ 1 (q121 c4) ∷
   rw 2 (q122 c4) ∷
   rw 3 (q120 c4) ∷
   rw 4 (q122 c4) ∷
   rw⁻ 5 (q121 c4) ∷
   re 0 6 (Bx⁻1-0234 ∷ []) ∷ []) Eq.refl

private
  q123 : WsL → Eqn
  q123 c4 = eqn (Sw01 ∷ Sb0-1-4-3 ∷ []) (Sb1-0-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·4·3⟩ c4)
  q124 : WsL → Eqn
  q124 c4 = eqn (Sw01 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻1-0-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·4·3⟩ c4)
  q125 : WsL → Eqn
  q125 c4 = eqn (Sw01 ∷ Bx⁻0-1234 ∷ []) (Bx⁻1-0234 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·1234⟩ c4)

-- nat 0 SBOXd(0;1;23;4): 7 steps
lem-nat-0-SBOXd⟨0·1·23·4⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-23-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·1·23·4⟩ c4 = derive (Sw01 ∷ Sb⁻0-1-23-4 ∷ []) (Sb⁻1-0-23-4 ∷ Sw01 ∷ [])
  (re 1 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) ∷
   rw 0 (q123 c4) ∷
   rw 1 (q71 c4) ∷
   rw 2 (q124 c4) ∷
   rw 3 (q71 c4) ∷
   rw 4 (q125 c4) ∷
   re 0 5 (Sb⁻1-0-23-4 ∷ []) ∷ []) Eq.refl

private
  q126 : WsL → Eqn
  q126 c4 = eqn (Sw01 ∷ CZ04 ∷ []) (CZ14 ∷ Sw01 ∷ []) (lem-nat-0-CZ04 c4)

-- nat 0 BOXd(1;04): 3 steps
lem-nat-0-BOXd⟨1·04⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻1-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-14 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·04⟩ c4 = derive (Sw01 ∷ Bx⁻1-04 ∷ []) (Bx⁻0-14 ∷ Sw01 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   rw 0 (q126 c4) ∷
   re 0 1 (Bx⁻0-14 ∷ []) ∷ []) Eq.refl

private
  q127 : WsL → Eqn
  q127 c4 = eqn (Sw01 ∷ Bx⁻1-04 ∷ []) (Bx⁻0-14 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·04⟩ c4)

-- nat 0 BOXd(0;124): 8 steps
lem-nat-0-BOXd⟨0·124⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻0-124 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-024 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·124⟩ c4 = derive (Sw01 ∷ Bx⁻0-124 ∷ []) (Bx⁻1-024 ∷ Sw01 ∷ [])
  (re 1 1 (Bx⁻1-04 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-04 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   rw 0 (q127 c4) ∷
   rw⁻ 1 (q121 c4) ∷
   rw 2 (q122 c4) ∷
   rw 3 (q127 c4) ∷
   rw 4 (q122 c4) ∷
   rw⁻ 5 (q121 c4) ∷
   re 0 6 (Bx⁻1-024 ∷ []) ∷ []) Eq.refl

private
  q128 : WsL → Eqn
  q128 c4 = eqn (Sw01 ∷ Bx⁻0-124 ∷ []) (Bx⁻1-024 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·124⟩ c4)

-- nat 0 BOXd(1;0324): 8 steps
lem-nat-0-BOXd⟨1·0324⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻1-0324 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1324 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·0324⟩ c4 = derive (Sw01 ∷ Bx⁻1-0324 ∷ []) (Bx⁻0-1324 ∷ Sw01 ∷ [])
  (re 1 1 (Bx⁻0-124 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-124 ∷ Toff103 ∷ CCZ013 ∷ []) ∷
   rw 0 (q128 c4) ∷
   rw⁻ 1 (q118 c4) ∷
   rw 2 (q119 c4) ∷
   rw 3 (q128 c4) ∷
   rw 4 (q119 c4) ∷
   rw⁻ 5 (q118 c4) ∷
   re 0 6 (Bx⁻0-1324 ∷ []) ∷ []) Eq.refl

private
  q129 : WsL → Eqn
  q129 c4 = eqn (Sw01 ∷ Bx⁻1-0324 ∷ []) (Bx⁻0-1324 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·0324⟩ c4)

-- nat 0 SBOXd(1;0;32;4): 7 steps
lem-nat-0-SBOXd⟨1·0·32·4⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻1-0-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-32-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·0·32·4⟩ c4 = derive (Sw01 ∷ Sb⁻1-0-32-4 ∷ []) (Sb⁻0-1-32-4 ∷ Sw01 ∷ [])
  (re 1 1 (Sb1-0-4-2 ∷ Toff423 ∷ Sb⁻1-0-4-2 ∷ Toff423 ∷ Bx⁻1-0324 ∷ []) ∷
   rw 0 (q72 c4) ∷
   rw 1 (q71 c4) ∷
   rw 2 (q73 c4) ∷
   rw 3 (q71 c4) ∷
   rw 4 (q129 c4) ∷
   re 0 5 (Sb⁻0-1-32-4 ∷ []) ∷ []) Eq.refl

private
  q130 : WsL → Eqn
  q130 c4 = eqn (Sw23 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ c4)
  q131 : WsL → Eqn
  q131 c4 = eqn (Sw23 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ c4)
  q132 : WsL → Eqn
  q132 c4 = eqn (Sw23 ∷ Bx⁻0-1324 ∷ []) (Bx⁻0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·1324⟩ c4)

-- nat 2 SBOXd(0;1;32;4): 7 steps
lem-nat-2-SBOXd⟨0·1·32·4⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-23-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·1·32·4⟩ c4 = derive (Sw23 ∷ Sb⁻0-1-32-4 ∷ []) (Sb⁻0-1-23-4 ∷ Sw23 ∷ [])
  (re 1 1 (Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ []) ∷
   rw 0 (q130 c4) ∷
   rw 1 (q113 c4) ∷
   rw 2 (q131 c4) ∷
   rw 3 (q113 c4) ∷
   rw 4 (q132 c4) ∷
   re 0 5 (Sb⁻0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q133 : WsL → Eqn
  q133 c4 = eqn (Sw23 ∷ Bx⁻0-14 ∷ []) (Bx⁻0-14 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·14⟩ c4)
  q134 : WsL → Eqn
  q134 c4 = eqn (Sw23 ∷ Toff103 ∷ []) (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4)

-- nat 2 BOXd(1;034): 8 steps
lem-nat-2-BOXd⟨1·034⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-024 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·034⟩ c4 = derive (Sw23 ∷ Bx⁻1-034 ∷ []) (Bx⁻1-024 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻0-14 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-14 ∷ Toff103 ∷ CCZ013 ∷ []) ∷
   rw 0 (q133 c4) ∷
   rw 1 (q107 c4) ∷
   rw 2 (q134 c4) ∷
   rw 3 (q133 c4) ∷
   rw 4 (q134 c4) ∷
   rw 5 (q107 c4) ∷
   re 0 6 (Bx⁻1-024 ∷ []) ∷ []) Eq.refl

private
  q135 : WsL → Eqn
  q135 c4 = eqn (Sw23 ∷ Bx⁻1-034 ∷ []) (Bx⁻1-024 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·034⟩ c4)
  q136 : WsL → Eqn
  q136 c4 = eqn (Sw23 ∷ Toff012 ∷ []) (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4)

-- nat 2 BOXd(0;1234): 8 steps
lem-nat-2-BOXd⟨0·1234⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1324 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·1234⟩ c4 = derive (Sw23 ∷ Bx⁻0-1234 ∷ []) (Bx⁻0-1324 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻1-034 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-034 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   rw 0 (q135 c4) ∷
   rw 1 (q110 c4) ∷
   rw 2 (q136 c4) ∷
   rw 3 (q135 c4) ∷
   rw 4 (q136 c4) ∷
   rw 5 (q110 c4) ∷
   re 0 6 (Bx⁻0-1324 ∷ []) ∷ []) Eq.refl

private
  q137 : WsL → Eqn
  q137 c4 = eqn (Sw23 ∷ Sb0-1-4-3 ∷ []) (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ c4)
  q138 : WsL → Eqn
  q138 c4 = eqn (Sw23 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ c4)
  q139 : WsL → Eqn
  q139 c4 = eqn (Sw23 ∷ Bx⁻0-1234 ∷ []) (Bx⁻0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·1234⟩ c4)

-- nat 2 SBOXd(0;1;23;4): 7 steps
lem-nat-2-SBOXd⟨0·1·23·4⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-32-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·1·23·4⟩ c4 = derive (Sw23 ∷ Sb⁻0-1-23-4 ∷ []) (Sb⁻0-1-32-4 ∷ Sw23 ∷ [])
  (re 1 1 (Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ Toff423 ∷ Bx⁻0-1234 ∷ []) ∷
   rw 0 (q137 c4) ∷
   rw 1 (q113 c4) ∷
   rw 2 (q138 c4) ∷
   rw 3 (q113 c4) ∷
   rw 4 (q139 c4) ∷
   re 0 5 (Sb⁻0-1-32-4 ∷ []) ∷ []) Eq.refl

private
  q140 : WsL → Eqn
  q140 c4 = eqn (Bx⁻3-02 ∷ Sw34 ∷ []) (Sw34 ∷ Bx⁻3-02 ∷ []) (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))

-- nat 3 BOXd(3;02): 2 steps
lem-nat-3-BOXd⟨3·02⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻3-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-02 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨3·02⟩ c4 = derive (Sw34 ∷ Bx⁻3-02 ∷ []) (Bx⁻4-02 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q140 c4) ∷
   re 0 1 (Bx⁻4-02 ∷ []) ∷ []) Eq.refl

private
  q141 : WsL → Eqn
  q141 c4 = eqn (Sw34 ∷ Bx⁻3-02 ∷ []) (Bx⁻4-02 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨3·02⟩ c4)
  q142 : WsL → Eqn
  q142 c4 = eqn (Sw34 ∷ CCZ013 ∷ []) (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4)
  q143 : WsL → Eqn
  q143 c4 = eqn (Sw34 ∷ Toff013 ∷ []) (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4)

-- nat 3 BOXd(0;312): 8 steps
lem-nat-3-BOXd⟨0·312⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻0-312 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-412 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·312⟩ c4 = derive (Sw34 ∷ Bx⁻0-312 ∷ []) (Bx⁻0-412 ∷ Sw34 ∷ [])
  (re 1 1 (Bx⁻3-02 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻3-02 ∷ Toff013 ∷ CCZ013 ∷ []) ∷
   rw 0 (q141 c4) ∷
   rw 1 (q142 c4) ∷
   rw 2 (q143 c4) ∷
   rw 3 (q141 c4) ∷
   rw 4 (q143 c4) ∷
   rw 5 (q142 c4) ∷
   re 0 6 (Bx⁻0-412 ∷ []) ∷ []) Eq.refl

private
  q144 : WsL → Eqn
  q144 c4 = eqn (Sw34 ∷ Bx⁻0-312 ∷ []) (Bx⁻0-412 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·312⟩ c4)
  q145 : WsL → Eqn
  q145 c4 = eqn (Sw34 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4)
  q146 : WsL → Eqn
  q146 c4 = eqn (Sw34 ∷ Toff304 ∷ []) (Toff403 ∷ Sw34 ∷ []) (lem-nat-3-TOFF304 c4)

-- nat 3 BOXd(3;0412): 8 steps
lem-nat-3-BOXd⟨3·0412⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0312 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨3·0412⟩ c4 = derive (Sw34 ∷ Bx⁻3-0412 ∷ []) (Bx⁻4-0312 ∷ Sw34 ∷ [])
  (re 1 1 (Bx⁻0-312 ∷ CCZ034 ∷ Toff304 ∷ Bx⁻0-312 ∷ Toff304 ∷ CCZ034 ∷ []) ∷
   rw 0 (q144 c4) ∷
   rw 1 (q145 c4) ∷
   rw 2 (q146 c4) ∷
   rw 3 (q144 c4) ∷
   rw 4 (q146 c4) ∷
   rw 5 (q145 c4) ∷
   re 0 6 (Bx⁻4-0312 ∷ []) ∷ []) Eq.refl

private
  q147 : WsL → Eqn
  q147 c4 = eqn (Sw34 ∷ Sb3-0-2-1 ∷ []) (Sb4-0-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨3·0·2·1⟩ c4)
  q148 : WsL → Eqn
  q148 c4 = eqn (Sw34 ∷ Toff214 ∷ []) (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 c4)
  q149 : WsL → Eqn
  q149 c4 = eqn (Sw34 ∷ Sb⁻3-0-2-1 ∷ []) (Sb⁻4-0-2-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨3·0·2·1⟩ c4)
  q150 : WsL → Eqn
  q150 c4 = eqn (Sw34 ∷ Bx⁻3-0412 ∷ []) (Bx⁻4-0312 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨3·0412⟩ c4)

-- nat 3 SBOXd(3;0;41;2): 7 steps
lem-nat-3-SBOXd⟨3·0·41·2⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-31-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨3·0·41·2⟩ c4 = derive (Sw34 ∷ Sb⁻3-0-41-2 ∷ []) (Sb⁻4-0-31-2 ∷ Sw34 ∷ [])
  (re 1 1 (Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ Toff214 ∷ Bx⁻3-0412 ∷ []) ∷
   rw 0 (q147 c4) ∷
   rw 1 (q148 c4) ∷
   rw 2 (q149 c4) ∷
   rw 3 (q148 c4) ∷
   rw 4 (q150 c4) ∷
   re 0 5 (Sb⁻4-0-31-2 ∷ []) ∷ []) Eq.refl

private
  q151 : WsL → Eqn
  q151 c4 = eqn (Sw12 ∷ CZ02 ∷ []) (CZ01 ∷ Sw12 ∷ []) (lem-nat-1-CZ02 c4)

-- nat 1 BOXd(4;02): 3 steps
lem-nat-1-BOXd⟨4·02⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻4-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-01 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·02⟩ c4 = derive (Sw12 ∷ Bx⁻4-02 ∷ []) (Bx⁻4-01 ∷ Sw12 ∷ [])
  (re 1 1 (CZ02 ∷ []) ∷
   rw 0 (q151 c4) ∷
   re 0 1 (Bx⁻4-01 ∷ []) ∷ []) Eq.refl

private
  q152 : WsL → Eqn
  q152 c4 = eqn (Sw12 ∷ Bx⁻4-02 ∷ []) (Bx⁻4-01 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·02⟩ c4)
  q153 : WsL → Eqn
  q153 c4 = eqn (Sw12 ∷ Toff014 ∷ []) (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4)

-- nat 1 BOXd(0;412): 8 steps
lem-nat-1-BOXd⟨0·412⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻0-412 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-421 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·412⟩ c4 = derive (Sw12 ∷ Bx⁻0-412 ∷ []) (Bx⁻0-421 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻4-02 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻4-02 ∷ Toff014 ∷ CCZ014 ∷ []) ∷
   rw 0 (q152 c4) ∷
   rw 1 (q38 c4) ∷
   rw 2 (q153 c4) ∷
   rw 3 (q152 c4) ∷
   rw 4 (q153 c4) ∷
   rw 5 (q38 c4) ∷
   re 0 6 (Bx⁻0-421 ∷ []) ∷ []) Eq.refl

private
  q154 : WsL → Eqn
  q154 c4 = eqn (Sw12 ∷ Bx⁻0-412 ∷ []) (Bx⁻0-421 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·412⟩ c4)
  q155 : WsL → Eqn
  q155 c4 = eqn (Sw12 ∷ Toff403 ∷ []) (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4)

-- nat 1 BOXd(4;0312): 8 steps
lem-nat-1-BOXd⟨4·0312⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0321 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·0312⟩ c4 = derive (Sw12 ∷ Bx⁻4-0312 ∷ []) (Bx⁻4-0321 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻0-412 ∷ CCZ034 ∷ Toff403 ∷ Bx⁻0-412 ∷ Toff403 ∷ CCZ034 ∷ []) ∷
   rw 0 (q154 c4) ∷
   rw 1 (q31 c4) ∷
   rw 2 (q155 c4) ∷
   rw 3 (q154 c4) ∷
   rw 4 (q155 c4) ∷
   rw 5 (q31 c4) ∷
   re 0 6 (Bx⁻4-0321 ∷ []) ∷ []) Eq.refl

private
  q156 : WsL → Eqn
  q156 c4 = eqn (Sw12 ∷ Sb4-0-2-1 ∷ []) (Sb4-0-1-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨4·0·2·1⟩ c4)
  q157 : WsL → Eqn
  q157 c4 = eqn (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) (wl0112 c4)
  q158 : WsL → Eqn
  q158 c4 = eqn (Sw12 ∷ Sb⁻4-0-2-1 ∷ []) (Sb⁻4-0-1-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨4·0·2·1⟩ c4)
  q159 : WsL → Eqn
  q159 c4 = eqn (Sw12 ∷ Bx⁻4-0312 ∷ []) (Bx⁻4-0321 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·0312⟩ c4)

-- nat 1 SBOXd(4;0;31;2): 7 steps
lem-nat-1-SBOXd⟨4·0·31·2⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻4-0-31-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-32-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨4·0·31·2⟩ c4 = derive (Sw12 ∷ Sb⁻4-0-31-2 ∷ []) (Sb⁻4-0-32-1 ∷ Sw12 ∷ [])
  (re 1 1 (Sb4-0-2-1 ∷ Toff213 ∷ Sb⁻4-0-2-1 ∷ Toff213 ∷ Bx⁻4-0312 ∷ []) ∷
   rw 0 (q156 c4) ∷
   rw 1 (q157 c4) ∷
   rw 2 (q158 c4) ∷
   rw 3 (q157 c4) ∷
   rw 4 (q159 c4) ∷
   re 0 5 (Sb⁻4-0-32-1 ∷ []) ∷ []) Eq.refl

private
  q160 : WsL → Eqn
  q160 c4 = eqn (Bx⁻4-01 ∷ Sw23 ∷ []) (Sw23 ∷ Bx⁻4-01 ∷ []) (c₂ (CZ) (Swap))

-- nat 2 BOXd(0;421): 8 steps
lem-nat-2-BOXd⟨0·421⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-421 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-431 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·421⟩ c4 = derive (Sw23 ∷ Bx⁻0-421 ∷ []) (Bx⁻0-431 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻4-01 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻4-01 ∷ Toff024 ∷ CCZ024 ∷ []) ∷
   rw⁻ 0 (q160 c4) ∷
   rw 1 (q25 c4) ∷
   rw 2 (q26 c4) ∷
   rw⁻ 3 (q160 c4) ∷
   rw 4 (q26 c4) ∷
   rw 5 (q25 c4) ∷
   re 0 6 (Bx⁻0-431 ∷ []) ∷ []) Eq.refl

private
  q161 : WsL → Eqn
  q161 c4 = eqn (Sw23 ∷ Bx⁻0-421 ∷ []) (Bx⁻0-431 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·421⟩ c4)
  q162 : WsL → Eqn
  q162 c4 = eqn (Sw23 ∷ Toff403 ∷ []) (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4)

-- nat 2 BOXd(4;0321): 8 steps
lem-nat-2-BOXd⟨4·0321⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0231 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨4·0321⟩ c4 = derive (Sw23 ∷ Bx⁻4-0321 ∷ []) (Bx⁻4-0231 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻0-421 ∷ CCZ034 ∷ Toff403 ∷ Bx⁻0-421 ∷ Toff403 ∷ CCZ034 ∷ []) ∷
   rw 0 (q161 c4) ∷
   rw 1 (q18 c4) ∷
   rw 2 (q162 c4) ∷
   rw 3 (q161 c4) ∷
   rw 4 (q162 c4) ∷
   rw 5 (q18 c4) ∷
   re 0 6 (Bx⁻4-0231 ∷ []) ∷ []) Eq.refl

private
  q163 : WsL → Eqn
  q163 c4 = eqn (Sw23 ∷ Sb4-0-1-2 ∷ []) (Sb4-0-1-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·0·1·2⟩ c4)
  q164 : WsL → Eqn
  q164 c4 = eqn (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ []) (wl0114 c4)
  q165 : WsL → Eqn
  q165 c4 = eqn (Sw23 ∷ Sb⁻4-0-1-2 ∷ []) (Sb⁻4-0-1-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨4·0·1·2⟩ c4)
  q166 : WsL → Eqn
  q166 c4 = eqn (Sw23 ∷ Bx⁻4-0321 ∷ []) (Bx⁻4-0231 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·0321⟩ c4)

-- nat 2 SBOXd(4;0;32;1): 7 steps
lem-nat-2-SBOXd⟨4·0·32·1⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻4-0-32-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-23-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨4·0·32·1⟩ c4 = derive (Sw23 ∷ Sb⁻4-0-32-1 ∷ []) (Sb⁻4-0-23-1 ∷ Sw23 ∷ [])
  (re 1 1 (Sb4-0-1-2 ∷ Toff123 ∷ Sb⁻4-0-1-2 ∷ Toff123 ∷ Bx⁻4-0321 ∷ []) ∷
   rw 0 (q163 c4) ∷
   rw 1 (q164 c4) ∷
   rw 2 (q165 c4) ∷
   rw 3 (q164 c4) ∷
   rw 4 (q166 c4) ∷
   re 0 5 (Sb⁻4-0-23-1 ∷ []) ∷ []) Eq.refl

-- nat 0 BOXd(4;01): 3 steps
lem-nat-0-BOXd⟨4·01⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻4-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-10 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨4·01⟩ c4 = derive (Sw01 ∷ Bx⁻4-01 ∷ []) (Bx⁻4-10 ∷ Sw01 ∷ [])
  (re 1 1 (CZ01 ∷ []) ∷
   rw⁻ 0 (q41 c4) ∷
   re 0 1 (Bx⁻4-10 ∷ []) ∷ []) Eq.refl

private
  q167 : WsL → Eqn
  q167 c4 = eqn (Sw01 ∷ Bx⁻4-01 ∷ []) (Bx⁻4-10 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·01⟩ c4)
  q168 : WsL → Eqn
  q168 c4 = eqn (Sw01 ∷ CCZ034 ∷ []) (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4)
  q169 : WsL → Eqn
  q169 c4 = eqn (Sw01 ∷ Toff034 ∷ []) (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4)

-- nat 0 BOXd(0;431): 8 steps
lem-nat-0-BOXd⟨0·431⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻0-431 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-430 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·431⟩ c4 = derive (Sw01 ∷ Bx⁻0-431 ∷ []) (Bx⁻1-430 ∷ Sw01 ∷ [])
  (re 1 1 (Bx⁻4-01 ∷ CCZ034 ∷ Toff034 ∷ Bx⁻4-01 ∷ Toff034 ∷ CCZ034 ∷ []) ∷
   rw 0 (q167 c4) ∷
   rw 1 (q168 c4) ∷
   rw 2 (q169 c4) ∷
   rw 3 (q167 c4) ∷
   rw 4 (q169 c4) ∷
   rw 5 (q168 c4) ∷
   re 0 6 (Bx⁻1-430 ∷ []) ∷ []) Eq.refl

private
  q170 : WsL → Eqn
  q170 c4 = eqn (Sw01 ∷ Bx⁻0-431 ∷ []) (Bx⁻1-430 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·431⟩ c4)
  q171 : WsL → Eqn
  q171 c4 = eqn (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4)
  q172 : WsL → Eqn
  q172 c4 = eqn (Sw01 ∷ Toff402 ∷ []) (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4)

-- nat 0 BOXd(4;0231): 8 steps
lem-nat-0-BOXd⟨4·0231⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻4-0231 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-1230 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨4·0231⟩ c4 = derive (Sw01 ∷ Bx⁻4-0231 ∷ []) (Bx⁻4-1230 ∷ Sw01 ∷ [])
  (re 1 1 (Bx⁻0-431 ∷ CCZ024 ∷ Toff402 ∷ Bx⁻0-431 ∷ Toff402 ∷ CCZ024 ∷ []) ∷
   rw 0 (q170 c4) ∷
   rw 1 (q171 c4) ∷
   rw 2 (q172 c4) ∷
   rw 3 (q170 c4) ∷
   rw 4 (q172 c4) ∷
   rw 5 (q171 c4) ∷
   re 0 6 (Bx⁻4-1230 ∷ []) ∷ []) Eq.refl

private
  q173 : WsL → Eqn
  q173 c4 = eqn (Sw01 ∷ Sb4-0-1-3 ∷ []) (Sb4-1-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨4·0·1·3⟩ c4)
  q174 : WsL → Eqn
  q174 c4 = eqn (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) (wl0053 c4)
  q175 : WsL → Eqn
  q175 c4 = eqn (Sw01 ∷ Sb⁻4-0-1-3 ∷ []) (Sb⁻4-1-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨4·0·1·3⟩ c4)
  q176 : WsL → Eqn
  q176 c4 = eqn (Sw01 ∷ Bx⁻4-0231 ∷ []) (Bx⁻4-1230 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·0231⟩ c4)

-- nat 0 SBOXd(4;0;23;1): 7 steps
lem-nat-0-SBOXd⟨4·0·23·1⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻4-0-23-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-1-23-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨4·0·23·1⟩ c4 = derive (Sw01 ∷ Sb⁻4-0-23-1 ∷ []) (Sb⁻4-1-23-0 ∷ Sw01 ∷ [])
  (re 1 1 (Sb4-0-1-3 ∷ Toff123 ∷ Sb⁻4-0-1-3 ∷ Toff123 ∷ Bx⁻4-0231 ∷ []) ∷
   rw 0 (q173 c4) ∷
   rw 1 (q174 c4) ∷
   rw 2 (q175 c4) ∷
   rw 3 (q174 c4) ∷
   rw 4 (q176 c4) ∷
   re 0 5 (Sb⁻4-1-23-0 ∷ []) ∷ []) Eq.refl

private
  q177 : WsL → Eqn
  q177 c4 = eqn (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) (wl0101 c4)

-- nat 0 BOXd(0;134): 8 steps
lem-nat-0-BOXd⟨0·134⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻0-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-034 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·134⟩ c4 = derive (Sw01 ∷ Bx⁻0-134 ∷ []) (Bx⁻1-034 ∷ Sw01 ∷ [])
  (re 1 1 (Bx⁻1-04 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-04 ∷ Toff013 ∷ CCZ013 ∷ []) ∷
   rw 0 (q127 c4) ∷
   rw⁻ 1 (q118 c4) ∷
   rw 2 (q177 c4) ∷
   rw 3 (q127 c4) ∷
   rw 4 (q177 c4) ∷
   rw⁻ 5 (q118 c4) ∷
   re 0 6 (Bx⁻1-034 ∷ []) ∷ []) Eq.refl

private
  q178 : WsL → Eqn
  q178 c4 = eqn (Sw01 ∷ Bx⁻0-134 ∷ []) (Bx⁻1-034 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·134⟩ c4)
  q179 : WsL → Eqn
  q179 c4 = eqn (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) (wl0097 c4)

-- nat 0 BOXd(1;0234): 8 steps
lem-nat-0-BOXd⟨1·0234⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1234 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·0234⟩ c4 = derive (Sw01 ∷ Bx⁻1-0234 ∷ []) (Bx⁻0-1234 ∷ Sw01 ∷ [])
  (re 1 1 (Bx⁻0-134 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-134 ∷ Toff102 ∷ CCZ012 ∷ []) ∷
   rw 0 (q178 c4) ∷
   rw⁻ 1 (q121 c4) ∷
   rw 2 (q179 c4) ∷
   rw 3 (q178 c4) ∷
   rw 4 (q179 c4) ∷
   rw⁻ 5 (q121 c4) ∷
   re 0 6 (Bx⁻0-1234 ∷ []) ∷ []) Eq.refl

private
  q180 : WsL → Eqn
  q180 c4 = eqn (Sw12 ∷ Toff013 ∷ []) (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4)

-- nat 1 BOXd(0;134): 8 steps
lem-nat-1-BOXd⟨0·134⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻0-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-234 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·134⟩ c4 = derive (Sw12 ∷ Bx⁻0-134 ∷ []) (Bx⁻0-234 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻1-04 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-04 ∷ Toff013 ∷ CCZ013 ∷ []) ∷
   rw 0 (q89 c4) ∷
   rw 1 (q93 c4) ∷
   rw 2 (q180 c4) ∷
   rw 3 (q89 c4) ∷
   rw 4 (q180 c4) ∷
   rw 5 (q93 c4) ∷
   re 0 6 (Bx⁻0-234 ∷ []) ∷ []) Eq.refl

private
  q181 : WsL → Eqn
  q181 c4 = eqn (Sw12 ∷ Bx⁻0-134 ∷ []) (Bx⁻0-234 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·134⟩ c4)
  q182 : WsL → Eqn
  q182 c4 = eqn (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) (wl0047 c4)

-- nat 1 BOXd(1;0234): 8 steps
lem-nat-1-BOXd⟨1·0234⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0134 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·0234⟩ c4 = derive (Sw12 ∷ Bx⁻1-0234 ∷ []) (Bx⁻2-0134 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻0-134 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-134 ∷ Toff102 ∷ CCZ012 ∷ []) ∷
   rw 0 (q181 c4) ∷
   rw⁻ 1 (q90 c4) ∷
   rw 2 (q182 c4) ∷
   rw 3 (q181 c4) ∷
   rw 4 (q182 c4) ∷
   rw⁻ 5 (q90 c4) ∷
   re 0 6 (Bx⁻2-0134 ∷ []) ∷ []) Eq.refl

-- nat 2 BOXd(3;04): 3 steps
lem-nat-2-BOXd⟨3·04⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻3-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-04 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨3·04⟩ c4 = derive (Sw23 ∷ Bx⁻3-04 ∷ []) (Bx⁻2-04 ∷ Sw23 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   rw 0 (q105 c4) ∷
   re 0 1 (Bx⁻2-04 ∷ []) ∷ []) Eq.refl

private
  q183 : WsL → Eqn
  q183 c4 = eqn (Sw23 ∷ Bx⁻3-04 ∷ []) (Bx⁻2-04 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·04⟩ c4)
  q184 : WsL → Eqn
  q184 c4 = eqn (CCZ023 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ023 ∷ []) (wl0065 c4)
  q185 : WsL → Eqn
  q185 c4 = eqn (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) (wl0093 c4)

-- nat 2 BOXd(0;324): 8 steps
lem-nat-2-BOXd⟨0·324⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-234 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·324⟩ c4 = derive (Sw23 ∷ Bx⁻0-324 ∷ []) (Bx⁻0-234 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻3-04 ∷ CCZ023 ∷ Toff023 ∷ Bx⁻3-04 ∷ Toff023 ∷ CCZ023 ∷ []) ∷
   rw 0 (q183 c4) ∷
   rw⁻ 1 (q184 c4) ∷
   rw 2 (q185 c4) ∷
   rw 3 (q183 c4) ∷
   rw 4 (q185 c4) ∷
   rw⁻ 5 (q184 c4) ∷
   re 0 6 (Bx⁻0-234 ∷ []) ∷ []) Eq.refl

private
  q186 : WsL → Eqn
  q186 c4 = eqn (Sw23 ∷ Bx⁻0-324 ∷ []) (Bx⁻0-234 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·324⟩ c4)
  q187 : WsL → Eqn
  q187 c4 = eqn (Sw23 ∷ Toff301 ∷ []) (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4)

-- nat 2 BOXd(3;0124): 8 steps
lem-nat-2-BOXd⟨3·0124⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0134 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨3·0124⟩ c4 = derive (Sw23 ∷ Bx⁻3-0124 ∷ []) (Bx⁻2-0134 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻0-324 ∷ CCZ013 ∷ Toff301 ∷ Bx⁻0-324 ∷ Toff301 ∷ CCZ013 ∷ []) ∷
   rw 0 (q186 c4) ∷
   rw 1 (q107 c4) ∷
   rw 2 (q187 c4) ∷
   rw 3 (q186 c4) ∷
   rw 4 (q187 c4) ∷
   rw 5 (q107 c4) ∷
   re 0 6 (Bx⁻2-0134 ∷ []) ∷ []) Eq.refl

-- nat 2 BOXd(2;04): 3 steps
lem-nat-2-BOXd⟨2·04⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻2-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-04 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨2·04⟩ c4 = derive (Sw23 ∷ Bx⁻2-04 ∷ []) (Bx⁻3-04 ∷ Sw23 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   rw 0 (q105 c4) ∷
   re 0 1 (Bx⁻3-04 ∷ []) ∷ []) Eq.refl

private
  q188 : WsL → Eqn
  q188 c4 = eqn (Sw23 ∷ Bx⁻2-04 ∷ []) (Bx⁻3-04 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨2·04⟩ c4)

-- nat 2 BOXd(0;234): 8 steps
lem-nat-2-BOXd⟨0·234⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-234 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-324 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·234⟩ c4 = derive (Sw23 ∷ Bx⁻0-234 ∷ []) (Bx⁻0-324 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻2-04 ∷ CCZ023 ∷ Toff023 ∷ Bx⁻2-04 ∷ Toff023 ∷ CCZ023 ∷ []) ∷
   rw 0 (q188 c4) ∷
   rw⁻ 1 (q184 c4) ∷
   rw 2 (q185 c4) ∷
   rw 3 (q188 c4) ∷
   rw 4 (q185 c4) ∷
   rw⁻ 5 (q184 c4) ∷
   re 0 6 (Bx⁻0-324 ∷ []) ∷ []) Eq.refl

private
  q189 : WsL → Eqn
  q189 c4 = eqn (Sw23 ∷ Bx⁻0-234 ∷ []) (Bx⁻0-324 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·234⟩ c4)
  q190 : WsL → Eqn
  q190 c4 = eqn (Sw23 ∷ Toff201 ∷ []) (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4)

-- nat 2 BOXd(2;0134): 8 steps
lem-nat-2-BOXd⟨2·0134⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-0124 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨2·0134⟩ c4 = derive (Sw23 ∷ Bx⁻2-0134 ∷ []) (Bx⁻3-0124 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻0-234 ∷ CCZ012 ∷ Toff201 ∷ Bx⁻0-234 ∷ Toff201 ∷ CCZ012 ∷ []) ∷
   rw 0 (q189 c4) ∷
   rw 1 (q110 c4) ∷
   rw 2 (q190 c4) ∷
   rw 3 (q189 c4) ∷
   rw 4 (q190 c4) ∷
   rw 5 (q110 c4) ∷
   re 0 6 (Bx⁻3-0124 ∷ []) ∷ []) Eq.refl

-- nat 3 BOXd(4;03): 3 steps
lem-nat-3-BOXd⟨4·03⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-04 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨4·03⟩ c4 = derive (Sw34 ∷ Bx⁻4-03 ∷ []) (Bx⁻3-04 ∷ Sw34 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw 0 (q84 c4) ∷
   re 0 1 (Bx⁻3-04 ∷ []) ∷ []) Eq.refl

private
  q191 : WsL → Eqn
  q191 c4 = eqn (Sw34 ∷ Bx⁻4-03 ∷ []) (Bx⁻3-04 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨4·03⟩ c4)

-- nat 3 BOXd(0;423): 8 steps
lem-nat-3-BOXd⟨0·423⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻0-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-324 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·423⟩ c4 = derive (Sw34 ∷ Bx⁻0-423 ∷ []) (Bx⁻0-324 ∷ Sw34 ∷ [])
  (re 1 1 (Bx⁻4-03 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻4-03 ∷ Toff024 ∷ CCZ024 ∷ []) ∷
   rw 0 (q191 c4) ∷
   rw 1 (q48 c4) ∷
   rw 2 (q49 c4) ∷
   rw 3 (q191 c4) ∷
   rw 4 (q49 c4) ∷
   rw 5 (q48 c4) ∷
   re 0 6 (Bx⁻0-324 ∷ []) ∷ []) Eq.refl

private
  q192 : WsL → Eqn
  q192 c4 = eqn (Sw34 ∷ Bx⁻0-423 ∷ []) (Bx⁻0-324 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·423⟩ c4)
  q193 : WsL → Eqn
  q193 c4 = eqn (Sw34 ∷ CCZ014 ∷ []) (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4)
  q194 : WsL → Eqn
  q194 c4 = eqn (Sw34 ∷ Toff401 ∷ []) (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4)

-- nat 3 BOXd(4;0123): 8 steps
lem-nat-3-BOXd⟨4·0123⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-0124 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨4·0123⟩ c4 = derive (Sw34 ∷ Bx⁻4-0123 ∷ []) (Bx⁻3-0124 ∷ Sw34 ∷ [])
  (re 1 1 (Bx⁻0-423 ∷ CCZ014 ∷ Toff401 ∷ Bx⁻0-423 ∷ Toff401 ∷ CCZ014 ∷ []) ∷
   rw 0 (q192 c4) ∷
   rw 1 (q193 c4) ∷
   rw 2 (q194 c4) ∷
   rw 3 (q192 c4) ∷
   rw 4 (q194 c4) ∷
   rw 5 (q193 c4) ∷
   re 0 6 (Bx⁻3-0124 ∷ []) ∷ []) Eq.refl

-- nat 3 BOXd(3;04): 3 steps
lem-nat-3-BOXd⟨3·04⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻3-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-03 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨3·04⟩ c4 = derive (Sw34 ∷ Bx⁻3-04 ∷ []) (Bx⁻4-03 ∷ Sw34 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   rw 0 (q74 c4) ∷
   re 0 1 (Bx⁻4-03 ∷ []) ∷ []) Eq.refl

private
  q195 : WsL → Eqn
  q195 c4 = eqn (Sw34 ∷ Bx⁻3-04 ∷ []) (Bx⁻4-03 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨3·04⟩ c4)
  q196 : WsL → Eqn
  q196 c4 = eqn (Sw34 ∷ Toff023 ∷ []) (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4)

-- nat 3 BOXd(0;324): 8 steps
lem-nat-3-BOXd⟨0·324⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻0-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-423 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·324⟩ c4 = derive (Sw34 ∷ Bx⁻0-324 ∷ []) (Bx⁻0-423 ∷ Sw34 ∷ [])
  (re 1 1 (Bx⁻3-04 ∷ CCZ023 ∷ Toff023 ∷ Bx⁻3-04 ∷ Toff023 ∷ CCZ023 ∷ []) ∷
   rw 0 (q195 c4) ∷
   rw 1 (q78 c4) ∷
   rw 2 (q196 c4) ∷
   rw 3 (q195 c4) ∷
   rw 4 (q196 c4) ∷
   rw 5 (q78 c4) ∷
   re 0 6 (Bx⁻0-423 ∷ []) ∷ []) Eq.refl

private
  q197 : WsL → Eqn
  q197 c4 = eqn (Sw34 ∷ Bx⁻0-324 ∷ []) (Bx⁻0-423 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·324⟩ c4)
  q198 : WsL → Eqn
  q198 c4 = eqn (Sw34 ∷ Toff301 ∷ []) (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4)

-- nat 3 BOXd(3;0124): 8 steps
lem-nat-3-BOXd⟨3·0124⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0123 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨3·0124⟩ c4 = derive (Sw34 ∷ Bx⁻3-0124 ∷ []) (Bx⁻4-0123 ∷ Sw34 ∷ [])
  (re 1 1 (Bx⁻0-324 ∷ CCZ013 ∷ Toff301 ∷ Bx⁻0-324 ∷ Toff301 ∷ CCZ013 ∷ []) ∷
   rw 0 (q197 c4) ∷
   rw 1 (q142 c4) ∷
   rw 2 (q198 c4) ∷
   rw 3 (q197 c4) ∷
   rw 4 (q198 c4) ∷
   rw 5 (q142 c4) ∷
   re 0 6 (Bx⁻4-0123 ∷ []) ∷ []) Eq.refl

-- nat 2 BOXd(4;02): 3 steps
lem-nat-2-BOXd⟨4·02⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻4-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-03 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨4·02⟩ c4 = derive (Sw23 ∷ Bx⁻4-02 ∷ []) (Bx⁻4-03 ∷ Sw23 ∷ [])
  (re 1 1 (CZ02 ∷ []) ∷
   rw 0 (q17 c4) ∷
   re 0 1 (Bx⁻4-03 ∷ []) ∷ []) Eq.refl

private
  q199 : WsL → Eqn
  q199 c4 = eqn (Sw23 ∷ Bx⁻4-02 ∷ []) (Bx⁻4-03 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·02⟩ c4)

-- nat 2 BOXd(0;432): 8 steps
lem-nat-2-BOXd⟨0·432⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-432 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-423 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·432⟩ c4 = derive (Sw23 ∷ Bx⁻0-432 ∷ []) (Bx⁻0-423 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻4-02 ∷ CCZ034 ∷ Toff034 ∷ Bx⁻4-02 ∷ Toff034 ∷ CCZ034 ∷ []) ∷
   rw 0 (q199 c4) ∷
   rw 1 (q18 c4) ∷
   rw 2 (q19 c4) ∷
   rw 3 (q199 c4) ∷
   rw 4 (q19 c4) ∷
   rw 5 (q18 c4) ∷
   re 0 6 (Bx⁻0-423 ∷ []) ∷ []) Eq.refl

private
  q200 : WsL → Eqn
  q200 c4 = eqn (Sw23 ∷ Bx⁻0-432 ∷ []) (Bx⁻0-423 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·432⟩ c4)

-- nat 2 BOXd(4;0132): 8 steps
lem-nat-2-BOXd⟨4·0132⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻4-0132 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0123 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨4·0132⟩ c4 = derive (Sw23 ∷ Bx⁻4-0132 ∷ []) (Bx⁻4-0123 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻0-432 ∷ CCZ014 ∷ Toff401 ∷ Bx⁻0-432 ∷ Toff401 ∷ CCZ014 ∷ []) ∷
   rw 0 (q200 c4) ∷
   rw 1 (q21 c4) ∷
   rw 2 (q22 c4) ∷
   rw 3 (q200 c4) ∷
   rw 4 (q22 c4) ∷
   rw 5 (q21 c4) ∷
   re 0 6 (Bx⁻4-0123 ∷ []) ∷ []) Eq.refl

-- nat 2 BOXd(4;03): 3 steps
lem-nat-2-BOXd⟨4·03⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻4-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-02 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨4·03⟩ c4 = derive (Sw23 ∷ Bx⁻4-03 ∷ []) (Bx⁻4-02 ∷ Sw23 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw 0 (q24 c4) ∷
   re 0 1 (Bx⁻4-02 ∷ []) ∷ []) Eq.refl

private
  q201 : WsL → Eqn
  q201 c4 = eqn (Sw23 ∷ Bx⁻4-03 ∷ []) (Bx⁻4-02 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·03⟩ c4)

-- nat 2 BOXd(0;423): 8 steps
lem-nat-2-BOXd⟨0·423⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-432 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·423⟩ c4 = derive (Sw23 ∷ Bx⁻0-423 ∷ []) (Bx⁻0-432 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻4-03 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻4-03 ∷ Toff024 ∷ CCZ024 ∷ []) ∷
   rw 0 (q201 c4) ∷
   rw 1 (q25 c4) ∷
   rw 2 (q26 c4) ∷
   rw 3 (q201 c4) ∷
   rw 4 (q26 c4) ∷
   rw 5 (q25 c4) ∷
   re 0 6 (Bx⁻0-432 ∷ []) ∷ []) Eq.refl

private
  q202 : WsL → Eqn
  q202 c4 = eqn (Sw23 ∷ Bx⁻0-423 ∷ []) (Bx⁻0-432 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·423⟩ c4)

-- nat 2 BOXd(4;0123): 8 steps
lem-nat-2-BOXd⟨4·0123⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0132 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨4·0123⟩ c4 = derive (Sw23 ∷ Bx⁻4-0123 ∷ []) (Bx⁻4-0132 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻0-423 ∷ CCZ014 ∷ Toff401 ∷ Bx⁻0-423 ∷ Toff401 ∷ CCZ014 ∷ []) ∷
   rw 0 (q202 c4) ∷
   rw 1 (q21 c4) ∷
   rw 2 (q22 c4) ∷
   rw 3 (q202 c4) ∷
   rw 4 (q22 c4) ∷
   rw 5 (q21 c4) ∷
   re 0 6 (Bx⁻4-0132 ∷ []) ∷ []) Eq.refl

-- nat 1 BOXd(4;01): 3 steps
lem-nat-1-BOXd⟨4·01⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻4-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-02 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·01⟩ c4 = derive (Sw12 ∷ Bx⁻4-01 ∷ []) (Bx⁻4-02 ∷ Sw12 ∷ [])
  (re 1 1 (CZ01 ∷ []) ∷
   rw 0 (q30 c4) ∷
   re 0 1 (Bx⁻4-02 ∷ []) ∷ []) Eq.refl

private
  q203 : WsL → Eqn
  q203 c4 = eqn (Sw12 ∷ Bx⁻4-01 ∷ []) (Bx⁻4-02 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·01⟩ c4)

-- nat 1 BOXd(0;431): 8 steps
lem-nat-1-BOXd⟨0·431⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻0-431 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-432 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·431⟩ c4 = derive (Sw12 ∷ Bx⁻0-431 ∷ []) (Bx⁻0-432 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻4-01 ∷ CCZ034 ∷ Toff034 ∷ Bx⁻4-01 ∷ Toff034 ∷ CCZ034 ∷ []) ∷
   rw 0 (q203 c4) ∷
   rw 1 (q31 c4) ∷
   rw 2 (q32 c4) ∷
   rw 3 (q203 c4) ∷
   rw 4 (q32 c4) ∷
   rw 5 (q31 c4) ∷
   re 0 6 (Bx⁻0-432 ∷ []) ∷ []) Eq.refl

private
  q204 : WsL → Eqn
  q204 c4 = eqn (Sw12 ∷ Bx⁻0-431 ∷ []) (Bx⁻0-432 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·431⟩ c4)

-- nat 1 BOXd(4;0231): 8 steps
lem-nat-1-BOXd⟨4·0231⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻4-0231 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0132 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·0231⟩ c4 = derive (Sw12 ∷ Bx⁻4-0231 ∷ []) (Bx⁻4-0132 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻0-431 ∷ CCZ024 ∷ Toff402 ∷ Bx⁻0-431 ∷ Toff402 ∷ CCZ024 ∷ []) ∷
   rw 0 (q204 c4) ∷
   rw 1 (q34 c4) ∷
   rw 2 (q35 c4) ∷
   rw 3 (q204 c4) ∷
   rw 4 (q35 c4) ∷
   rw 5 (q34 c4) ∷
   re 0 6 (Bx⁻4-0132 ∷ []) ∷ []) Eq.refl

-- nat 1 BOXd(0;432): 8 steps
lem-nat-1-BOXd⟨0·432⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻0-432 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-431 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·432⟩ c4 = derive (Sw12 ∷ Bx⁻0-432 ∷ []) (Bx⁻0-431 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻4-02 ∷ CCZ034 ∷ Toff034 ∷ Bx⁻4-02 ∷ Toff034 ∷ CCZ034 ∷ []) ∷
   rw 0 (q152 c4) ∷
   rw 1 (q31 c4) ∷
   rw 2 (q32 c4) ∷
   rw 3 (q152 c4) ∷
   rw 4 (q32 c4) ∷
   rw 5 (q31 c4) ∷
   re 0 6 (Bx⁻0-431 ∷ []) ∷ []) Eq.refl

private
  q205 : WsL → Eqn
  q205 c4 = eqn (Sw12 ∷ Bx⁻0-432 ∷ []) (Bx⁻0-431 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·432⟩ c4)

-- nat 1 BOXd(4;0132): 8 steps
lem-nat-1-BOXd⟨4·0132⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻4-0132 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0231 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·0132⟩ c4 = derive (Sw12 ∷ Bx⁻4-0132 ∷ []) (Bx⁻4-0231 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻0-432 ∷ CCZ014 ∷ Toff401 ∷ Bx⁻0-432 ∷ Toff401 ∷ CCZ014 ∷ []) ∷
   rw 0 (q205 c4) ∷
   rw 1 (q38 c4) ∷
   rw 2 (q39 c4) ∷
   rw 3 (q205 c4) ∷
   rw 4 (q39 c4) ∷
   rw 5 (q38 c4) ∷
   re 0 6 (Bx⁻4-0231 ∷ []) ∷ []) Eq.refl

-- nat 0 BOXd(4;10): 3 steps
lem-nat-0-BOXd⟨4·10⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻4-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-01 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨4·10⟩ c4 = derive (Sw01 ∷ Bx⁻4-10 ∷ []) (Bx⁻4-01 ∷ Sw01 ∷ [])
  (re 1 1 (CZ01 ∷ []) ∷
   rw⁻ 0 (q41 c4) ∷
   re 0 1 (Bx⁻4-01 ∷ []) ∷ []) Eq.refl

private
  q206 : WsL → Eqn
  q206 c4 = eqn (Sw01 ∷ Bx⁻4-10 ∷ []) (Bx⁻4-01 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·10⟩ c4)

-- nat 0 BOXd(1;430): 8 steps
lem-nat-0-BOXd⟨1·430⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻1-430 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-431 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·430⟩ c4 = derive (Sw01 ∷ Bx⁻1-430 ∷ []) (Bx⁻0-431 ∷ Sw01 ∷ [])
  (re 1 1 (Bx⁻4-10 ∷ CCZ134 ∷ Toff134 ∷ Bx⁻4-10 ∷ Toff134 ∷ CCZ134 ∷ []) ∷
   rw 0 (q206 c4) ∷
   rw 1 (q42 c4) ∷
   rw 2 (q43 c4) ∷
   rw 3 (q206 c4) ∷
   rw 4 (q43 c4) ∷
   rw 5 (q42 c4) ∷
   re 0 6 (Bx⁻0-431 ∷ []) ∷ []) Eq.refl

private
  q207 : WsL → Eqn
  q207 c4 = eqn (Sw01 ∷ Bx⁻1-430 ∷ []) (Bx⁻0-431 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·430⟩ c4)

-- nat 0 BOXd(4;1230): 8 steps
lem-nat-0-BOXd⟨4·1230⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-0231 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨4·1230⟩ c4 = derive (Sw01 ∷ Bx⁻4-1230 ∷ []) (Bx⁻4-0231 ∷ Sw01 ∷ [])
  (re 1 1 (Bx⁻1-430 ∷ CCZ124 ∷ Toff412 ∷ Bx⁻1-430 ∷ Toff412 ∷ CCZ124 ∷ []) ∷
   rw 0 (q207 c4) ∷
   rw 1 (q45 c4) ∷
   rw 2 (q46 c4) ∷
   rw 3 (q207 c4) ∷
   rw 4 (q46 c4) ∷
   rw 5 (q45 c4) ∷
   re 0 6 (Bx⁻4-0231 ∷ []) ∷ []) Eq.refl

private
  q208 : WsL → Eqn
  q208 c4 = eqn (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ []) (wl0018 c4)
  q209 : WsL → Eqn
  q209 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 c4)
  q210 : WsL → Eqn
  q210 c4 = eqn (Sw01 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))

-- resp CSd14 at 2: 4 steps
lem-resp-CSd14-at-2 : WsL → ⟪ (CS14⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS24⁻ ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CSd14-at-2 c4 = derive (CS14⁻ ∷ []) (Sw12 ∷ Sw01 ∷ CS24⁻ ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q29 c4) ∷
   rw 0 (q208 c4) ∷
   rw⁻ 2 (q209 c4) ∷
   rw⁻ 1 (q210 c4) ∷ []) Eq.refl

-- nat 2 CS03: 2 steps
lem-nat-2-CS03 : WsL → ⟪ (Sw23 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CS03 c4 = derive (Sw23 ∷ CS03 ∷ []) (CS02 ∷ Sw23 ∷ [])
  (re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 0 (q2 c4) ∷ []) Eq.refl

private
  q211 : WsL → Eqn
  q211 c4 = eqn (CX23 ∷ Sw12 ∷ []) (Sw12 ∷ CX13 ∷ []) (wl0052 c4)
  q212 : WsL → Eqn
  q212 c4 = eqn (CX34 ∷ Sw23 ∷ []) (Sw23 ∷ CX24 ∷ []) (wl0051 c4)
  q213 : WsL → Eqn
  q213 c4 = eqn (CCZ012 ∷ CX34 ∷ []) (CX34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₀₁))
  q214 : WsL → Eqn
  q214 c4 = eqn (CX24 ∷ Sw23 ∷ []) (Sw23 ∷ CX34 ∷ []) (wl0050 c4)
  q215 : WsL → Eqn
  q215 c4 = eqn (CX13 ∷ Sw12 ∷ []) (Sw12 ∷ CX23 ∷ []) (wl0049 c4)

-- comm CCZ024 CX13: 11 steps
lem-comm-CCZ024-CX13 : WsL → ⟪ (CCZ024 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CCZ024 ∷ []) ⟫ʷ
lem-comm-CCZ024-CX13 c4 = derive (CCZ024 ∷ CX13 ∷ []) (CX13 ∷ CCZ024 ∷ [])
  (re 0 1 (Sw12 ∷ Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ []) ∷
   rw⁻ 6 (q211 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (CX24 ∷ []) ∷
   rw⁻ 4 (q212 c4) ∷
   rw 3 (q213 c4) ∷
   rw⁻ 2 (q214 c4) ∷
   re 2 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) ∷
   rw 1 (q6 c4) ∷
   rw⁻ 0 (q215 c4) ∷
   re 1 7 (CCZ024 ∷ []) ∷ []) Eq.refl

private
  q216 : WsL → Eqn
  q216 c4 = eqn (CS03⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS13⁻ ∷ []) (wl0022 c4)

-- resp CSd03 at 1: 2 steps
lem-resp-CSd03-at-1 : WsL → ⟪ (CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS13⁻ ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CSd03-at-1 c4 = derive (CS03⁻ ∷ []) (Sw01 ∷ CS13⁻ ∷ Sw01 ∷ [])
  (rw⁻ 1 (q209 c4) ∷
   rw 0 (q216 c4) ∷ []) Eq.refl

private
  q217 : WsL → Eqn
  q217 c4 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (c₂ (Swap) (CX₀₁))

-- resp CX13 at 2: 4 steps
lem-resp-CX13-at-2 : WsL → ⟪ (CX13 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX23 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX13-at-2 c4 = derive (CX13 ∷ []) (Sw12 ∷ Sw01 ∷ CX23 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q29 c4) ∷
   rw 0 (q215 c4) ∷
   rw⁻ 2 (q209 c4) ∷
   rw⁻ 1 (q217 c4) ∷ []) Eq.refl

-- nat 2 CSd03: 2 steps
lem-nat-2-CSd03 : WsL → ⟪ (Sw23 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CSd03 c4 = derive (Sw23 ∷ CS03⁻ ∷ []) (CS02⁻ ∷ Sw23 ∷ [])
  (re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 0 (q2 c4) ∷ []) Eq.refl

private
  q218 : WsL → Eqn
  q218 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl0015 c4)
  q219 : WsL → Eqn
  q219 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q220 : WsL → Eqn
  q220 c4 = eqn (Sw01 ∷ CS34 ∷ []) (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))

-- resp CS24 at 3: 6 steps
lem-resp-CS24-at-3 : WsL → ⟪ (CS24 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CS24-at-3 c4 = derive (CS24 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q2 c4) ∷
   rw 0 (q218 c4) ∷
   rw⁻ 2 (q29 c4) ∷
   rw⁻ 1 (q219 c4) ∷
   rw⁻ 3 (q209 c4) ∷
   rw⁻ 2 (q220 c4) ∷ []) Eq.refl

private
  q221 : WsL → Eqn
  q221 c4 = eqn (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) (wl0084 c4)
  q222 : WsL → Eqn
  q222 c4 = eqn (CS01⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ))
  q223 : WsL → Eqn
  q223 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl0034 c4)

-- comm CSd03 CCZ124: 9 steps
lem-comm-CSd03-CCZ124 : WsL → ⟪ (CS03⁻ ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-comm-CSd03-CCZ124 c4 = derive (CS03⁻ ∷ CCZ124 ∷ []) (CCZ124 ∷ CS03⁻ ∷ [])
  (re 0 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (CCZ134 ∷ []) ∷
   rw⁻ 3 (q221 c4) ∷
   rw 2 (q222 c4) ∷
   rw⁻ 1 (q223 c4) ∷
   re 1 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 0 (q2 c4) ∷
   re 1 5 (CS03⁻ ∷ []) ∷ []) Eq.refl

private
  q224 : WsL → Eqn
  q224 c4 = eqn (Sw23 ∷ CS13⁻ ∷ []) (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 c4)

-- nat 2 SBOXd(0;1;3;2): 3 steps
lem-nat-2-SBOXd⟨0·1·3·2⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·1·3·2⟩ c4 = derive (Sw23 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-2-3 ∷ Sw23 ∷ [])
  (re 1 1 (CS13⁻ ∷ []) ∷
   rw 0 (q224 c4) ∷
   re 0 1 (Sb⁻0-1-2-3 ∷ []) ∷ []) Eq.refl

private
  q225 : WsL → Eqn
  q225 c4 = eqn (Sw23 ∷ Bx0-13 ∷ []) (Bx0-12 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·13⟩ c4)

-- nat 2 BOX(1;023): 8 steps
lem-nat-2-BOX⟨1·023⟩ : WsL → ⟪ (Sw23 ∷ Bx1-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-032 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·023⟩ c4 = derive (Sw23 ∷ Bx1-023 ∷ []) (Bx1-032 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) ∷
   rw 0 (q110 c4) ∷
   rw 1 (q111 c4) ∷
   rw 2 (q225 c4) ∷
   rw 3 (q111 c4) ∷
   rw 4 (q110 c4) ∷
   rw 5 (q225 c4) ∷
   re 0 6 (Bx1-032 ∷ []) ∷ []) Eq.refl

private
  q226 : WsL → Eqn
  q226 c4 = eqn (Sw23 ∷ Toff014 ∷ []) (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4)
  q227 : WsL → Eqn
  q227 c4 = eqn (Sw23 ∷ Bx1-023 ∷ []) (Bx1-032 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·023⟩ c4)

-- nat 2 BOX(0;1423): 8 steps
lem-nat-2-BOX⟨0·1423⟩ : WsL → ⟪ (Sw23 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·1423⟩ c4 = derive (Sw23 ∷ Bx0-1423 ∷ []) (Bx0-1432 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) ∷
   rw 0 (q21 c4) ∷
   rw 1 (q226 c4) ∷
   rw 2 (q227 c4) ∷
   rw 3 (q226 c4) ∷
   rw 4 (q21 c4) ∷
   rw 5 (q227 c4) ∷
   re 0 6 (Bx0-1432 ∷ []) ∷ []) Eq.refl

private
  q228 : WsL → Eqn
  q228 c4 = eqn (Sw23 ∷ CS12⁻ ∷ []) (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 c4)

-- nat 2 SBOXd(0;1;2;3): 3 steps
lem-nat-2-SBOXd⟨0·1·2·3⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·1·2·3⟩ c4 = derive (Sw23 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-1-3-2 ∷ Sw23 ∷ [])
  (re 1 1 (CS12⁻ ∷ []) ∷
   rw 0 (q228 c4) ∷
   re 0 1 (Sb⁻0-1-3-2 ∷ []) ∷ []) Eq.refl

private
  q229 : WsL → Eqn
  q229 c4 = eqn (Sw23 ∷ CS13 ∷ []) (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 c4)

-- nat 2 SBOX(0;1;3;2): 3 steps
lem-nat-2-SBOX⟨0·1·3·2⟩ : WsL → ⟪ (Sw23 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-2-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·1·3·2⟩ c4 = derive (Sw23 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-2-3 ∷ Sw23 ∷ [])
  (re 1 1 (CS13 ∷ []) ∷
   rw 0 (q229 c4) ∷
   re 0 1 (Sb0-1-2-3 ∷ []) ∷ []) Eq.refl

private
  q230 : WsL → Eqn
  q230 c4 = eqn (Sw23 ∷ CS12 ∷ []) (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 c4)

-- nat 2 SBOX(0;1;2;3): 3 steps
lem-nat-2-SBOX⟨0·1·2·3⟩ : WsL → ⟪ (Sw23 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·1·2·3⟩ c4 = derive (Sw23 ∷ Sb0-1-2-3 ∷ []) (Sb0-1-3-2 ∷ Sw23 ∷ [])
  (re 1 1 (CS12 ∷ []) ∷
   rw 0 (q230 c4) ∷
   re 0 1 (Sb0-1-3-2 ∷ []) ∷ []) Eq.refl

private
  q231 : WsL → Eqn
  q231 c4 = eqn (Sw01 ∷ Bx1-34 ∷ []) (Bx1-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑))

-- nat 0 BOX(1;34): 2 steps
lem-nat-0-BOX⟨1·34⟩ : WsL → ⟪ (Sw01 ∷ Bx1-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-34 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·34⟩ c4 = derive (Sw01 ∷ Bx1-34 ∷ []) (Bx0-34 ∷ Sw01 ∷ [])
  (rw 0 (q231 c4) ∷
   re 0 1 (Bx0-34 ∷ []) ∷ []) Eq.refl

private
  q232 : WsL → Eqn
  q232 c4 = eqn (CCZ023 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ123 ∷ []) (wl0003 c4)
  q233 : WsL → Eqn
  q233 c4 = eqn (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) (wl0110 c4)
  q234 : WsL → Eqn
  q234 c4 = eqn (Sw01 ∷ Bx1-34 ∷ []) (Bx0-34 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·34⟩ c4)

-- nat 0 BOX(3;124): 8 steps
lem-nat-0-BOX⟨3·124⟩ : WsL → ⟪ (Sw01 ∷ Bx3-124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-024 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·124⟩ c4 = derive (Sw01 ∷ Bx3-124 ∷ []) (Bx3-024 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-34 ∷ Toff312 ∷ CCZ123 ∷ Bx1-34 ∷ []) ∷
   rw⁻ 0 (q232 c4) ∷
   rw 1 (q233 c4) ∷
   rw 2 (q234 c4) ∷
   rw 3 (q233 c4) ∷
   rw⁻ 4 (q232 c4) ∷
   rw 5 (q234 c4) ∷
   re 0 6 (Bx3-024 ∷ []) ∷ []) Eq.refl

private
  q235 : WsL → Eqn
  q235 c4 = eqn (Sw01 ∷ Bx3-124 ∷ []) (Bx3-024 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·124⟩ c4)

-- nat 0 BOX(1;3024): 8 steps
lem-nat-0-BOX⟨1·3024⟩ : WsL → ⟪ (Sw01 ∷ Bx1-3024 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·3024⟩ c4 = derive (Sw01 ∷ Bx1-3024 ∷ []) (Bx0-3124 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-124 ∷ Toff103 ∷ CCZ013 ∷ Bx3-124 ∷ []) ∷
   rw⁻ 0 (q118 c4) ∷
   rw 1 (q119 c4) ∷
   rw 2 (q235 c4) ∷
   rw 3 (q119 c4) ∷
   rw⁻ 4 (q118 c4) ∷
   rw 5 (q235 c4) ∷
   re 0 6 (Bx0-3124 ∷ []) ∷ []) Eq.refl

private
  q236 : WsL → Eqn
  q236 c4 = eqn (Sw12 ∷ Bx2-34 ∷ []) (Bx2-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ))

-- nat 1 BOX(2;34): 2 steps
lem-nat-1-BOX⟨2·34⟩ : WsL → ⟪ (Sw12 ∷ Bx2-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-34 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·34⟩ c4 = derive (Sw12 ∷ Bx2-34 ∷ []) (Bx1-34 ∷ Sw12 ∷ [])
  (rw 0 (q236 c4) ∷
   re 0 1 (Bx1-34 ∷ []) ∷ []) Eq.refl

private
  q237 : WsL → Eqn
  q237 c4 = eqn (CCZ123 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ123 ∷ []) (wl0111 c4)
  q238 : WsL → Eqn
  q238 c4 = eqn (Sw12 ∷ Toff312 ∷ []) (Toff312 ∷ Sw12 ∷ []) (wl0143 c4)
  q239 : WsL → Eqn
  q239 c4 = eqn (Sw12 ∷ Bx2-34 ∷ []) (Bx1-34 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·34⟩ c4)

-- nat 1 BOX(3;214): 8 steps
lem-nat-1-BOX⟨3·214⟩ : WsL → ⟪ (Sw12 ∷ Bx3-214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-124 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·214⟩ c4 = derive (Sw12 ∷ Bx3-214 ∷ []) (Bx3-124 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) ∷
   rw⁻ 0 (q237 c4) ∷
   rw 1 (q238 c4) ∷
   rw 2 (q239 c4) ∷
   rw 3 (q238 c4) ∷
   rw⁻ 4 (q237 c4) ∷
   rw 5 (q239 c4) ∷
   re 0 6 (Bx3-124 ∷ []) ∷ []) Eq.refl

private
  q240 : WsL → Eqn
  q240 c4 = eqn (Sw12 ∷ Toff203 ∷ []) (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4)
  q241 : WsL → Eqn
  q241 c4 = eqn (Sw12 ∷ Bx3-214 ∷ []) (Bx3-124 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·214⟩ c4)

-- nat 1 BOX(2;3014): 8 steps
lem-nat-1-BOX⟨2·3014⟩ : WsL → ⟪ (Sw12 ∷ Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3024 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·3014⟩ c4 = derive (Sw12 ∷ Bx2-3014 ∷ []) (Bx1-3024 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-214 ∷ Toff203 ∷ CCZ023 ∷ Bx3-214 ∷ []) ∷
   rw 0 (q100 c4) ∷
   rw 1 (q240 c4) ∷
   rw 2 (q241 c4) ∷
   rw 3 (q240 c4) ∷
   rw 4 (q100 c4) ∷
   rw 5 (q241 c4) ∷
   re 0 6 (Bx1-3024 ∷ []) ∷ []) Eq.refl

private
  q242 : WsL → Eqn
  q242 c4 = eqn (CCZ123 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ023 ∷ []) (wl0103 c4)
  q243 : WsL → Eqn
  q243 c4 = eqn (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) (wl0116 c4)
  q244 : WsL → Eqn
  q244 c4 = eqn (Sw01 ∷ Bx2-34 ∷ []) (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑))

-- nat 0 BOX(3;204): 8 steps
lem-nat-0-BOX⟨3·204⟩ : WsL → ⟪ (Sw01 ∷ Bx3-204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-214 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·204⟩ c4 = derive (Sw01 ∷ Bx3-204 ∷ []) (Bx3-214 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) ∷
   rw⁻ 0 (q242 c4) ∷
   rw 1 (q243 c4) ∷
   rw 2 (q244 c4) ∷
   rw 3 (q243 c4) ∷
   rw⁻ 4 (q242 c4) ∷
   rw 5 (q244 c4) ∷
   re 0 6 (Bx3-214 ∷ []) ∷ []) Eq.refl

private
  q245 : WsL → Eqn
  q245 c4 = eqn (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) (wl0004 c4)
  q246 : WsL → Eqn
  q246 c4 = eqn (Sw01 ∷ Bx3-204 ∷ []) (Bx3-214 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·204⟩ c4)

-- nat 0 BOX(2;3104): 8 steps
lem-nat-0-BOX⟨2·3104⟩ : WsL → ⟪ (Sw01 ∷ Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·3104⟩ c4 = derive (Sw01 ∷ Bx2-3104 ∷ []) (Bx2-3014 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-204 ∷ Toff213 ∷ CCZ123 ∷ Bx3-204 ∷ []) ∷
   rw⁻ 0 (q232 c4) ∷
   rw 1 (q245 c4) ∷
   rw 2 (q246 c4) ∷
   rw 3 (q245 c4) ∷
   rw⁻ 4 (q232 c4) ∷
   rw 5 (q246 c4) ∷
   re 0 6 (Bx2-3014 ∷ []) ∷ []) Eq.refl

-- nat 0 BOX(2;04): 3 steps
lem-nat-0-BOX⟨2·04⟩ : WsL → ⟪ (Sw01 ∷ Bx2-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-14 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·04⟩ c4 = derive (Sw01 ∷ Bx2-04 ∷ []) (Bx2-14 ∷ Sw01 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   rw 0 (q126 c4) ∷
   re 0 1 (Bx2-14 ∷ []) ∷ []) Eq.refl

private
  q247 : WsL → Eqn
  q247 c4 = eqn (Sw01 ∷ Bx2-04 ∷ []) (Bx2-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·04⟩ c4)

-- nat 0 BOX(0;214): 8 steps
lem-nat-0-BOX⟨0·214⟩ : WsL → ⟪ (Sw01 ∷ Bx0-214 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-204 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·214⟩ c4 = derive (Sw01 ∷ Bx0-214 ∷ []) (Bx1-204 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) ∷
   rw⁻ 0 (q121 c4) ∷
   rw 1 (q122 c4) ∷
   rw 2 (q247 c4) ∷
   rw 3 (q122 c4) ∷
   rw⁻ 4 (q121 c4) ∷
   rw 5 (q247 c4) ∷
   re 0 6 (Bx1-204 ∷ []) ∷ []) Eq.refl

private
  q248 : WsL → Eqn
  q248 c4 = eqn (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) (wl0104 c4)
  q249 : WsL → Eqn
  q249 c4 = eqn (Sw01 ∷ Bx0-214 ∷ []) (Bx1-204 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·214⟩ c4)

-- nat 0 BOX(2;0314): 8 steps
lem-nat-0-BOX⟨2·0314⟩ : WsL → ⟪ (Sw01 ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·0314⟩ c4 = derive (Sw01 ∷ Bx2-0314 ∷ []) (Bx2-1304 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ []) ∷
   rw⁻ 0 (q242 c4) ∷
   rw 1 (q248 c4) ∷
   rw 2 (q249 c4) ∷
   rw 3 (q248 c4) ∷
   rw⁻ 4 (q242 c4) ∷
   rw 5 (q249 c4) ∷
   re 0 6 (Bx2-1304 ∷ []) ∷ []) Eq.refl

-- nat 0 BOX(2;14): 3 steps
lem-nat-0-BOX⟨2·14⟩ : WsL → ⟪ (Sw01 ∷ Bx2-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-04 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·14⟩ c4 = derive (Sw01 ∷ Bx2-14 ∷ []) (Bx2-04 ∷ Sw01 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   rw 0 (q116 c4) ∷
   re 0 1 (Bx2-04 ∷ []) ∷ []) Eq.refl

private
  q250 : WsL → Eqn
  q250 c4 = eqn (Sw01 ∷ Bx2-14 ∷ []) (Bx2-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·14⟩ c4)

-- nat 0 BOX(1;204): 8 steps
lem-nat-0-BOX⟨1·204⟩ : WsL → ⟪ (Sw01 ∷ Bx1-204 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-214 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·204⟩ c4 = derive (Sw01 ∷ Bx1-204 ∷ []) (Bx0-214 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) ∷
   rw⁻ 0 (q121 c4) ∷
   rw 1 (q179 c4) ∷
   rw 2 (q250 c4) ∷
   rw 3 (q179 c4) ∷
   rw⁻ 4 (q121 c4) ∷
   rw 5 (q250 c4) ∷
   re 0 6 (Bx0-214 ∷ []) ∷ []) Eq.refl

private
  q251 : WsL → Eqn
  q251 c4 = eqn (Sw01 ∷ Bx1-204 ∷ []) (Bx0-214 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·204⟩ c4)

-- nat 0 BOX(2;1304): 8 steps
lem-nat-0-BOX⟨2·1304⟩ : WsL → ⟪ (Sw01 ∷ Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·1304⟩ c4 = derive (Sw01 ∷ Bx2-1304 ∷ []) (Bx2-0314 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-204 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ []) ∷
   rw⁻ 0 (q232 c4) ∷
   rw 1 (q245 c4) ∷
   rw 2 (q251 c4) ∷
   rw 3 (q245 c4) ∷
   rw⁻ 4 (q232 c4) ∷
   rw 5 (q251 c4) ∷
   re 0 6 (Bx2-0314 ∷ []) ∷ []) Eq.refl

private
  q252 : WsL → Eqn
  q252 c4 = eqn (Sw01 ∷ Toff023 ∷ []) (Toff123 ∷ Sw01 ∷ []) (wl0108 c4)

-- nat 0 BOX(0;234): 8 steps
lem-nat-0-BOX⟨0·234⟩ : WsL → ⟪ (Sw01 ∷ Bx0-234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-234 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·234⟩ c4 = derive (Sw01 ∷ Bx0-234 ∷ []) (Bx1-234 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) ∷
   rw⁻ 0 (q242 c4) ∷
   rw 1 (q252 c4) ∷
   rw 2 (q247 c4) ∷
   rw 3 (q252 c4) ∷
   rw⁻ 4 (q242 c4) ∷
   rw 5 (q247 c4) ∷
   re 0 6 (Bx1-234 ∷ []) ∷ []) Eq.refl

private
  q253 : WsL → Eqn
  q253 c4 = eqn (Sw01 ∷ Toff201 ∷ []) (Toff201 ∷ Sw01 ∷ []) (wl0107 c4)
  q254 : WsL → Eqn
  q254 c4 = eqn (Sw01 ∷ Bx0-234 ∷ []) (Bx1-234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·234⟩ c4)

-- nat 0 BOX(2;0134): 8 steps
lem-nat-0-BOX⟨2·0134⟩ : WsL → ⟪ (Sw01 ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·0134⟩ c4 = derive (Sw01 ∷ Bx2-0134 ∷ []) (Bx2-1034 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ []) ∷
   rw⁻ 0 (q121 c4) ∷
   rw 1 (q253 c4) ∷
   rw 2 (q254 c4) ∷
   rw 3 (q253 c4) ∷
   rw⁻ 4 (q121 c4) ∷
   rw 5 (q254 c4) ∷
   re 0 6 (Bx2-1034 ∷ []) ∷ []) Eq.refl

-- nat 0 BOX(1;234): 8 steps
lem-nat-0-BOX⟨1·234⟩ : WsL → ⟪ (Sw01 ∷ Bx1-234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-234 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·234⟩ c4 = derive (Sw01 ∷ Bx1-234 ∷ []) (Bx0-234 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) ∷
   rw⁻ 0 (q232 c4) ∷
   rw 1 (q174 c4) ∷
   rw 2 (q250 c4) ∷
   rw 3 (q174 c4) ∷
   rw⁻ 4 (q232 c4) ∷
   rw 5 (q250 c4) ∷
   re 0 6 (Bx0-234 ∷ []) ∷ []) Eq.refl

private
  q255 : WsL → Eqn
  q255 c4 = eqn (Sw01 ∷ Bx1-234 ∷ []) (Bx0-234 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·234⟩ c4)

-- nat 0 BOX(2;1034): 8 steps
lem-nat-0-BOX⟨2·1034⟩ : WsL → ⟪ (Sw01 ∷ Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·1034⟩ c4 = derive (Sw01 ∷ Bx2-1034 ∷ []) (Bx2-0134 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ []) ∷
   rw⁻ 0 (q121 c4) ∷
   rw 1 (q253 c4) ∷
   rw 2 (q255 c4) ∷
   rw 3 (q253 c4) ∷
   rw⁻ 4 (q121 c4) ∷
   rw 5 (q255 c4) ∷
   re 0 6 (Bx2-0134 ∷ []) ∷ []) Eq.refl

private
  q256 : WsL → Eqn
  q256 c4 = eqn (Sw01 ∷ Bx0-34 ∷ []) (Bx0-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑))

-- nat 0 BOX(0;34): 2 steps
lem-nat-0-BOX⟨0·34⟩ : WsL → ⟪ (Sw01 ∷ Bx0-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-34 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·34⟩ c4 = derive (Sw01 ∷ Bx0-34 ∷ []) (Bx1-34 ∷ Sw01 ∷ [])
  (rw 0 (q256 c4) ∷
   re 0 1 (Bx1-34 ∷ []) ∷ []) Eq.refl

private
  q257 : WsL → Eqn
  q257 c4 = eqn (Sw01 ∷ Bx0-34 ∷ []) (Bx1-34 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·34⟩ c4)

-- nat 0 BOX(3;024): 8 steps
lem-nat-0-BOX⟨3·024⟩ : WsL → ⟪ (Sw01 ∷ Bx3-024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-124 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·024⟩ c4 = derive (Sw01 ∷ Bx3-024 ∷ []) (Bx3-124 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) ∷
   rw⁻ 0 (q242 c4) ∷
   rw 1 (q243 c4) ∷
   rw 2 (q257 c4) ∷
   rw 3 (q243 c4) ∷
   rw⁻ 4 (q242 c4) ∷
   rw 5 (q257 c4) ∷
   re 0 6 (Bx3-124 ∷ []) ∷ []) Eq.refl

private
  q258 : WsL → Eqn
  q258 c4 = eqn (Sw01 ∷ Bx3-024 ∷ []) (Bx3-124 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·024⟩ c4)

-- nat 0 BOX(0;3124): 8 steps
lem-nat-0-BOX⟨0·3124⟩ : WsL → ⟪ (Sw01 ∷ Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3024 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·3124⟩ c4 = derive (Sw01 ∷ Bx0-3124 ∷ []) (Bx1-3024 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ []) ∷
   rw⁻ 0 (q118 c4) ∷
   rw 1 (q177 c4) ∷
   rw 2 (q258 c4) ∷
   rw 3 (q177 c4) ∷
   rw⁻ 4 (q118 c4) ∷
   rw 5 (q258 c4) ∷
   re 0 6 (Bx1-3024 ∷ []) ∷ []) Eq.refl

private
  q259 : WsL → Eqn
  q259 c4 = eqn (Sw12 ∷ Bx1-34 ∷ []) (Bx1-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ))

-- nat 1 BOX(1;34): 2 steps
lem-nat-1-BOX⟨1·34⟩ : WsL → ⟪ (Sw12 ∷ Bx1-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-34 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·34⟩ c4 = derive (Sw12 ∷ Bx1-34 ∷ []) (Bx2-34 ∷ Sw12 ∷ [])
  (rw 0 (q259 c4) ∷
   re 0 1 (Bx2-34 ∷ []) ∷ []) Eq.refl

private
  q260 : WsL → Eqn
  q260 c4 = eqn (Sw12 ∷ Bx1-34 ∷ []) (Bx2-34 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·34⟩ c4)

-- nat 1 BOX(3;124): 8 steps
lem-nat-1-BOX⟨3·124⟩ : WsL → ⟪ (Sw12 ∷ Bx3-124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-214 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·124⟩ c4 = derive (Sw12 ∷ Bx3-124 ∷ []) (Bx3-214 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-34 ∷ Toff312 ∷ CCZ123 ∷ Bx1-34 ∷ []) ∷
   rw⁻ 0 (q237 c4) ∷
   rw 1 (q238 c4) ∷
   rw 2 (q260 c4) ∷
   rw 3 (q238 c4) ∷
   rw⁻ 4 (q237 c4) ∷
   rw 5 (q260 c4) ∷
   re 0 6 (Bx3-214 ∷ []) ∷ []) Eq.refl
