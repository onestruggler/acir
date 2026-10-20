{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R007 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0011 ; wl0012 ; wl0013 ; wl0015 ; wl0016 ; wl0017 ; wl0018 ; wl0019 ; wl0020 ; wl0021 ; wl0022 ; wl0023 ; wl0027 ; wl0028 ; wl0030 ; wl0031 ; wl0032 ; wl0033 ; wl0034 ; wl0035 ; wl0036 ; wl0048 ; wl0061 ; wl0063 ; wl0064 ; wl0065 ; wl0073 ; wl0074 ; wl0078 ; wl0087 ; wl0088 ; wl0089 ; wl0091 ; wl0092 ; wl0093 ; wl0095 ; wl0096 ; wl0097 ; wl0099 ; wl0100 ; wl0101 ; wl0103 ; wl0104 ; wl0105 ; wl0111 ; wl0112 ; wl0119 ; wl0120 ; wl0121 ; wl0122 ; wl0123 ; wl0124 ; wl0125 ; wl0126 ; wl0127 ; wl0128 ; wl0129 ; wl0130 ; wl0131 ; wl0132 ; wl0133 ; wl0134 ; wl0135 ; wl0136)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-2-BOX⟨0·1234⟩ ; lem-nat-2-BOX⟨0·1324⟩ ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF013 ; lem-nat-2-TOFF103 ; lem-nat-3-BOX⟨0·1423⟩ ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ013 ; lem-nat-2-TOFF304 ; lem-nat-3-BOX⟨0·1324⟩ ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023 ; lem-nat-3-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ014 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF104 ; lem-nat-0-TOFF412 ; lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-CZ04 ; lem-nat-0-TOFF204 ; lem-nat-0-TOFF214 ; lem-nat-0-TOFF413 ; lem-nat-1-TOFF013 ; lem-nat-1-TOFF304 ; lem-nat-2-TOFF104 ; lem-nat-3-TOFF023)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-BOX⟨0·1423⟩ ; lem-nat-0-BOX⟨1·0423⟩ ; lem-nat-0-TOFF024 ; lem-nat-1-BOX⟨1·0423⟩ ; lem-nat-1-BOX⟨2·0413⟩ ; lem-nat-2-CCZ014 ; lem-nat-2-CZ02 ; lem-nat-2-TOFF402 ; lem-nat-3-TOFF103)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-BOX⟨0·2341⟩ ; lem-nat-1-CS02 ; lem-nat-1-CZ01 ; lem-nat-1-CZ02 ; lem-nat-2-BOX⟨0·12⟩ ; lem-nat-3-CS13 ; lem-nat-3-CS14 ; lem-nat-3-CSd13 ; lem-nat-3-CSd14)

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
  q9 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl0021 c4)
  q10 : WsL → Eqn
  q10 c4 = eqn (CS14⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS14⁻ ∷ []) (wl0033 c4)
  q11 : WsL → Eqn
  q11 c4 = eqn (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4)
  q12 : WsL → Eqn
  q12 c4 = eqn (Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap))
  q13 : WsL → Eqn
  q13 c4 = eqn (CS01 ∷ Sw34 ∷ []) (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑))

-- nat 2 TOFF014: 68 steps
lem-nat-2-TOFF014 : WsL → ⟪ (Sw23 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF014 c4 = derive (Sw23 ∷ Toff014 ∷ []) (Toff014 ∷ Sw23 ∷ [])
  (re 1 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   re 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
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
   rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q11 c4) ∷
   rw⁻ 7 (q12 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw⁻ 9 (q12 c4) ∷
   rw⁻ 10 (q11 c4) ∷
   re 5 7 (CS04 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   rw⁻ 1 (q5 c4) ∷
   re 3 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 2 (q6 c4) ∷
   rw⁻ 3 (q7 c4) ∷
   re 5 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 8 (q8 c4) ∷
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
   re 0 3 (Toff014 ∷ []) ∷ []) Eq.refl

-- nat 2 TOFF403: 2 steps
lem-nat-2-TOFF403 : WsL → ⟪ (Sw23 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF403 c4 = derive (Sw23 ∷ Toff403 ∷ []) (Toff402 ∷ Sw23 ∷ [])
  (re 1 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) ∷
   rw 0 (q2 c4) ∷ []) Eq.refl

private
  q14 : WsL → Eqn
  q14 c4 = eqn (CZ34 ∷ Sw23 ∷ []) (Sw23 ∷ CZ24 ∷ []) (wl0028 c4)

-- nat 2 BOX(0;42): 3 steps
lem-nat-2-BOX⟨0·42⟩ : WsL → ⟪ (Sw23 ∷ Bx0-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-43 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·42⟩ c4 = derive (Sw23 ∷ Bx0-42 ∷ []) (Bx0-43 ∷ Sw23 ∷ [])
  (re 1 1 (CZ24 ∷ []) ∷
   rw⁻ 0 (q14 c4) ∷
   re 0 1 (Bx0-43 ∷ []) ∷ []) Eq.refl

private
  q15 : WsL → Eqn
  q15 c4 = eqn (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4)
  q16 : WsL → Eqn
  q16 c4 = eqn (Sw23 ∷ Toff403 ∷ []) (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4)
  q17 : WsL → Eqn
  q17 c4 = eqn (Sw23 ∷ Bx0-42 ∷ []) (Bx0-43 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·42⟩ c4)

-- nat 2 BOX(4;032): 8 steps
lem-nat-2-BOX⟨4·032⟩ : WsL → ⟪ (Sw23 ∷ Bx4-032 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-023 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·032⟩ c4 = derive (Sw23 ∷ Bx4-032 ∷ []) (Bx4-023 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) ∷
   rw 0 (q15 c4) ∷
   rw 1 (q16 c4) ∷
   rw 2 (q17 c4) ∷
   rw 3 (q16 c4) ∷
   rw 4 (q15 c4) ∷
   rw 5 (q17 c4) ∷
   re 0 6 (Bx4-023 ∷ []) ∷ []) Eq.refl

private
  q18 : WsL → Eqn
  q18 c4 = eqn (Sw23 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4)
  q19 : WsL → Eqn
  q19 c4 = eqn (Sw23 ∷ Toff014 ∷ []) (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4)
  q20 : WsL → Eqn
  q20 c4 = eqn (Sw23 ∷ Bx4-032 ∷ []) (Bx4-023 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·032⟩ c4)

-- nat 2 BOX(0;4132): 8 steps
lem-nat-2-BOX⟨0·4132⟩ : WsL → ⟪ (Sw23 ∷ Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·4132⟩ c4 = derive (Sw23 ∷ Bx0-4132 ∷ []) (Bx0-4123 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-032 ∷ Toff014 ∷ CCZ014 ∷ Bx4-032 ∷ []) ∷
   rw 0 (q18 c4) ∷
   rw 1 (q19 c4) ∷
   rw 2 (q20 c4) ∷
   rw 3 (q19 c4) ∷
   rw 4 (q18 c4) ∷
   rw 5 (q20 c4) ∷
   re 0 6 (Bx0-4123 ∷ []) ∷ []) Eq.refl

private
  q21 : WsL → Eqn
  q21 c4 = eqn (CZ24 ∷ Sw23 ∷ []) (Sw23 ∷ CZ34 ∷ []) (wl0027 c4)

-- nat 2 BOX(0;43): 3 steps
lem-nat-2-BOX⟨0·43⟩ : WsL → ⟪ (Sw23 ∷ Bx0-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-42 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·43⟩ c4 = derive (Sw23 ∷ Bx0-43 ∷ []) (Bx0-42 ∷ Sw23 ∷ [])
  (re 1 1 (CZ34 ∷ []) ∷
   rw⁻ 0 (q21 c4) ∷
   re 0 1 (Bx0-42 ∷ []) ∷ []) Eq.refl

private
  q22 : WsL → Eqn
  q22 c4 = eqn (Sw23 ∷ CCZ024 ∷ []) (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4)
  q23 : WsL → Eqn
  q23 c4 = eqn (Sw23 ∷ Toff402 ∷ []) (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4)
  q24 : WsL → Eqn
  q24 c4 = eqn (Sw23 ∷ Bx0-43 ∷ []) (Bx0-42 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·43⟩ c4)

-- nat 2 BOX(4;023): 8 steps
lem-nat-2-BOX⟨4·023⟩ : WsL → ⟪ (Sw23 ∷ Bx4-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-032 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·023⟩ c4 = derive (Sw23 ∷ Bx4-023 ∷ []) (Bx4-032 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) ∷
   rw 0 (q22 c4) ∷
   rw 1 (q23 c4) ∷
   rw 2 (q24 c4) ∷
   rw 3 (q23 c4) ∷
   rw 4 (q22 c4) ∷
   rw 5 (q24 c4) ∷
   re 0 6 (Bx4-032 ∷ []) ∷ []) Eq.refl

private
  q25 : WsL → Eqn
  q25 c4 = eqn (Sw23 ∷ Bx4-023 ∷ []) (Bx4-032 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·023⟩ c4)

-- nat 2 BOX(0;4123): 8 steps
lem-nat-2-BOX⟨0·4123⟩ : WsL → ⟪ (Sw23 ∷ Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·4123⟩ c4 = derive (Sw23 ∷ Bx0-4123 ∷ []) (Bx0-4132 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) ∷
   rw 0 (q18 c4) ∷
   rw 1 (q19 c4) ∷
   rw 2 (q25 c4) ∷
   rw 3 (q19 c4) ∷
   rw 4 (q18 c4) ∷
   rw 5 (q25 c4) ∷
   re 0 6 (Bx0-4132 ∷ []) ∷ []) Eq.refl

private
  q26 : WsL → Eqn
  q26 c4 = eqn (Sw01 ∷ Bx1-42 ∷ []) (Bx1-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑))

-- nat 0 BOX(1;42): 2 steps
lem-nat-0-BOX⟨1·42⟩ : WsL → ⟪ (Sw01 ∷ Bx1-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-42 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·42⟩ c4 = derive (Sw01 ∷ Bx1-42 ∷ []) (Bx0-42 ∷ Sw01 ∷ [])
  (rw 0 (q26 c4) ∷
   re 0 1 (Bx0-42 ∷ []) ∷ []) Eq.refl

private
  q27 : WsL → Eqn
  q27 c4 = eqn (Sw01 ∷ CCZ134 ∷ []) (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4)
  q28 : WsL → Eqn
  q28 c4 = eqn (Sw01 ∷ Toff413 ∷ []) (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4)
  q29 : WsL → Eqn
  q29 c4 = eqn (Sw01 ∷ Bx1-42 ∷ []) (Bx0-42 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·42⟩ c4)

-- nat 0 BOX(4;132): 8 steps
lem-nat-0-BOX⟨4·132⟩ : WsL → ⟪ (Sw01 ∷ Bx4-132 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-032 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·132⟩ c4 = derive (Sw01 ∷ Bx4-132 ∷ []) (Bx4-032 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff413 ∷ Bx1-42 ∷ Toff413 ∷ CCZ134 ∷ Bx1-42 ∷ []) ∷
   rw 0 (q27 c4) ∷
   rw 1 (q28 c4) ∷
   rw 2 (q29 c4) ∷
   rw 3 (q28 c4) ∷
   rw 4 (q27 c4) ∷
   rw 5 (q29 c4) ∷
   re 0 6 (Bx4-032 ∷ []) ∷ []) Eq.refl

private
  q30 : WsL → Eqn
  q30 c4 = eqn (Sw01 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4)
  q31 : WsL → Eqn
  q31 c4 = eqn (Sw01 ∷ Toff104 ∷ []) (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4)
  q32 : WsL → Eqn
  q32 c4 = eqn (Sw01 ∷ Bx4-132 ∷ []) (Bx4-032 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·132⟩ c4)

-- nat 0 BOX(1;4032): 8 steps
lem-nat-0-BOX⟨1·4032⟩ : WsL → ⟪ (Sw01 ∷ Bx1-4032 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·4032⟩ c4 = derive (Sw01 ∷ Bx1-4032 ∷ []) (Bx0-4132 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff104 ∷ Bx4-132 ∷ Toff104 ∷ CCZ014 ∷ Bx4-132 ∷ []) ∷
   rw 0 (q30 c4) ∷
   rw 1 (q31 c4) ∷
   rw 2 (q32 c4) ∷
   rw 3 (q31 c4) ∷
   rw 4 (q30 c4) ∷
   rw 5 (q32 c4) ∷
   re 0 6 (Bx0-4132 ∷ []) ∷ []) Eq.refl

private
  q33 : WsL → Eqn
  q33 c4 = eqn (CZ24 ∷ Sw12 ∷ []) (Sw12 ∷ CZ14 ∷ []) (wl0089 c4)

-- nat 1 BOX(2;41): 3 steps
lem-nat-1-BOX⟨2·41⟩ : WsL → ⟪ (Sw12 ∷ Bx2-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-42 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·41⟩ c4 = derive (Sw12 ∷ Bx2-41 ∷ []) (Bx1-42 ∷ Sw12 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   rw⁻ 0 (q33 c4) ∷
   re 0 1 (Bx1-42 ∷ []) ∷ []) Eq.refl

private
  q34 : WsL → Eqn
  q34 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl0034 c4)
  q35 : WsL → Eqn
  q35 c4 = eqn (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) (wl0091 c4)
  q36 : WsL → Eqn
  q36 c4 = eqn (Sw12 ∷ Bx2-41 ∷ []) (Bx1-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·41⟩ c4)

-- nat 1 BOX(4;231): 8 steps
lem-nat-1-BOX⟨4·231⟩ : WsL → ⟪ (Sw12 ∷ Bx4-231 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-132 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·231⟩ c4 = derive (Sw12 ∷ Bx4-231 ∷ []) (Bx4-132 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) ∷
   rw⁻ 0 (q34 c4) ∷
   rw 1 (q35 c4) ∷
   rw 2 (q36 c4) ∷
   rw 3 (q35 c4) ∷
   rw⁻ 4 (q34 c4) ∷
   rw 5 (q36 c4) ∷
   re 0 6 (Bx4-132 ∷ []) ∷ []) Eq.refl

private
  q37 : WsL → Eqn
  q37 c4 = eqn (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4)
  q38 : WsL → Eqn
  q38 c4 = eqn (Sw12 ∷ Toff204 ∷ []) (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4)
  q39 : WsL → Eqn
  q39 c4 = eqn (Sw12 ∷ Bx4-231 ∷ []) (Bx4-132 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·231⟩ c4)

-- nat 1 BOX(2;4031): 8 steps
lem-nat-1-BOX⟨2·4031⟩ : WsL → ⟪ (Sw12 ∷ Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4032 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·4031⟩ c4 = derive (Sw12 ∷ Bx2-4031 ∷ []) (Bx1-4032 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-231 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ []) ∷
   rw 0 (q37 c4) ∷
   rw 1 (q38 c4) ∷
   rw 2 (q39 c4) ∷
   rw 3 (q38 c4) ∷
   rw 4 (q37 c4) ∷
   rw 5 (q39 c4) ∷
   re 0 6 (Bx1-4032 ∷ []) ∷ []) Eq.refl

private
  q40 : WsL → Eqn
  q40 c4 = eqn (Sw01 ∷ CZ04 ∷ []) (CZ14 ∷ Sw01 ∷ []) (lem-nat-0-CZ04 c4)

-- nat 0 BOX(2;40): 3 steps
lem-nat-0-BOX⟨2·40⟩ : WsL → ⟪ (Sw01 ∷ Bx2-40 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-41 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·40⟩ c4 = derive (Sw01 ∷ Bx2-40 ∷ []) (Bx2-41 ∷ Sw01 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   rw 0 (q40 c4) ∷
   re 0 1 (Bx2-41 ∷ []) ∷ []) Eq.refl

private
  q41 : WsL → Eqn
  q41 c4 = eqn (Sw01 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ))
  q42 : WsL → Eqn
  q42 c4 = eqn (Sw01 ∷ Toff423 ∷ []) (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ))
  q43 : WsL → Eqn
  q43 c4 = eqn (Sw01 ∷ Bx2-40 ∷ []) (Bx2-41 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·40⟩ c4)

-- nat 0 BOX(4;230): 8 steps
lem-nat-0-BOX⟨4·230⟩ : WsL → ⟪ (Sw01 ∷ Bx4-230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-231 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·230⟩ c4 = derive (Sw01 ∷ Bx4-230 ∷ []) (Bx4-231 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff423 ∷ Bx2-40 ∷ Toff423 ∷ CCZ234 ∷ Bx2-40 ∷ []) ∷
   rw 0 (q41 c4) ∷
   rw 1 (q42 c4) ∷
   rw 2 (q43 c4) ∷
   rw 3 (q42 c4) ∷
   rw 4 (q41 c4) ∷
   rw 5 (q43 c4) ∷
   re 0 6 (Bx4-231 ∷ []) ∷ []) Eq.refl

private
  q44 : WsL → Eqn
  q44 c4 = eqn (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4)
  q45 : WsL → Eqn
  q45 c4 = eqn (Sw01 ∷ Toff214 ∷ []) (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4)
  q46 : WsL → Eqn
  q46 c4 = eqn (Sw01 ∷ Bx4-230 ∷ []) (Bx4-231 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·230⟩ c4)

-- nat 0 BOX(2;4130): 8 steps
lem-nat-0-BOX⟨2·4130⟩ : WsL → ⟪ (Sw01 ∷ Bx2-4130 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·4130⟩ c4 = derive (Sw01 ∷ Bx2-4130 ∷ []) (Bx2-4031 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff214 ∷ Bx4-230 ∷ Toff214 ∷ CCZ124 ∷ Bx4-230 ∷ []) ∷
   rw 0 (q44 c4) ∷
   rw 1 (q45 c4) ∷
   rw 2 (q46 c4) ∷
   rw 3 (q45 c4) ∷
   rw 4 (q44 c4) ∷
   rw 5 (q46 c4) ∷
   re 0 6 (Bx2-4031 ∷ []) ∷ []) Eq.refl

private
  q47 : WsL → Eqn
  q47 c4 = eqn (Sw01 ∷ Toff412 ∷ []) (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4)
  q48 : WsL → Eqn
  q48 c4 = eqn (Sw01 ∷ Bx2-43 ∷ []) (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑))

-- nat 0 BOX(4;213): 8 steps
lem-nat-0-BOX⟨4·213⟩ : WsL → ⟪ (Sw01 ∷ Bx4-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-203 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·213⟩ c4 = derive (Sw01 ∷ Bx4-213 ∷ []) (Bx4-203 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) ∷
   rw 0 (q44 c4) ∷
   rw 1 (q47 c4) ∷
   rw 2 (q48 c4) ∷
   rw 3 (q47 c4) ∷
   rw 4 (q44 c4) ∷
   rw 5 (q48 c4) ∷
   re 0 6 (Bx4-203 ∷ []) ∷ []) Eq.refl

private
  q49 : WsL → Eqn
  q49 c4 = eqn (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4)
  q50 : WsL → Eqn
  q50 c4 = eqn (Sw01 ∷ Toff204 ∷ []) (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4)
  q51 : WsL → Eqn
  q51 c4 = eqn (Sw01 ∷ Bx4-213 ∷ []) (Bx4-203 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·213⟩ c4)

-- nat 0 BOX(2;4013): 8 steps
lem-nat-0-BOX⟨2·4013⟩ : WsL → ⟪ (Sw01 ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·4013⟩ c4 = derive (Sw01 ∷ Bx2-4013 ∷ []) (Bx2-4103 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ []) ∷
   rw 0 (q49 c4) ∷
   rw 1 (q50 c4) ∷
   rw 2 (q51 c4) ∷
   rw 3 (q50 c4) ∷
   rw 4 (q49 c4) ∷
   rw 5 (q51 c4) ∷
   re 0 6 (Bx2-4103 ∷ []) ∷ []) Eq.refl

-- nat 2 SBOX(0;1;4;2): 3 steps
lem-nat-2-SBOX⟨0·1·4·2⟩ : WsL → ⟪ (Sw23 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-4-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·1·4·2⟩ c4 = derive (Sw23 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-4-3 ∷ Sw23 ∷ [])
  (re 1 1 (CS14 ∷ []) ∷
   rw⁻ 0 (q9 c4) ∷
   re 0 1 (Sb0-1-4-3 ∷ []) ∷ []) Eq.refl

-- nat 2 SBOXd(0;1;4;2): 3 steps
lem-nat-2-SBOXd⟨0·1·4·2⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·1·4·2⟩ c4 = derive (Sw23 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-4-3 ∷ Sw23 ∷ [])
  (re 1 1 (CS14⁻ ∷ []) ∷
   rw⁻ 0 (q10 c4) ∷
   re 0 1 (Sb⁻0-1-4-3 ∷ []) ∷ []) Eq.refl

private
  q52 : WsL → Eqn
  q52 c4 = eqn (Sw23 ∷ Bx0-1324 ∷ []) (Bx0-1234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1324⟩ c4)
  q53 : WsL → Eqn
  q53 c4 = eqn (Sw23 ∷ Toff423 ∷ []) (Toff423 ∷ Sw23 ∷ []) (wl0087 c4)
  q54 : WsL → Eqn
  q54 c4 = eqn (Sw23 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·2⟩ c4)
  q55 : WsL → Eqn
  q55 c4 = eqn (Sw23 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-4-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·2⟩ c4)

-- nat 2 SBOX(0;1;32;4): 7 steps
lem-nat-2-SBOX⟨0·1·32·4⟩ : WsL → ⟪ (Sw23 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-23-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·1·32·4⟩ c4 = derive (Sw23 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-23-4 ∷ Sw23 ∷ [])
  (re 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) ∷
   rw 0 (q52 c4) ∷
   rw 1 (q53 c4) ∷
   rw 2 (q54 c4) ∷
   rw 3 (q53 c4) ∷
   rw 4 (q55 c4) ∷
   re 0 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

-- nat 2 SBOX(0;1;4;3): 3 steps
lem-nat-2-SBOX⟨0·1·4·3⟩ : WsL → ⟪ (Sw23 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-4-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·1·4·3⟩ c4 = derive (Sw23 ∷ Sb0-1-4-3 ∷ []) (Sb0-1-4-2 ∷ Sw23 ∷ [])
  (re 1 1 (CS14 ∷ []) ∷
   rw⁻ 0 (q9 c4) ∷
   re 0 1 (Sb0-1-4-2 ∷ []) ∷ []) Eq.refl

-- nat 2 SBOXd(0;1;4;3): 3 steps
lem-nat-2-SBOXd⟨0·1·4·3⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·1·4·3⟩ c4 = derive (Sw23 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-1-4-2 ∷ Sw23 ∷ [])
  (re 1 1 (CS14⁻ ∷ []) ∷
   rw⁻ 0 (q10 c4) ∷
   re 0 1 (Sb⁻0-1-4-2 ∷ []) ∷ []) Eq.refl

private
  q56 : WsL → Eqn
  q56 c4 = eqn (Sw23 ∷ Bx0-1234 ∷ []) (Bx0-1324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1234⟩ c4)
  q57 : WsL → Eqn
  q57 c4 = eqn (Sw23 ∷ Sb0-1-4-3 ∷ []) (Sb0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·4·3⟩ c4)
  q58 : WsL → Eqn
  q58 c4 = eqn (Sw23 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-1-4-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·4·3⟩ c4)

-- nat 2 SBOX(0;1;23;4): 7 steps
lem-nat-2-SBOX⟨0·1·23·4⟩ : WsL → ⟪ (Sw23 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-32-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·1·23·4⟩ c4 = derive (Sw23 ∷ Sb0-1-23-4 ∷ []) (Sb0-1-32-4 ∷ Sw23 ∷ [])
  (re 1 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   rw 0 (q56 c4) ∷
   rw 1 (q53 c4) ∷
   rw 2 (q57 c4) ∷
   rw 3 (q53 c4) ∷
   rw 4 (q58 c4) ∷
   re 0 5 (Sb0-1-32-4 ∷ []) ∷ []) Eq.refl

private
  q59 : WsL → Eqn
  q59 c4 = eqn (Sw34 ∷ CS13 ∷ []) (CS14 ∷ Sw34 ∷ []) (lem-nat-3-CS13 c4)

-- nat 3 SBOX(0;1;3;2): 3 steps
lem-nat-3-SBOX⟨0·1·3·2⟩ : WsL → ⟪ (Sw34 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-4-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·1·3·2⟩ c4 = derive (Sw34 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-4-2 ∷ Sw34 ∷ [])
  (re 1 1 (CS13 ∷ []) ∷
   rw 0 (q59 c4) ∷
   re 0 1 (Sb0-1-4-2 ∷ []) ∷ []) Eq.refl

private
  q60 : WsL → Eqn
  q60 c4 = eqn (Sw34 ∷ CS13⁻ ∷ []) (CS14⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd13 c4)

-- nat 3 SBOXd(0;1;3;2): 3 steps
lem-nat-3-SBOXd⟨0·1·3·2⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·1·3·2⟩ c4 = derive (Sw34 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-4-2 ∷ Sw34 ∷ [])
  (re 1 1 (CS13⁻ ∷ []) ∷
   rw 0 (q60 c4) ∷
   re 0 1 (Sb⁻0-1-4-2 ∷ []) ∷ []) Eq.refl

private
  q61 : WsL → Eqn
  q61 c4 = eqn (Sw34 ∷ Bx0-1423 ∷ []) (Bx0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1423⟩ c4)
  q62 : WsL → Eqn
  q62 c4 = eqn (Sw34 ∷ Toff324 ∷ []) (Toff423 ∷ Sw34 ∷ []) (wl0119 c4)
  q63 : WsL → Eqn
  q63 c4 = eqn (Sw34 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ c4)
  q64 : WsL → Eqn
  q64 c4 = eqn (Sw34 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ c4)

-- nat 3 SBOX(0;1;42;3): 7 steps
lem-nat-3-SBOX⟨0·1·42·3⟩ : WsL → ⟪ (Sw34 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-32-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·1·42·3⟩ c4 = derive (Sw34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-32-4 ∷ Sw34 ∷ [])
  (re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw 0 (q61 c4) ∷
   rw 1 (q62 c4) ∷
   rw 2 (q63 c4) ∷
   rw 3 (q62 c4) ∷
   rw 4 (q64 c4) ∷
   re 0 5 (Sb0-1-32-4 ∷ []) ∷ []) Eq.refl

private
  q65 : WsL → Eqn
  q65 c4 = eqn (Sw34 ∷ CS14 ∷ []) (CS13 ∷ Sw34 ∷ []) (lem-nat-3-CS14 c4)

-- nat 3 SBOX(0;1;4;2): 3 steps
lem-nat-3-SBOX⟨0·1·4·2⟩ : WsL → ⟪ (Sw34 ∷ Sb0-1-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·1·4·2⟩ c4 = derive (Sw34 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-3-2 ∷ Sw34 ∷ [])
  (re 1 1 (CS14 ∷ []) ∷
   rw 0 (q65 c4) ∷
   re 0 1 (Sb0-1-3-2 ∷ []) ∷ []) Eq.refl

private
  q66 : WsL → Eqn
  q66 c4 = eqn (Sw34 ∷ CS14⁻ ∷ []) (CS13⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd14 c4)

-- nat 3 SBOXd(0;1;4;2): 3 steps
lem-nat-3-SBOXd⟨0·1·4·2⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻0-1-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·1·4·2⟩ c4 = derive (Sw34 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sw34 ∷ [])
  (re 1 1 (CS14⁻ ∷ []) ∷
   rw 0 (q66 c4) ∷
   re 0 1 (Sb⁻0-1-3-2 ∷ []) ∷ []) Eq.refl

private
  q67 : WsL → Eqn
  q67 c4 = eqn (Sw34 ∷ Bx0-1324 ∷ []) (Bx0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·1324⟩ c4)
  q68 : WsL → Eqn
  q68 c4 = eqn (Sw34 ∷ Toff423 ∷ []) (Toff324 ∷ Sw34 ∷ []) (wl0120 c4)
  q69 : WsL → Eqn
  q69 c4 = eqn (Sw34 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ c4)
  q70 : WsL → Eqn
  q70 c4 = eqn (Sw34 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ c4)

-- nat 3 SBOX(0;1;32;4): 7 steps
lem-nat-3-SBOX⟨0·1·32·4⟩ : WsL → ⟪ (Sw34 ∷ Sb0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·1·32·4⟩ c4 = derive (Sw34 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-42-3 ∷ Sw34 ∷ [])
  (re 1 1 (Bx0-1324 ∷ Toff423 ∷ Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ []) ∷
   rw 0 (q67 c4) ∷
   rw 1 (q68 c4) ∷
   rw 2 (q69 c4) ∷
   rw 3 (q68 c4) ∷
   rw 4 (q70 c4) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q71 : WsL → Eqn
  q71 c4 = eqn (CS13 ∷ Sw01 ∷ []) (Sw01 ∷ CS03 ∷ []) (wl0061 c4)

-- nat 0 SBOX(1;0;3;2): 3 steps
lem-nat-0-SBOX⟨1·0·3·2⟩ : WsL → ⟪ (Sw01 ∷ Sb1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·0·3·2⟩ c4 = derive (Sw01 ∷ Sb1-0-3-2 ∷ []) (Sb0-1-3-2 ∷ Sw01 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   rw⁻ 0 (q71 c4) ∷
   re 0 1 (Sb0-1-3-2 ∷ []) ∷ []) Eq.refl

private
  q72 : WsL → Eqn
  q72 c4 = eqn (CS13⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS03⁻ ∷ []) (wl0121 c4)

-- nat 0 SBOXd(1;0;3;2): 3 steps
lem-nat-0-SBOXd⟨1·0·3·2⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·0·3·2⟩ c4 = derive (Sw01 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sw01 ∷ [])
  (re 1 1 (CS03⁻ ∷ []) ∷
   rw⁻ 0 (q72 c4) ∷
   re 0 1 (Sb⁻0-1-3-2 ∷ []) ∷ []) Eq.refl

private
  q73 : WsL → Eqn
  q73 c4 = eqn (Sw01 ∷ Bx1-0423 ∷ []) (Bx0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0423⟩ c4)
  q74 : WsL → Eqn
  q74 c4 = eqn (Sw01 ∷ Toff324 ∷ []) (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))
  q75 : WsL → Eqn
  q75 c4 = eqn (Sw01 ∷ Sb1-0-3-2 ∷ []) (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ c4)
  q76 : WsL → Eqn
  q76 c4 = eqn (Sw01 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ c4)

-- nat 0 SBOX(1;0;42;3): 7 steps
lem-nat-0-SBOX⟨1·0·42·3⟩ : WsL → ⟪ (Sw01 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·0·42·3⟩ c4 = derive (Sw01 ∷ Sb1-0-42-3 ∷ []) (Sb0-1-42-3 ∷ Sw01 ∷ [])
  (re 1 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 0 (q73 c4) ∷
   rw 1 (q74 c4) ∷
   rw 2 (q75 c4) ∷
   rw 3 (q74 c4) ∷
   rw 4 (q76 c4) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q77 : WsL → Eqn
  q77 c4 = eqn (Sw01 ∷ Sw34 ∷ []) (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑))

-- nat 0 CS04: 5 steps
lem-nat-0-CS04 : WsL → ⟪ (Sw01 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CS04 c4 = derive (Sw01 ∷ CS04 ∷ []) (CS14 ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 0 (q77 c4) ∷
   rw⁻ 1 (q71 c4) ∷
   rw 2 (q77 c4) ∷
   re 0 3 (CS14 ∷ []) ∷ []) Eq.refl

private
  q78 : WsL → Eqn
  q78 c4 = eqn (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) (wl0019 c4)

-- nat 0 CS14: 5 steps
lem-nat-0-CS14 : WsL → ⟪ (Sw01 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CS14 c4 = derive (Sw01 ∷ CS14 ∷ []) (CS04 ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 0 (q77 c4) ∷
   rw⁻ 1 (q78 c4) ∷
   rw 2 (q77 c4) ∷
   re 0 3 (CS04 ∷ []) ∷ []) Eq.refl

-- nat 0 SBOX(0;1;3;2): 3 steps
lem-nat-0-SBOX⟨0·1·3·2⟩ : WsL → ⟪ (Sw01 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·1·3·2⟩ c4 = derive (Sw01 ∷ Sb0-1-3-2 ∷ []) (Sb1-0-3-2 ∷ Sw01 ∷ [])
  (re 1 1 (CS13 ∷ []) ∷
   rw⁻ 0 (q78 c4) ∷
   re 0 1 (Sb1-0-3-2 ∷ []) ∷ []) Eq.refl

private
  q79 : WsL → Eqn
  q79 c4 = eqn (CS03⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS13⁻ ∷ []) (wl0022 c4)

-- nat 0 SBOXd(0;1;3;2): 3 steps
lem-nat-0-SBOXd⟨0·1·3·2⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·1·3·2⟩ c4 = derive (Sw01 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻1-0-3-2 ∷ Sw01 ∷ [])
  (re 1 1 (CS13⁻ ∷ []) ∷
   rw⁻ 0 (q79 c4) ∷
   re 0 1 (Sb⁻1-0-3-2 ∷ []) ∷ []) Eq.refl

private
  q80 : WsL → Eqn
  q80 c4 = eqn (Sw01 ∷ Bx0-1423 ∷ []) (Bx1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1423⟩ c4)
  q81 : WsL → Eqn
  q81 c4 = eqn (Sw01 ∷ Sb0-1-3-2 ∷ []) (Sb1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·3·2⟩ c4)
  q82 : WsL → Eqn
  q82 c4 = eqn (Sw01 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·3·2⟩ c4)

-- nat 0 SBOX(0;1;42;3): 7 steps
lem-nat-0-SBOX⟨0·1·42·3⟩ : WsL → ⟪ (Sw01 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·1·42·3⟩ c4 = derive (Sw01 ∷ Sb0-1-42-3 ∷ []) (Sb1-0-42-3 ∷ Sw01 ∷ [])
  (re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw 0 (q80 c4) ∷
   rw 1 (q74 c4) ∷
   rw 2 (q81 c4) ∷
   rw 3 (q74 c4) ∷
   rw 4 (q82 c4) ∷
   re 0 5 (Sb1-0-42-3 ∷ []) ∷ []) Eq.refl

private
  q83 : WsL → Eqn
  q83 c4 = eqn (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) (wl0010 c4)

-- nat 1 SBOX(2;0;3;1): 3 steps
lem-nat-1-SBOX⟨2·0·3·1⟩ : WsL → ⟪ (Sw12 ∷ Sb2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·0·3·1⟩ c4 = derive (Sw12 ∷ Sb2-0-3-1 ∷ []) (Sb1-0-3-2 ∷ Sw12 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   rw⁻ 0 (q83 c4) ∷
   re 0 1 (Sb1-0-3-2 ∷ []) ∷ []) Eq.refl

private
  q84 : WsL → Eqn
  q84 c4 = eqn (CS03⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS03⁻ ∷ []) (wl0023 c4)

-- nat 1 SBOXd(2;0;3;1): 3 steps
lem-nat-1-SBOXd⟨2·0·3·1⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·0·3·1⟩ c4 = derive (Sw12 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻1-0-3-2 ∷ Sw12 ∷ [])
  (re 1 1 (CS03⁻ ∷ []) ∷
   rw⁻ 0 (q84 c4) ∷
   re 0 1 (Sb⁻1-0-3-2 ∷ []) ∷ []) Eq.refl

private
  q85 : WsL → Eqn
  q85 c4 = eqn (Sw12 ∷ Bx2-0413 ∷ []) (Bx1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0413⟩ c4)
  q86 : WsL → Eqn
  q86 c4 = eqn (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) (wl0064 c4)
  q87 : WsL → Eqn
  q87 c4 = eqn (Sw12 ∷ Sb2-0-3-1 ∷ []) (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ c4)
  q88 : WsL → Eqn
  q88 c4 = eqn (Sw12 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ c4)

-- nat 1 SBOX(2;0;41;3): 7 steps
lem-nat-1-SBOX⟨2·0·41·3⟩ : WsL → ⟪ (Sw12 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·0·41·3⟩ c4 = derive (Sw12 ∷ Sb2-0-41-3 ∷ []) (Sb1-0-42-3 ∷ Sw12 ∷ [])
  (re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 0 (q85 c4) ∷
   rw 1 (q86 c4) ∷
   rw 2 (q87 c4) ∷
   rw 3 (q86 c4) ∷
   rw 4 (q88 c4) ∷
   re 0 5 (Sb1-0-42-3 ∷ []) ∷ []) Eq.refl

-- nat 1 CS04: 5 steps
lem-nat-1-CS04 : WsL → ⟪ (Sw12 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CS04 c4 = derive (Sw12 ∷ CS04 ∷ []) (CS04 ∷ Sw12 ∷ [])
  (re 1 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 0 (q12 c4) ∷
   rw⁻ 1 (q83 c4) ∷
   rw 2 (q12 c4) ∷
   re 0 3 (CS04 ∷ []) ∷ []) Eq.refl

-- nat 1 SBOX(1;0;3;2): 3 steps
lem-nat-1-SBOX⟨1·0·3·2⟩ : WsL → ⟪ (Sw12 ∷ Sb1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-3-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·0·3·2⟩ c4 = derive (Sw12 ∷ Sb1-0-3-2 ∷ []) (Sb2-0-3-1 ∷ Sw12 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   rw⁻ 0 (q83 c4) ∷
   re 0 1 (Sb2-0-3-1 ∷ []) ∷ []) Eq.refl

-- nat 1 SBOXd(1;0;3;2): 3 steps
lem-nat-1-SBOXd⟨1·0·3·2⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-3-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·0·3·2⟩ c4 = derive (Sw12 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻2-0-3-1 ∷ Sw12 ∷ [])
  (re 1 1 (CS03⁻ ∷ []) ∷
   rw⁻ 0 (q84 c4) ∷
   re 0 1 (Sb⁻2-0-3-1 ∷ []) ∷ []) Eq.refl

private
  q89 : WsL → Eqn
  q89 c4 = eqn (Sw12 ∷ Bx1-0423 ∷ []) (Bx2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0423⟩ c4)
  q90 : WsL → Eqn
  q90 c4 = eqn (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) (wl0063 c4)
  q91 : WsL → Eqn
  q91 c4 = eqn (Sw12 ∷ Sb1-0-3-2 ∷ []) (Sb2-0-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·3·2⟩ c4)
  q92 : WsL → Eqn
  q92 c4 = eqn (Sw12 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻2-0-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·3·2⟩ c4)

-- nat 1 SBOX(1;0;42;3): 7 steps
lem-nat-1-SBOX⟨1·0·42·3⟩ : WsL → ⟪ (Sw12 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·0·42·3⟩ c4 = derive (Sw12 ∷ Sb1-0-42-3 ∷ []) (Sb2-0-41-3 ∷ Sw12 ∷ [])
  (re 1 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 0 (q89 c4) ∷
   rw 1 (q90 c4) ∷
   rw 2 (q91 c4) ∷
   rw 3 (q90 c4) ∷
   rw 4 (q92 c4) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

-- nat 3 CS24: 2 steps
lem-nat-3-CS24 : WsL → ⟪ (Sw34 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CS24 c4 = derive (Sw34 ∷ CS24 ∷ []) (CS23 ∷ Sw34 ∷ [])
  (re 1 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 0 (q6 c4) ∷ []) Eq.refl

-- nat 3 CS23: 2 steps
lem-nat-3-CS23 : WsL → ⟪ (Sw34 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CS23 c4 = derive (Sw34 ∷ CS23 ∷ []) (CS24 ∷ Sw34 ∷ [])
  (rw⁻ 2 (q6 c4) ∷
   re 0 3 (CS24 ∷ []) ∷ []) Eq.refl

private
  q93 : WsL → Eqn
  q93 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 c4)
  q94 : WsL → Eqn
  q94 c4 = eqn (CX30 ∷ Sw01 ∷ []) (Sw01 ∷ CX31 ∷ []) (wl0122 c4)

-- resp CX40 at 1: 6 steps
lem-resp-CX40-at-1 : WsL → ⟪ (CX40 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX41 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX40-at-1 c4 = derive (CX40 ∷ []) (Sw01 ∷ CX41 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q93 c4) ∷
   re 0 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q77 c4) ∷
   rw 1 (q94 c4) ∷
   rw⁻ 0 (q77 c4) ∷
   re 1 3 (CX41 ∷ []) ∷ []) Eq.refl

private
  q95 : WsL → Eqn
  q95 c4 = eqn (CZ13 ∷ Sw01 ∷ []) (Sw01 ∷ CZ03 ∷ []) (wl0092 c4)

-- nat 0 BOX(2;03): 3 steps
lem-nat-0-BOX⟨2·03⟩ : WsL → ⟪ (Sw01 ∷ Bx2-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-13 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·03⟩ c4 = derive (Sw01 ∷ Bx2-03 ∷ []) (Bx2-13 ∷ Sw01 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw⁻ 0 (q95 c4) ∷
   re 0 1 (Bx2-13 ∷ []) ∷ []) Eq.refl

private
  q96 : WsL → Eqn
  q96 c4 = eqn (CCZ012 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ012 ∷ []) (wl0096 c4)
  q97 : WsL → Eqn
  q97 c4 = eqn (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) (wl0099 c4)
  q98 : WsL → Eqn
  q98 c4 = eqn (Sw01 ∷ Bx2-03 ∷ []) (Bx2-13 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·03⟩ c4)

-- nat 0 BOX(0;213): 8 steps
lem-nat-0-BOX⟨0·213⟩ : WsL → ⟪ (Sw01 ∷ Bx0-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-203 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·213⟩ c4 = derive (Sw01 ∷ Bx0-213 ∷ []) (Bx1-203 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   rw⁻ 0 (q96 c4) ∷
   rw 1 (q97 c4) ∷
   rw 2 (q98 c4) ∷
   rw 3 (q97 c4) ∷
   rw⁻ 4 (q96 c4) ∷
   rw 5 (q98 c4) ∷
   re 0 6 (Bx1-203 ∷ []) ∷ []) Eq.refl

private
  q99 : WsL → Eqn
  q99 c4 = eqn (Sw01 ∷ Bx0-213 ∷ []) (Bx1-203 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·213⟩ c4)

-- nat 0 BOX(2;0413): 8 steps
lem-nat-0-BOX⟨2·0413⟩ : WsL → ⟪ (Sw01 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·0413⟩ c4 = derive (Sw01 ∷ Bx2-0413 ∷ []) (Bx2-1403 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) ∷
   rw 0 (q49 c4) ∷
   rw 1 (q50 c4) ∷
   rw 2 (q99 c4) ∷
   rw 3 (q50 c4) ∷
   rw 4 (q49 c4) ∷
   rw 5 (q99 c4) ∷
   re 0 6 (Bx2-1403 ∷ []) ∷ []) Eq.refl

-- nat 3 CX42: 2 steps
lem-nat-3-CX42 : WsL → ⟪ (Sw34 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CX42 c4 = derive (Sw34 ∷ CX42 ∷ []) (CX32 ∷ Sw34 ∷ [])
  (re 1 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) ∷
   rw 0 (q6 c4) ∷ []) Eq.refl

private
  q100 : WsL → Eqn
  q100 c4 = eqn (CX31 ∷ Sw01 ∷ []) (Sw01 ∷ CX30 ∷ []) (wl0123 c4)

-- nat 0 CX40: 5 steps
lem-nat-0-CX40 : WsL → ⟪ (Sw01 ∷ CX40 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CX40 c4 = derive (Sw01 ∷ CX40 ∷ []) (CX41 ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) ∷
   rw 0 (q77 c4) ∷
   rw⁻ 1 (q100 c4) ∷
   rw 2 (q77 c4) ∷
   re 0 3 (CX41 ∷ []) ∷ []) Eq.refl

private
  q101 : WsL → Eqn
  q101 c4 = eqn (CZ03 ∷ Sw01 ∷ []) (Sw01 ∷ CZ13 ∷ []) (wl0088 c4)

-- nat 0 BOX(2;13): 3 steps
lem-nat-0-BOX⟨2·13⟩ : WsL → ⟪ (Sw01 ∷ Bx2-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-03 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·13⟩ c4 = derive (Sw01 ∷ Bx2-13 ∷ []) (Bx2-03 ∷ Sw01 ∷ [])
  (re 1 1 (CZ13 ∷ []) ∷
   rw⁻ 0 (q101 c4) ∷
   re 0 1 (Bx2-03 ∷ []) ∷ []) Eq.refl

private
  q102 : WsL → Eqn
  q102 c4 = eqn (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) (wl0097 c4)
  q103 : WsL → Eqn
  q103 c4 = eqn (Sw01 ∷ Bx2-13 ∷ []) (Bx2-03 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·13⟩ c4)

-- nat 0 BOX(1;203): 8 steps
lem-nat-0-BOX⟨1·203⟩ : WsL → ⟪ (Sw01 ∷ Bx1-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-213 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·203⟩ c4 = derive (Sw01 ∷ Bx1-203 ∷ []) (Bx0-213 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-13 ∷ Toff102 ∷ CCZ012 ∷ Bx2-13 ∷ []) ∷
   rw⁻ 0 (q96 c4) ∷
   rw 1 (q102 c4) ∷
   rw 2 (q103 c4) ∷
   rw 3 (q102 c4) ∷
   rw⁻ 4 (q96 c4) ∷
   rw 5 (q103 c4) ∷
   re 0 6 (Bx0-213 ∷ []) ∷ []) Eq.refl

private
  q104 : WsL → Eqn
  q104 c4 = eqn (Sw01 ∷ Bx1-203 ∷ []) (Bx0-213 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·203⟩ c4)

-- nat 0 BOX(2;1403): 8 steps
lem-nat-0-BOX⟨2·1403⟩ : WsL → ⟪ (Sw01 ∷ Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·1403⟩ c4 = derive (Sw01 ∷ Bx2-1403 ∷ []) (Bx2-0413 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-203 ∷ Toff214 ∷ CCZ124 ∷ Bx1-203 ∷ []) ∷
   rw 0 (q44 c4) ∷
   rw 1 (q45 c4) ∷
   rw 2 (q104 c4) ∷
   rw 3 (q45 c4) ∷
   rw 4 (q44 c4) ∷
   rw 5 (q104 c4) ∷
   re 0 6 (Bx2-0413 ∷ []) ∷ []) Eq.refl

private
  q105 : WsL → Eqn
  q105 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 c4)
  q106 : WsL → Eqn
  q106 c4 = eqn (CX30 ∷ Sw12 ∷ []) (Sw12 ∷ CX30 ∷ []) (wl0124 c4)

-- resp CX40 at 2: 12 steps
lem-resp-CX40-at-2 : WsL → ⟪ (CX40 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX41 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX40-at-2 c4 = derive (CX40 ∷ []) (Sw12 ∷ Sw01 ∷ CX41 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q105 c4) ∷
   re 0 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q12 c4) ∷
   rw 1 (q106 c4) ∷
   rw⁻ 0 (q12 c4) ∷
   re 1 3 (CX40 ∷ []) ∷
   rw⁻ 2 (q93 c4) ∷
   re 1 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) ∷
   rw⁻ 3 (q77 c4) ∷
   rw 2 (q94 c4) ∷
   rw⁻ 1 (q77 c4) ∷
   re 2 3 (CX41 ∷ []) ∷ []) Eq.refl

private
  q107 : WsL → Eqn
  q107 c4 = eqn (CX41 ∷ Sw12 ∷ []) (Sw12 ∷ CX42 ∷ []) (wl0125 c4)
  q108 : WsL → Eqn
  q108 c4 = eqn (Sw01 ∷ CX42 ∷ []) (CX42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CX₁₀ • Swap ↑))

-- resp CX41 at 2: 4 steps
lem-resp-CX41-at-2 : WsL → ⟪ (CX41 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX42 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX41-at-2 c4 = derive (CX41 ∷ []) (Sw12 ∷ Sw01 ∷ CX42 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q105 c4) ∷
   rw 0 (q107 c4) ∷
   rw⁻ 2 (q93 c4) ∷
   rw⁻ 1 (q108 c4) ∷ []) Eq.refl

-- resp CS04 at 2: 12 steps
lem-resp-CS04-at-2 : WsL → ⟪ (CS04 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CS04-at-2 c4 = derive (CS04 ∷ []) (Sw12 ∷ Sw01 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q105 c4) ∷
   re 0 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q12 c4) ∷
   rw 1 (q83 c4) ∷
   rw⁻ 0 (q12 c4) ∷
   re 1 3 (CS04 ∷ []) ∷
   rw⁻ 2 (q93 c4) ∷
   re 1 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 3 (q77 c4) ∷
   rw 2 (q78 c4) ∷
   rw⁻ 1 (q77 c4) ∷
   re 2 3 (CS14 ∷ []) ∷ []) Eq.refl

private
  q109 : WsL → Eqn
  q109 c4 = eqn (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4)
  q110 : WsL → Eqn
  q110 c4 = eqn (Sw23 ∷ Toff103 ∷ []) (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4)
  q111 : WsL → Eqn
  q111 c4 = eqn (Sw23 ∷ Bx0-12 ∷ []) (Bx0-13 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·12⟩ c4)

-- nat 2 BOX(1;032): 8 steps
lem-nat-2-BOX⟨1·032⟩ : WsL → ⟪ (Sw23 ∷ Bx1-032 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-023 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·032⟩ c4 = derive (Sw23 ∷ Bx1-032 ∷ []) (Bx1-023 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) ∷
   rw 0 (q109 c4) ∷
   rw 1 (q110 c4) ∷
   rw 2 (q111 c4) ∷
   rw 3 (q110 c4) ∷
   rw 4 (q109 c4) ∷
   rw 5 (q111 c4) ∷
   re 0 6 (Bx1-023 ∷ []) ∷ []) Eq.refl

private
  q112 : WsL → Eqn
  q112 c4 = eqn (Sw23 ∷ Bx1-032 ∷ []) (Bx1-023 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·032⟩ c4)

-- nat 2 BOX(0;1432): 8 steps
lem-nat-2-BOX⟨0·1432⟩ : WsL → ⟪ (Sw23 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·1432⟩ c4 = derive (Sw23 ∷ Bx0-1432 ∷ []) (Bx0-1423 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) ∷
   rw 0 (q18 c4) ∷
   rw 1 (q19 c4) ∷
   rw 2 (q112 c4) ∷
   rw 3 (q19 c4) ∷
   rw 4 (q18 c4) ∷
   rw 5 (q112 c4) ∷
   re 0 6 (Bx0-1423 ∷ []) ∷ []) Eq.refl

private
  q113 : WsL → Eqn
  q113 c4 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (c₁ (K) (Swap))
  q114 : WsL → Eqn
  q114 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0008 c4)
  q115 : WsL → Eqn
  q115 c4 = eqn (CS24⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS14⁻ ∷ []) (wl0009 c4)
  q116 : WsL → Eqn
  q116 c4 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap))
  q117 : WsL → Eqn
  q117 c4 = eqn (Sw01 ∷ ι ∷ []) (ι ∷ Sw01 ∷ []) (wl0030 c4)
  q118 : WsL → Eqn
  q118 c4 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wl0031 c4)
  q119 : WsL → Eqn
  q119 c4 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wl0048 c4)
  q120 : WsL → Eqn
  q120 c4 = eqn (Sw01 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q121 : WsL → Eqn
  q121 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q122 : WsL → Eqn
  q122 c4 = eqn (K1 ∷ Sw34 ∷ []) (Sw34 ∷ K1 ∷ []) (c₂ (K ↑) (Swap ↑))
  q123 : WsL → Eqn
  q123 c4 = eqn (CX12 ∷ Sw34 ∷ []) (Sw34 ∷ CX12 ∷ []) (c₃ (CX₀₁ ↑) (Swap))
  q124 : WsL → Eqn
  q124 c4 = eqn (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wl0032 c4)

-- resp TOFF014 at 3: 143 steps
lem-resp-TOFF014-at-3 : WsL → ⟪ (Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff124 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF014-at-3 c4 = derive (Toff014 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff124 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q2 c4) ∷
   re 0 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 (q3 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 (q1 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw 9 (q2 c4) ∷
   rw⁻ 0 (q5 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   re 1 3 (CS14 ∷ []) ∷
   rw⁻ 2 (q7 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (CS14⁻ ∷ []) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw⁻ 6 (q5 c4) ∷
   rw⁻ 7 (q8 c4) ∷
   rw 8 (q6 c4) ∷
   rw 7 (q4 c4) ∷
   rw 6 (q1 c4) ∷
   re 5 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 10 (q11 c4) ∷
   rw 9 (q12 c4) ∷
   rw 8 (q13 c4) ∷
   rw 7 (q12 c4) ∷
   rw⁻ 5 (q11 c4) ∷
   re 6 7 (CS04 ∷ []) ∷
   rw 4 (q3 c4) ∷
   rw 3 (q10 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q9 c4) ∷
   rw 0 (q1 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   re 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   re 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q6 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 9 (q8 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 (q2 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q2 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 (q2 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 2 3 (Toff013 ∷ []) ∷
   re 1 3 (Toff014 ∷ []) ∷
   rw⁻ 2 (q105 c4) ∷
   rw⁻ 1 (q105 c4) ∷
   re 2 3 (Toff024 ∷ []) ∷
   rw⁻ 3 (q93 c4) ∷
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
   rw⁻ 2 (q113 c4) ∷
   rw⁻ 3 (q114 c4) ∷
   rw⁻ 6 (q105 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw⁻ 5 (q115 c4) ∷
   rw⁻ 8 (q105 c4) ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q12 c4) ∷
   rw⁻ 8 (q83 c4) ∷
   rw 9 (q12 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q113 c4) ∷
   rw⁻ 9 (q116 c4) ∷
   rw 10 (q105 c4) ∷
   rw⁻ 9 (q117 c4) ∷
   rw 8 (q118 c4) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 9 (q77 c4) ∷
   rw 8 (q78 c4) ∷
   rw⁻ 7 (q77 c4) ∷
   re 8 3 (CS14 ∷ []) ∷
   rw 6 (q119 c4) ∷
   rw⁻ 5 (q120 c4) ∷
   rw 4 (q119 c4) ∷
   rw⁻ 3 (q121 c4) ∷
   rw 2 (q118 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw⁻ 4 (q122 c4) ∷
   re 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q123 c4) ∷
   re 8 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 7 (q6 c4) ∷
   rw⁻ 8 (q123 c4) ∷
   re 10 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 9 (q6 c4) ∷
   rw⁻ 10 (q122 c4) ∷
   rw⁻ 11 (q8 c4) ∷
   rw 4 (q124 c4) ∷
   re 4 8 (Toff123 ∷ []) ∷
   re 3 3 (Toff124 ∷ []) ∷ []) Eq.refl

private
  q125 : WsL → Eqn
  q125 c4 = eqn (Sw12 ∷ CZ02 ∷ []) (CZ01 ∷ Sw12 ∷ []) (lem-nat-1-CZ02 c4)

-- nat 1 BOX(3;02): 3 steps
lem-nat-1-BOX⟨3·02⟩ : WsL → ⟪ (Sw12 ∷ Bx3-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-01 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·02⟩ c4 = derive (Sw12 ∷ Bx3-02 ∷ []) (Bx3-01 ∷ Sw12 ∷ [])
  (re 1 1 (CZ02 ∷ []) ∷
   rw 0 (q125 c4) ∷
   re 0 1 (Bx3-01 ∷ []) ∷ []) Eq.refl

private
  q126 : WsL → Eqn
  q126 c4 = eqn (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4)
  q127 : WsL → Eqn
  q127 c4 = eqn (Sw12 ∷ Toff013 ∷ []) (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4)
  q128 : WsL → Eqn
  q128 c4 = eqn (Sw12 ∷ Bx3-02 ∷ []) (Bx3-01 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·02⟩ c4)

-- nat 1 BOX(0;312): 8 steps
lem-nat-1-BOX⟨0·312⟩ : WsL → ⟪ (Sw12 ∷ Bx0-312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-321 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·312⟩ c4 = derive (Sw12 ∷ Bx0-312 ∷ []) (Bx0-321 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) ∷
   rw 0 (q126 c4) ∷
   rw 1 (q127 c4) ∷
   rw 2 (q128 c4) ∷
   rw 3 (q127 c4) ∷
   rw 4 (q126 c4) ∷
   rw 5 (q128 c4) ∷
   re 0 6 (Bx0-321 ∷ []) ∷ []) Eq.refl

private
  q129 : WsL → Eqn
  q129 c4 = eqn (Sw12 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4)
  q130 : WsL → Eqn
  q130 c4 = eqn (Sw12 ∷ Toff304 ∷ []) (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4)
  q131 : WsL → Eqn
  q131 c4 = eqn (Sw12 ∷ Bx0-312 ∷ []) (Bx0-321 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·312⟩ c4)

-- nat 1 BOX(3;0412): 8 steps
lem-nat-1-BOX⟨3·0412⟩ : WsL → ⟪ (Sw12 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·0412⟩ c4 = derive (Sw12 ∷ Bx3-0412 ∷ []) (Bx3-0421 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) ∷
   rw 0 (q129 c4) ∷
   rw 1 (q130 c4) ∷
   rw 2 (q131 c4) ∷
   rw 3 (q130 c4) ∷
   rw 4 (q129 c4) ∷
   rw 5 (q131 c4) ∷
   re 0 6 (Bx3-0421 ∷ []) ∷ []) Eq.refl

private
  q132 : WsL → Eqn
  q132 c4 = eqn (Sw12 ∷ CS02 ∷ []) (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4)

-- nat 1 SBOX(3;0;2;1): 3 steps
lem-nat-1-SBOX⟨3·0·2·1⟩ : WsL → ⟪ (Sw12 ∷ Sb3-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-1-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·0·2·1⟩ c4 = derive (Sw12 ∷ Sb3-0-2-1 ∷ []) (Sb3-0-1-2 ∷ Sw12 ∷ [])
  (re 1 1 (CS02 ∷ []) ∷
   rw 0 (q132 c4) ∷
   re 0 1 (Sb3-0-1-2 ∷ []) ∷ []) Eq.refl

-- nat 1 CSd02: 2 steps
lem-nat-1-CSd02 : WsL → ⟪ (Sw12 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CSd02 c4 = derive (Sw12 ∷ CS02⁻ ∷ []) (CS01⁻ ∷ Sw12 ∷ [])
  (re 1 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 0 (q105 c4) ∷ []) Eq.refl

private
  q133 : WsL → Eqn
  q133 c4 = eqn (Sw12 ∷ CS02⁻ ∷ []) (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4)

-- nat 1 SBOXd(3;0;2;1): 3 steps
lem-nat-1-SBOXd⟨3·0·2·1⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻3-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-1-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·0·2·1⟩ c4 = derive (Sw12 ∷ Sb⁻3-0-2-1 ∷ []) (Sb⁻3-0-1-2 ∷ Sw12 ∷ [])
  (re 1 1 (CS02⁻ ∷ []) ∷
   rw 0 (q133 c4) ∷
   re 0 1 (Sb⁻3-0-1-2 ∷ []) ∷ []) Eq.refl

private
  q134 : WsL → Eqn
  q134 c4 = eqn (Sw12 ∷ Bx3-0412 ∷ []) (Bx3-0421 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0412⟩ c4)
  q135 : WsL → Eqn
  q135 c4 = eqn (Sw12 ∷ Toff214 ∷ []) (Toff124 ∷ Sw12 ∷ []) (wl0126 c4)
  q136 : WsL → Eqn
  q136 c4 = eqn (Sw12 ∷ Sb3-0-2-1 ∷ []) (Sb3-0-1-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·2·1⟩ c4)
  q137 : WsL → Eqn
  q137 c4 = eqn (Sw12 ∷ Sb⁻3-0-2-1 ∷ []) (Sb⁻3-0-1-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·0·2·1⟩ c4)

-- nat 1 SBOX(3;0;41;2): 7 steps
lem-nat-1-SBOX⟨3·0·41·2⟩ : WsL → ⟪ (Sw12 ∷ Sb3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-42-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·0·41·2⟩ c4 = derive (Sw12 ∷ Sb3-0-41-2 ∷ []) (Sb3-0-42-1 ∷ Sw12 ∷ [])
  (re 1 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   rw 0 (q134 c4) ∷
   rw 1 (q135 c4) ∷
   rw 2 (q136 c4) ∷
   rw 3 (q135 c4) ∷
   rw 4 (q137 c4) ∷
   re 0 5 (Sb3-0-42-1 ∷ []) ∷ []) Eq.refl

private
  q138 : WsL → Eqn
  q138 c4 = eqn (Sw23 ∷ CZ02 ∷ []) (CZ03 ∷ Sw23 ∷ []) (lem-nat-2-CZ02 c4)

-- nat 2 BOX(1;02): 3 steps
lem-nat-2-BOX⟨1·02⟩ : WsL → ⟪ (Sw23 ∷ Bx1-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-03 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·02⟩ c4 = derive (Sw23 ∷ Bx1-02 ∷ []) (Bx1-03 ∷ Sw23 ∷ [])
  (re 1 1 (CZ02 ∷ []) ∷
   rw 0 (q138 c4) ∷
   re 0 1 (Bx1-03 ∷ []) ∷ []) Eq.refl

private
  q139 : WsL → Eqn
  q139 c4 = eqn (Sw23 ∷ Toff013 ∷ []) (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4)
  q140 : WsL → Eqn
  q140 c4 = eqn (Sw23 ∷ Bx1-02 ∷ []) (Bx1-03 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·02⟩ c4)

-- nat 2 BOX(0;132): 8 steps
lem-nat-2-BOX⟨0·132⟩ : WsL → ⟪ (Sw23 ∷ Bx0-132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-123 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·132⟩ c4 = derive (Sw23 ∷ Bx0-132 ∷ []) (Bx0-123 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-02 ∷ Toff013 ∷ CCZ013 ∷ Bx1-02 ∷ []) ∷
   rw 0 (q109 c4) ∷
   rw 1 (q139 c4) ∷
   rw 2 (q140 c4) ∷
   rw 3 (q139 c4) ∷
   rw 4 (q109 c4) ∷
   rw 5 (q140 c4) ∷
   re 0 6 (Bx0-123 ∷ []) ∷ []) Eq.refl

private
  q141 : WsL → Eqn
  q141 c4 = eqn (Sw23 ∷ Toff104 ∷ []) (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4)
  q142 : WsL → Eqn
  q142 c4 = eqn (Sw23 ∷ Bx0-132 ∷ []) (Bx0-123 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·132⟩ c4)

-- nat 2 BOX(1;0432): 8 steps
lem-nat-2-BOX⟨1·0432⟩ : WsL → ⟪ (Sw23 ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·0432⟩ c4 = derive (Sw23 ∷ Bx1-0432 ∷ []) (Bx1-0423 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-132 ∷ Toff104 ∷ CCZ014 ∷ Bx0-132 ∷ []) ∷
   rw 0 (q18 c4) ∷
   rw 1 (q141 c4) ∷
   rw 2 (q142 c4) ∷
   rw 3 (q141 c4) ∷
   rw 4 (q18 c4) ∷
   rw 5 (q142 c4) ∷
   re 0 6 (Bx1-0423 ∷ []) ∷ []) Eq.refl

-- nat 2 CS02: 2 steps
lem-nat-2-CS02 : WsL → ⟪ (Sw23 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CS02 c4 = derive (Sw23 ∷ CS02 ∷ []) (CS03 ∷ Sw23 ∷ [])
  (rw⁻ 2 (q2 c4) ∷
   re 0 3 (CS03 ∷ []) ∷ []) Eq.refl

private
  q143 : WsL → Eqn
  q143 c4 = eqn (Sw23 ∷ CS02 ∷ []) (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4)

-- nat 2 SBOX(1;0;2;3): 3 steps
lem-nat-2-SBOX⟨1·0·2·3⟩ : WsL → ⟪ (Sw23 ∷ Sb1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·0·2·3⟩ c4 = derive (Sw23 ∷ Sb1-0-2-3 ∷ []) (Sb1-0-3-2 ∷ Sw23 ∷ [])
  (re 1 1 (CS02 ∷ []) ∷
   rw 0 (q143 c4) ∷
   re 0 1 (Sb1-0-3-2 ∷ []) ∷ []) Eq.refl

-- nat 2 CSd02: 2 steps
lem-nat-2-CSd02 : WsL → ⟪ (Sw23 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CSd02 c4 = derive (Sw23 ∷ CS02⁻ ∷ []) (CS03⁻ ∷ Sw23 ∷ [])
  (rw⁻ 2 (q2 c4) ∷
   re 0 3 (CS03⁻ ∷ []) ∷ []) Eq.refl

private
  q144 : WsL → Eqn
  q144 c4 = eqn (Sw23 ∷ CS02⁻ ∷ []) (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 c4)

-- nat 2 SBOXd(1;0;2;3): 3 steps
lem-nat-2-SBOXd⟨1·0·2·3⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·2·3⟩ c4 = derive (Sw23 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻1-0-3-2 ∷ Sw23 ∷ [])
  (re 1 1 (CS02⁻ ∷ []) ∷
   rw 0 (q144 c4) ∷
   re 0 1 (Sb⁻1-0-3-2 ∷ []) ∷ []) Eq.refl

private
  q145 : WsL → Eqn
  q145 c4 = eqn (Sw23 ∷ Bx1-0432 ∷ []) (Bx1-0423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0432⟩ c4)
  q146 : WsL → Eqn
  q146 c4 = eqn (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) (wl0127 c4)
  q147 : WsL → Eqn
  q147 c4 = eqn (Sw23 ∷ Sb1-0-2-3 ∷ []) (Sb1-0-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·2·3⟩ c4)
  q148 : WsL → Eqn
  q148 c4 = eqn (Sw23 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻1-0-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·2·3⟩ c4)

-- nat 2 SBOX(1;0;43;2): 7 steps
lem-nat-2-SBOX⟨1·0·43·2⟩ : WsL → ⟪ (Sw23 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-42-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·0·43·2⟩ c4 = derive (Sw23 ∷ Sb1-0-43-2 ∷ []) (Sb1-0-42-3 ∷ Sw23 ∷ [])
  (re 1 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) ∷
   rw 0 (q145 c4) ∷
   rw 1 (q146 c4) ∷
   rw 2 (q147 c4) ∷
   rw 3 (q146 c4) ∷
   rw 4 (q148 c4) ∷
   re 0 5 (Sb1-0-42-3 ∷ []) ∷ []) Eq.refl

private
  q149 : WsL → Eqn
  q149 c4 = eqn (Bx3-01 ∷ Sw23 ∷ []) (Sw23 ∷ Bx3-01 ∷ []) (c₂ (CZ) (Swap))

-- nat 2 BOX(3;01): 2 steps
lem-nat-2-BOX⟨3·01⟩ : WsL → ⟪ (Sw23 ∷ Bx3-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-01 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·01⟩ c4 = derive (Sw23 ∷ Bx3-01 ∷ []) (Bx2-01 ∷ Sw23 ∷ [])
  (rw⁻ 0 (q149 c4) ∷
   re 0 1 (Bx2-01 ∷ []) ∷ []) Eq.refl

private
  q150 : WsL → Eqn
  q150 c4 = eqn (CCZ023 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ023 ∷ []) (wl0065 c4)
  q151 : WsL → Eqn
  q151 c4 = eqn (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) (wl0093 c4)
  q152 : WsL → Eqn
  q152 c4 = eqn (Sw23 ∷ Bx3-01 ∷ []) (Bx2-01 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·01⟩ c4)

-- nat 2 BOX(0;321): 8 steps
lem-nat-2-BOX⟨0·321⟩ : WsL → ⟪ (Sw23 ∷ Bx0-321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-231 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·321⟩ c4 = derive (Sw23 ∷ Bx0-321 ∷ []) (Bx0-231 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) ∷
   rw⁻ 0 (q150 c4) ∷
   rw 1 (q151 c4) ∷
   rw 2 (q152 c4) ∷
   rw 3 (q151 c4) ∷
   rw⁻ 4 (q150 c4) ∷
   rw 5 (q152 c4) ∷
   re 0 6 (Bx0-231 ∷ []) ∷ []) Eq.refl

private
  q153 : WsL → Eqn
  q153 c4 = eqn (Sw23 ∷ Toff304 ∷ []) (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4)
  q154 : WsL → Eqn
  q154 c4 = eqn (Sw23 ∷ Bx0-321 ∷ []) (Bx0-231 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·321⟩ c4)

-- nat 2 BOX(3;0421): 8 steps
lem-nat-2-BOX⟨3·0421⟩ : WsL → ⟪ (Sw23 ∷ Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·0421⟩ c4 = derive (Sw23 ∷ Bx3-0421 ∷ []) (Bx2-0431 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-321 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ []) ∷
   rw 0 (q15 c4) ∷
   rw 1 (q153 c4) ∷
   rw 2 (q154 c4) ∷
   rw 3 (q153 c4) ∷
   rw 4 (q15 c4) ∷
   rw 5 (q154 c4) ∷
   re 0 6 (Bx2-0431 ∷ []) ∷ []) Eq.refl

-- nat 2 TOFF124: 2 steps
lem-nat-2-TOFF124 : WsL → ⟪ (Sw23 ∷ Toff124 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF124 c4 = derive (Sw23 ∷ Toff124 ∷ []) (Toff134 ∷ Sw23 ∷ [])
  (rw⁻ 2 (q2 c4) ∷
   re 0 3 (Toff134 ∷ []) ∷ []) Eq.refl

private
  q155 : WsL → Eqn
  q155 c4 = eqn (Sb3-0-1-2 ∷ Sw23 ∷ []) (Sw23 ∷ Sb3-0-1-2 ∷ []) (c₂ (CS) (Swap))

-- nat 2 SBOX(3;0;1;2): 2 steps
lem-nat-2-SBOX⟨3·0·1·2⟩ : WsL → ⟪ (Sw23 ∷ Sb3-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-1-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·0·1·2⟩ c4 = derive (Sw23 ∷ Sb3-0-1-2 ∷ []) (Sb2-0-1-3 ∷ Sw23 ∷ [])
  (rw⁻ 0 (q155 c4) ∷
   re 0 1 (Sb2-0-1-3 ∷ []) ∷ []) Eq.refl

private
  q156 : WsL → Eqn
  q156 c4 = eqn (Sb⁻3-0-1-2 ∷ Sw23 ∷ []) (Sw23 ∷ Sb⁻3-0-1-2 ∷ []) (c₂ (CS • CS • CS) (Swap))

-- nat 2 SBOXd(3;0;1;2): 2 steps
lem-nat-2-SBOXd⟨3·0·1·2⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻3-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-1-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·0·1·2⟩ c4 = derive (Sw23 ∷ Sb⁻3-0-1-2 ∷ []) (Sb⁻2-0-1-3 ∷ Sw23 ∷ [])
  (rw⁻ 0 (q156 c4) ∷
   re 0 1 (Sb⁻2-0-1-3 ∷ []) ∷ []) Eq.refl

private
  q157 : WsL → Eqn
  q157 c4 = eqn (Sw23 ∷ Bx3-0421 ∷ []) (Bx2-0431 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0421⟩ c4)
  q158 : WsL → Eqn
  q158 c4 = eqn (Sw23 ∷ Toff124 ∷ []) (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4)
  q159 : WsL → Eqn
  q159 c4 = eqn (Sw23 ∷ Sb3-0-1-2 ∷ []) (Sb2-0-1-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·1·2⟩ c4)
  q160 : WsL → Eqn
  q160 c4 = eqn (Sw23 ∷ Sb⁻3-0-1-2 ∷ []) (Sb⁻2-0-1-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·0·1·2⟩ c4)

-- nat 2 SBOX(3;0;42;1): 7 steps
lem-nat-2-SBOX⟨3·0·42·1⟩ : WsL → ⟪ (Sw23 ∷ Sb3-0-42-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-43-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·0·42·1⟩ c4 = derive (Sw23 ∷ Sb3-0-42-1 ∷ []) (Sb2-0-43-1 ∷ Sw23 ∷ [])
  (re 1 1 (Bx3-0421 ∷ Toff124 ∷ Sb3-0-1-2 ∷ Toff124 ∷ Sb⁻3-0-1-2 ∷ []) ∷
   rw 0 (q157 c4) ∷
   rw 1 (q158 c4) ∷
   rw 2 (q159 c4) ∷
   rw 3 (q158 c4) ∷
   rw 4 (q160 c4) ∷
   re 0 5 (Sb2-0-43-1 ∷ []) ∷ []) Eq.refl

private
  q161 : WsL → Eqn
  q161 c4 = eqn (Sw34 ∷ CCZ014 ∷ []) (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4)
  q162 : WsL → Eqn
  q162 c4 = eqn (Sw34 ∷ Toff014 ∷ []) (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4)
  q163 : WsL → Eqn
  q163 c4 = eqn (Bx1-02 ∷ Sw34 ∷ []) (Sw34 ∷ Bx1-02 ∷ []) (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))

-- nat 3 BOX(0;142): 8 steps
lem-nat-3-BOX⟨0·142⟩ : WsL → ⟪ (Sw34 ∷ Bx0-142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-132 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·142⟩ c4 = derive (Sw34 ∷ Bx0-142 ∷ []) (Bx0-132 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-02 ∷ Toff014 ∷ CCZ014 ∷ Bx1-02 ∷ []) ∷
   rw 0 (q161 c4) ∷
   rw 1 (q162 c4) ∷
   rw⁻ 2 (q163 c4) ∷
   rw 3 (q162 c4) ∷
   rw 4 (q161 c4) ∷
   rw⁻ 5 (q163 c4) ∷
   re 0 6 (Bx0-132 ∷ []) ∷ []) Eq.refl

private
  q164 : WsL → Eqn
  q164 c4 = eqn (Sw34 ∷ CCZ013 ∷ []) (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4)
  q165 : WsL → Eqn
  q165 c4 = eqn (Sw34 ∷ Toff103 ∷ []) (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4)
  q166 : WsL → Eqn
  q166 c4 = eqn (Sw34 ∷ Bx0-142 ∷ []) (Bx0-132 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·142⟩ c4)

-- nat 3 BOX(1;0342): 8 steps
lem-nat-3-BOX⟨1·0342⟩ : WsL → ⟪ (Sw34 ∷ Bx1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·0342⟩ c4 = derive (Sw34 ∷ Bx1-0342 ∷ []) (Bx1-0432 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-142 ∷ Toff103 ∷ CCZ013 ∷ Bx0-142 ∷ []) ∷
   rw 0 (q164 c4) ∷
   rw 1 (q165 c4) ∷
   rw 2 (q166 c4) ∷
   rw 3 (q165 c4) ∷
   rw 4 (q164 c4) ∷
   rw 5 (q166 c4) ∷
   re 0 6 (Bx1-0432 ∷ []) ∷ []) Eq.refl

private
  q167 : WsL → Eqn
  q167 c4 = eqn (Sb1-0-2-4 ∷ Sw34 ∷ []) (Sw34 ∷ Sb1-0-2-4 ∷ []) (c₃ (Swap ↑ • CS • Swap ↑) (Swap))

-- nat 3 SBOX(1;0;2;4): 2 steps
lem-nat-3-SBOX⟨1·0·2·4⟩ : WsL → ⟪ (Sw34 ∷ Sb1-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·0·2·4⟩ c4 = derive (Sw34 ∷ Sb1-0-2-4 ∷ []) (Sb1-0-2-3 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q167 c4) ∷
   re 0 1 (Sb1-0-2-3 ∷ []) ∷ []) Eq.refl

private
  q168 : WsL → Eqn
  q168 c4 = eqn (Sb⁻1-0-2-4 ∷ Sw34 ∷ []) (Sw34 ∷ Sb⁻1-0-2-4 ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (Swap))

-- nat 3 SBOXd(1;0;2;4): 2 steps
lem-nat-3-SBOXd⟨1·0·2·4⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻1-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·0·2·4⟩ c4 = derive (Sw34 ∷ Sb⁻1-0-2-4 ∷ []) (Sb⁻1-0-2-3 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q168 c4) ∷
   re 0 1 (Sb⁻1-0-2-3 ∷ []) ∷ []) Eq.refl

private
  q169 : WsL → Eqn
  q169 c4 = eqn (Sw34 ∷ Bx1-0342 ∷ []) (Bx1-0432 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·0342⟩ c4)
  q170 : WsL → Eqn
  q170 c4 = eqn (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) (wl0128 c4)
  q171 : WsL → Eqn
  q171 c4 = eqn (Sw34 ∷ Sb1-0-2-4 ∷ []) (Sb1-0-2-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·2·4⟩ c4)
  q172 : WsL → Eqn
  q172 c4 = eqn (Sw34 ∷ Sb⁻1-0-2-4 ∷ []) (Sb⁻1-0-2-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·2·4⟩ c4)

-- nat 3 SBOX(1;0;34;2): 7 steps
lem-nat-3-SBOX⟨1·0·34·2⟩ : WsL → ⟪ (Sw34 ∷ Sb1-0-34-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·0·34·2⟩ c4 = derive (Sw34 ∷ Sb1-0-34-2 ∷ []) (Sb1-0-43-2 ∷ Sw34 ∷ [])
  (re 1 1 (Bx1-0342 ∷ Toff234 ∷ Sb1-0-2-4 ∷ Toff234 ∷ Sb⁻1-0-2-4 ∷ []) ∷
   rw 0 (q169 c4) ∷
   rw 1 (q170 c4) ∷
   rw 2 (q171 c4) ∷
   rw 3 (q170 c4) ∷
   rw 4 (q172 c4) ∷
   re 0 5 (Sb1-0-43-2 ∷ []) ∷ []) Eq.refl

private
  q173 : WsL → Eqn
  q173 c4 = eqn (Sw34 ∷ CCZ023 ∷ []) (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4)
  q174 : WsL → Eqn
  q174 c4 = eqn (Sw34 ∷ Toff023 ∷ []) (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4)
  q175 : WsL → Eqn
  q175 c4 = eqn (Bx2-01 ∷ Sw34 ∷ []) (Sw34 ∷ Bx2-01 ∷ []) (c₂ (CZ) (Swap ↑))

-- nat 3 BOX(0;231): 8 steps
lem-nat-3-BOX⟨0·231⟩ : WsL → ⟪ (Sw34 ∷ Bx0-231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-241 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·231⟩ c4 = derive (Sw34 ∷ Bx0-231 ∷ []) (Bx0-241 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) ∷
   rw 0 (q173 c4) ∷
   rw 1 (q174 c4) ∷
   rw⁻ 2 (q175 c4) ∷
   rw 3 (q174 c4) ∷
   rw 4 (q173 c4) ∷
   rw⁻ 5 (q175 c4) ∷
   re 0 6 (Bx0-241 ∷ []) ∷ []) Eq.refl

private
  q176 : WsL → Eqn
  q176 c4 = eqn (Sw34 ∷ CCZ024 ∷ []) (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4)
  q177 : WsL → Eqn
  q177 c4 = eqn (Sw34 ∷ Toff204 ∷ []) (Toff203 ∷ Sw34 ∷ []) (lem-nat-3-TOFF204 c4)
  q178 : WsL → Eqn
  q178 c4 = eqn (Sw34 ∷ Bx0-231 ∷ []) (Bx0-241 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·231⟩ c4)

-- nat 3 BOX(2;0431): 8 steps
lem-nat-3-BOX⟨2·0431⟩ : WsL → ⟪ (Sw34 ∷ Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·0431⟩ c4 = derive (Sw34 ∷ Bx2-0431 ∷ []) (Bx2-0341 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-231 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ []) ∷
   rw 0 (q176 c4) ∷
   rw 1 (q177 c4) ∷
   rw 2 (q178 c4) ∷
   rw 3 (q177 c4) ∷
   rw 4 (q176 c4) ∷
   rw 5 (q178 c4) ∷
   re 0 6 (Bx2-0341 ∷ []) ∷ []) Eq.refl

private
  q179 : WsL → Eqn
  q179 c4 = eqn (Sb2-0-1-3 ∷ Sw34 ∷ []) (Sw34 ∷ Sb2-0-1-3 ∷ []) (c₂ (CS) (Swap ↑))

-- nat 3 SBOX(2;0;1;3): 2 steps
lem-nat-3-SBOX⟨2·0·1·3⟩ : WsL → ⟪ (Sw34 ∷ Sb2-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-1-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·0·1·3⟩ c4 = derive (Sw34 ∷ Sb2-0-1-3 ∷ []) (Sb2-0-1-4 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q179 c4) ∷
   re 0 1 (Sb2-0-1-4 ∷ []) ∷ []) Eq.refl

private
  q180 : WsL → Eqn
  q180 c4 = eqn (Sb⁻2-0-1-3 ∷ Sw34 ∷ []) (Sw34 ∷ Sb⁻2-0-1-3 ∷ []) (c₂ (CS • CS • CS) (Swap ↑))

-- nat 3 SBOXd(2;0;1;3): 2 steps
lem-nat-3-SBOXd⟨2·0·1·3⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻2-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-1-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·0·1·3⟩ c4 = derive (Sw34 ∷ Sb⁻2-0-1-3 ∷ []) (Sb⁻2-0-1-4 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q180 c4) ∷
   re 0 1 (Sb⁻2-0-1-4 ∷ []) ∷ []) Eq.refl

private
  q181 : WsL → Eqn
  q181 c4 = eqn (Sw34 ∷ Bx2-0431 ∷ []) (Bx2-0341 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·0431⟩ c4)
  q182 : WsL → Eqn
  q182 c4 = eqn (Sw34 ∷ Toff134 ∷ []) (Toff134 ∷ Sw34 ∷ []) (wl0129 c4)
  q183 : WsL → Eqn
  q183 c4 = eqn (Sw34 ∷ Sb2-0-1-3 ∷ []) (Sb2-0-1-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·1·3⟩ c4)
  q184 : WsL → Eqn
  q184 c4 = eqn (Sw34 ∷ Sb⁻2-0-1-3 ∷ []) (Sb⁻2-0-1-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·1·3⟩ c4)

-- nat 3 SBOX(2;0;43;1): 7 steps
lem-nat-3-SBOX⟨2·0·43·1⟩ : WsL → ⟪ (Sw34 ∷ Sb2-0-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-34-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·0·43·1⟩ c4 = derive (Sw34 ∷ Sb2-0-43-1 ∷ []) (Sb2-0-34-1 ∷ Sw34 ∷ [])
  (re 1 1 (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) ∷
   rw 0 (q181 c4) ∷
   rw 1 (q182 c4) ∷
   rw 2 (q183 c4) ∷
   rw 3 (q182 c4) ∷
   rw 4 (q184 c4) ∷
   re 0 5 (Sb2-0-34-1 ∷ []) ∷ []) Eq.refl

private
  q185 : WsL → Eqn
  q185 c4 = eqn (CZ02 ∷ Sw01 ∷ []) (Sw01 ∷ CZ12 ∷ []) (wl0105 c4)

-- nat 0 BOX(0;12): 3 steps
lem-nat-0-BOX⟨0·12⟩ : WsL → ⟪ (Sw01 ∷ Bx0-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-02 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·12⟩ c4 = derive (Sw01 ∷ Bx0-12 ∷ []) (Bx1-02 ∷ Sw01 ∷ [])
  (re 1 1 (CZ12 ∷ []) ∷
   rw⁻ 0 (q185 c4) ∷
   re 0 1 (Bx1-02 ∷ []) ∷ []) Eq.refl

private
  q186 : WsL → Eqn
  q186 c4 = eqn (Sw01 ∷ Bx0-12 ∷ []) (Bx1-02 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·12⟩ c4)

-- nat 0 BOX(1;042): 8 steps
lem-nat-0-BOX⟨1·042⟩ : WsL → ⟪ (Sw01 ∷ Bx1-042 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-142 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·042⟩ c4 = derive (Sw01 ∷ Bx1-042 ∷ []) (Bx0-142 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) ∷
   rw 0 (q30 c4) ∷
   rw 1 (q31 c4) ∷
   rw 2 (q186 c4) ∷
   rw 3 (q31 c4) ∷
   rw 4 (q30 c4) ∷
   rw 5 (q186 c4) ∷
   re 0 6 (Bx0-142 ∷ []) ∷ []) Eq.refl

private
  q187 : WsL → Eqn
  q187 c4 = eqn (CCZ013 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ013 ∷ []) (wl0100 c4)
  q188 : WsL → Eqn
  q188 c4 = eqn (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) (wl0101 c4)
  q189 : WsL → Eqn
  q189 c4 = eqn (Sw01 ∷ Bx1-042 ∷ []) (Bx0-142 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·042⟩ c4)

-- nat 0 BOX(0;1342): 8 steps
lem-nat-0-BOX⟨0·1342⟩ : WsL → ⟪ (Sw01 ∷ Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0342 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·1342⟩ c4 = derive (Sw01 ∷ Bx0-1342 ∷ []) (Bx1-0342 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ []) ∷
   rw⁻ 0 (q187 c4) ∷
   rw 1 (q188 c4) ∷
   rw 2 (q189 c4) ∷
   rw 3 (q188 c4) ∷
   rw⁻ 4 (q187 c4) ∷
   rw 5 (q189 c4) ∷
   re 0 6 (Bx1-0342 ∷ []) ∷ []) Eq.refl

private
  q190 : WsL → Eqn
  q190 c4 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wl0035 c4)

-- nat 0 SBOX(0;1;2;4): 3 steps
lem-nat-0-SBOX⟨0·1·2·4⟩ : WsL → ⟪ (Sw01 ∷ Sb0-1-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·1·2·4⟩ c4 = derive (Sw01 ∷ Sb0-1-2-4 ∷ []) (Sb1-0-2-4 ∷ Sw01 ∷ [])
  (re 1 1 (CS12 ∷ []) ∷
   rw⁻ 0 (q190 c4) ∷
   re 0 1 (Sb1-0-2-4 ∷ []) ∷ []) Eq.refl

private
  q191 : WsL → Eqn
  q191 c4 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wl0036 c4)

-- nat 0 SBOXd(0;1;2;4): 3 steps
lem-nat-0-SBOXd⟨0·1·2·4⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻0-1-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·1·2·4⟩ c4 = derive (Sw01 ∷ Sb⁻0-1-2-4 ∷ []) (Sb⁻1-0-2-4 ∷ Sw01 ∷ [])
  (re 1 1 (CS12⁻ ∷ []) ∷
   rw⁻ 0 (q191 c4) ∷
   re 0 1 (Sb⁻1-0-2-4 ∷ []) ∷ []) Eq.refl

private
  q192 : WsL → Eqn
  q192 c4 = eqn (Sw01 ∷ Bx0-1342 ∷ []) (Bx1-0342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1342⟩ c4)
  q193 : WsL → Eqn
  q193 c4 = eqn (Sw01 ∷ Toff234 ∷ []) (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff))
  q194 : WsL → Eqn
  q194 c4 = eqn (Sw01 ∷ Sb0-1-2-4 ∷ []) (Sb1-0-2-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·2·4⟩ c4)
  q195 : WsL → Eqn
  q195 c4 = eqn (Sw01 ∷ Sb⁻0-1-2-4 ∷ []) (Sb⁻1-0-2-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·2·4⟩ c4)

-- nat 0 SBOX(0;1;34;2): 7 steps
lem-nat-0-SBOX⟨0·1·34·2⟩ : WsL → ⟪ (Sw01 ∷ Sb0-1-34-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-34-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·1·34·2⟩ c4 = derive (Sw01 ∷ Sb0-1-34-2 ∷ []) (Sb1-0-34-2 ∷ Sw01 ∷ [])
  (re 1 1 (Bx0-1342 ∷ Toff234 ∷ Sb0-1-2-4 ∷ Toff234 ∷ Sb⁻0-1-2-4 ∷ []) ∷
   rw 0 (q192 c4) ∷
   rw 1 (q193 c4) ∷
   rw 2 (q194 c4) ∷
   rw 3 (q193 c4) ∷
   rw 4 (q195 c4) ∷
   re 0 5 (Sb1-0-34-2 ∷ []) ∷ []) Eq.refl

private
  q196 : WsL → Eqn
  q196 c4 = eqn (CZ01 ∷ Sw01 ∷ []) (Sw01 ∷ CZ01 ∷ []) (wl0130 c4)

-- nat 0 BOX(2;01): 3 steps
lem-nat-0-BOX⟨2·01⟩ : WsL → ⟪ (Sw01 ∷ Bx2-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-10 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·01⟩ c4 = derive (Sw01 ∷ Bx2-01 ∷ []) (Bx2-10 ∷ Sw01 ∷ [])
  (re 1 1 (CZ01 ∷ []) ∷
   rw⁻ 0 (q196 c4) ∷
   re 0 1 (Bx2-10 ∷ []) ∷ []) Eq.refl

private
  q197 : WsL → Eqn
  q197 c4 = eqn (Sw01 ∷ Toff024 ∷ []) (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4)
  q198 : WsL → Eqn
  q198 c4 = eqn (Sw01 ∷ Bx2-01 ∷ []) (Bx2-10 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·01⟩ c4)

-- nat 0 BOX(0;241): 8 steps
lem-nat-0-BOX⟨0·241⟩ : WsL → ⟪ (Sw01 ∷ Bx0-241 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-240 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·241⟩ c4 = derive (Sw01 ∷ Bx0-241 ∷ []) (Bx1-240 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) ∷
   rw 0 (q49 c4) ∷
   rw 1 (q197 c4) ∷
   rw 2 (q198 c4) ∷
   rw 3 (q197 c4) ∷
   rw 4 (q49 c4) ∷
   rw 5 (q198 c4) ∷
   re 0 6 (Bx1-240 ∷ []) ∷ []) Eq.refl

private
  q199 : WsL → Eqn
  q199 c4 = eqn (CCZ123 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ023 ∷ []) (wl0103 c4)
  q200 : WsL → Eqn
  q200 c4 = eqn (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) (wl0104 c4)
  q201 : WsL → Eqn
  q201 c4 = eqn (Sw01 ∷ Bx0-241 ∷ []) (Bx1-240 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·241⟩ c4)

-- nat 0 BOX(2;0341): 8 steps
lem-nat-0-BOX⟨2·0341⟩ : WsL → ⟪ (Sw01 ∷ Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·0341⟩ c4 = derive (Sw01 ∷ Bx2-0341 ∷ []) (Bx2-1340 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-241 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ []) ∷
   rw⁻ 0 (q199 c4) ∷
   rw 1 (q200 c4) ∷
   rw 2 (q201 c4) ∷
   rw 3 (q200 c4) ∷
   rw⁻ 4 (q199 c4) ∷
   rw 5 (q201 c4) ∷
   re 0 6 (Bx2-1340 ∷ []) ∷ []) Eq.refl

private
  q202 : WsL → Eqn
  q202 c4 = eqn (ι1 ∷ Sw34 ∷ []) (Sw34 ∷ ι1 ∷ []) (c₂ (iI ↑) (Swap ↑))
  q203 : WsL → Eqn
  q203 c4 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (c₂ (K ↑) (Swap))
  q204 : WsL → Eqn
  q204 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl0011 c4)
  q205 : WsL → Eqn
  q205 c4 = eqn (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) (wl0012 c4)
  q206 : WsL → Eqn
  q206 c4 = eqn (ι1 ∷ Sw23 ∷ []) (Sw23 ∷ ι1 ∷ []) (c₂ (iI ↑) (Swap))
  q207 : WsL → Eqn
  q207 c4 = eqn (Sw01 ∷ CS34 ∷ []) (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))
  q208 : WsL → Eqn
  q208 c4 = eqn (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) (wl0020 c4)
  q209 : WsL → Eqn
  q209 c4 = eqn (Sw01 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑))
  q210 : WsL → Eqn
  q210 c4 = eqn (Sw01 ∷ ι1 ∷ []) (ι1 ∷ Sw01 ∷ []) (wl0073 c4)
  q211 : WsL → Eqn
  q211 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl0015 c4)
  q212 : WsL → Eqn
  q212 c4 = eqn (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) (wl0016 c4)
  q213 : WsL → Eqn
  q213 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl0017 c4)
  q214 : WsL → Eqn
  q214 c4 = eqn (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ []) (wl0018 c4)
  q215 : WsL → Eqn
  q215 c4 = eqn (Sw12 ∷ ι1 ∷ []) (ι1 ∷ Sw12 ∷ []) (wl0074 c4)
  q216 : WsL → Eqn
  q216 c4 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι1 ∷ []) (wl0131 c4)

-- nat 0 TOFF134: 100 steps
lem-nat-0-TOFF134 : WsL → ⟪ (Sw01 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF134 c4 = derive (Sw01 ∷ Toff134 ∷ []) (Toff034 ∷ Sw01 ∷ [])
  (re 1 1 (Sw23 ∷ Toff124 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff123 ∷ Sw34 ∷ []) ∷
   re 3 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw⁻ 2 (q122 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (CS24 ∷ []) ∷
   rw⁻ 4 (q123 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (CS24⁻ ∷ []) ∷
   rw⁻ 6 (q123 c4) ∷
   rw⁻ 9 (q6 c4) ∷
   re 7 3 (CS14 ∷ []) ∷
   rw⁻ 8 (q122 c4) ∷
   rw⁻ 9 (q202 c4) ∷
   rw 10 (q6 c4) ∷
   rw⁻ 1 (q203 c4) ∷
   rw⁻ 2 (q204 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (CX13 ∷ []) ∷
   rw⁻ 4 (q205 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (CX13 ∷ []) ∷
   rw⁻ 6 (q9 c4) ∷
   rw⁻ 7 (q203 c4) ∷
   rw⁻ 8 (q206 c4) ∷
   rw 9 (q2 c4) ∷
   rw⁻ 0 (q118 c4) ∷
   rw 1 (q207 c4) ∷
   rw⁻ 2 (q208 c4) ∷
   rw 3 (q209 c4) ∷
   rw⁻ 4 (q208 c4) ∷
   re 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 5 (q77 c4) ∷
   rw⁻ 6 (q78 c4) ∷
   rw 7 (q77 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw⁻ 6 (q118 c4) ∷
   rw 7 (q210 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q211 c4) ∷
   re 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 4 (q212 c4) ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 5 (q2 c4) ∷
   re 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 6 (q11 c4) ∷
   rw⁻ 8 (q12 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw⁻ 10 (q12 c4) ∷
   rw⁻ 11 (q11 c4) ∷
   re 6 7 (CS04 ∷ []) ∷
   rw⁻ 7 (q1 c4) ∷
   rw⁻ 8 (q206 c4) ∷
   rw⁻ 1 (q105 c4) ∷
   rw⁻ 2 (q113 c4) ∷
   rw⁻ 3 (q213 c4) ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 (q105 c4) ∷
   rw⁻ 5 (q214 c4) ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 (q105 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q12 c4) ∷
   rw⁻ 8 (q83 c4) ∷
   rw 9 (q12 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q113 c4) ∷
   rw 9 (q215 c4) ∷
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
   rw⁻ 10 (q202 c4) ∷
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
   rw⁻ 11 (q206 c4) ∷
   rw⁻ 4 (q216 c4) ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 3 3 (Toff013 ∷ []) ∷
   re 2 3 (Toff014 ∷ []) ∷
   re 1 3 (Toff024 ∷ []) ∷
   re 0 3 (Toff034 ∷ []) ∷ []) Eq.refl

private
  q217 : WsL → Eqn
  q217 c4 = eqn (CS01 ∷ Sw01 ∷ []) (Sw01 ∷ CS01 ∷ []) (wl0132 c4)

-- nat 0 SBOX(2;0;1;4): 3 steps
lem-nat-0-SBOX⟨2·0·1·4⟩ : WsL → ⟪ (Sw01 ∷ Sb2-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-0-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·0·1·4⟩ c4 = derive (Sw01 ∷ Sb2-0-1-4 ∷ []) (Sb2-1-0-4 ∷ Sw01 ∷ [])
  (re 1 1 (CS01 ∷ []) ∷
   rw⁻ 0 (q217 c4) ∷
   re 0 1 (Sb2-1-0-4 ∷ []) ∷ []) Eq.refl

private
  q218 : WsL → Eqn
  q218 c4 = eqn (CS01⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS01⁻ ∷ []) (wl0133 c4)

-- nat 0 SBOXd(2;0;1;4): 3 steps
lem-nat-0-SBOXd⟨2·0·1·4⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-0-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·0·1·4⟩ c4 = derive (Sw01 ∷ Sb⁻2-0-1-4 ∷ []) (Sb⁻2-1-0-4 ∷ Sw01 ∷ [])
  (re 1 1 (CS01⁻ ∷ []) ∷
   rw⁻ 0 (q218 c4) ∷
   re 0 1 (Sb⁻2-1-0-4 ∷ []) ∷ []) Eq.refl

private
  q219 : WsL → Eqn
  q219 c4 = eqn (Sw01 ∷ Bx2-0341 ∷ []) (Bx2-1340 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0341⟩ c4)
  q220 : WsL → Eqn
  q220 c4 = eqn (Sw01 ∷ Toff134 ∷ []) (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4)
  q221 : WsL → Eqn
  q221 c4 = eqn (Sw01 ∷ Sb2-0-1-4 ∷ []) (Sb2-1-0-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·1·4⟩ c4)
  q222 : WsL → Eqn
  q222 c4 = eqn (Sw01 ∷ Sb⁻2-0-1-4 ∷ []) (Sb⁻2-1-0-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·0·1·4⟩ c4)

-- nat 0 SBOX(2;0;34;1): 7 steps
lem-nat-0-SBOX⟨2·0·34·1⟩ : WsL → ⟪ (Sw01 ∷ Sb2-0-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-34-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·0·34·1⟩ c4 = derive (Sw01 ∷ Sb2-0-34-1 ∷ []) (Sb2-1-34-0 ∷ Sw01 ∷ [])
  (re 1 1 (Bx2-0341 ∷ Toff134 ∷ Sb2-0-1-4 ∷ Toff134 ∷ Sb⁻2-0-1-4 ∷ []) ∷
   rw 0 (q219 c4) ∷
   rw 1 (q220 c4) ∷
   rw 2 (q221 c4) ∷
   rw 3 (q220 c4) ∷
   rw 4 (q222 c4) ∷
   re 0 5 (Sb2-1-34-0 ∷ []) ∷ []) Eq.refl

private
  q223 : WsL → Eqn
  q223 c4 = eqn (CS12 ∷ Sw12 ∷ []) (Sw12 ∷ CS12 ∷ []) (wl0134 c4)

-- nat 1 SBOX(0;2;1;4): 3 steps
lem-nat-1-SBOX⟨0·2·1·4⟩ : WsL → ⟪ (Sw12 ∷ Sb0-2-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-2-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·2·1·4⟩ c4 = derive (Sw12 ∷ Sb0-2-1-4 ∷ []) (Sb0-1-2-4 ∷ Sw12 ∷ [])
  (re 1 1 (CS12 ∷ []) ∷
   rw⁻ 0 (q223 c4) ∷
   re 0 1 (Sb0-1-2-4 ∷ []) ∷ []) Eq.refl

private
  q224 : WsL → Eqn
  q224 c4 = eqn (CS12⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS12⁻ ∷ []) (wl0135 c4)

-- nat 1 SBOXd(0;2;1;4): 3 steps
lem-nat-1-SBOXd⟨0·2·1·4⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻0-2-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-2-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·2·1·4⟩ c4 = derive (Sw12 ∷ Sb⁻0-2-1-4 ∷ []) (Sb⁻0-1-2-4 ∷ Sw12 ∷ [])
  (re 1 1 (CS12⁻ ∷ []) ∷
   rw⁻ 0 (q224 c4) ∷
   re 0 1 (Sb⁻0-1-2-4 ∷ []) ∷ []) Eq.refl

private
  q225 : WsL → Eqn
  q225 c4 = eqn (Sw12 ∷ Bx0-2341 ∷ []) (Bx0-1342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2341⟩ c4)
  q226 : WsL → Eqn
  q226 c4 = eqn (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) (wl0136 c4)
  q227 : WsL → Eqn
  q227 c4 = eqn (Sw12 ∷ Sb0-2-1-4 ∷ []) (Sb0-1-2-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·1·4⟩ c4)
  q228 : WsL → Eqn
  q228 c4 = eqn (Sw12 ∷ Sb⁻0-2-1-4 ∷ []) (Sb⁻0-1-2-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·2·1·4⟩ c4)

-- nat 1 SBOX(0;2;34;1): 7 steps
lem-nat-1-SBOX⟨0·2·34·1⟩ : WsL → ⟪ (Sw12 ∷ Sb0-2-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-34-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·2·34·1⟩ c4 = derive (Sw12 ∷ Sb0-2-34-1 ∷ []) (Sb0-1-34-2 ∷ Sw12 ∷ [])
  (re 1 1 (Bx0-2341 ∷ Toff134 ∷ Sb0-2-1-4 ∷ Toff134 ∷ Sb⁻0-2-1-4 ∷ []) ∷
   rw 0 (q225 c4) ∷
   rw 1 (q226 c4) ∷
   rw 2 (q227 c4) ∷
   rw 3 (q226 c4) ∷
   rw 4 (q228 c4) ∷
   re 0 5 (Sb0-1-34-2 ∷ []) ∷ []) Eq.refl

private
  q229 : WsL → Eqn
  q229 c4 = eqn (Sw12 ∷ CZ01 ∷ []) (CZ02 ∷ Sw12 ∷ []) (lem-nat-1-CZ01 c4)

-- nat 1 BOX(2;10): 3 steps
lem-nat-1-BOX⟨2·10⟩ : WsL → ⟪ (Sw12 ∷ Bx2-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-20 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·10⟩ c4 = derive (Sw12 ∷ Bx2-10 ∷ []) (Bx1-20 ∷ Sw12 ∷ [])
  (re 1 1 (CZ01 ∷ []) ∷
   rw 0 (q229 c4) ∷
   re 0 1 (Bx1-20 ∷ []) ∷ []) Eq.refl

private
  q230 : WsL → Eqn
  q230 c4 = eqn (CCZ124 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ124 ∷ []) (wl0078 c4)
  q231 : WsL → Eqn
  q231 c4 = eqn (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) (wl0095 c4)
  q232 : WsL → Eqn
  q232 c4 = eqn (Sw12 ∷ Bx2-10 ∷ []) (Bx1-20 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·10⟩ c4)

-- nat 1 BOX(1;240): 8 steps
lem-nat-1-BOX⟨1·240⟩ : WsL → ⟪ (Sw12 ∷ Bx1-240 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-140 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·240⟩ c4 = derive (Sw12 ∷ Bx1-240 ∷ []) (Bx2-140 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) ∷
   rw⁻ 0 (q230 c4) ∷
   rw 1 (q231 c4) ∷
   rw 2 (q232 c4) ∷
   rw 3 (q231 c4) ∷
   rw⁻ 4 (q230 c4) ∷
   rw 5 (q232 c4) ∷
   re 0 6 (Bx2-140 ∷ []) ∷ []) Eq.refl

private
  q233 : WsL → Eqn
  q233 c4 = eqn (CCZ123 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ123 ∷ []) (wl0111 c4)
  q234 : WsL → Eqn
  q234 c4 = eqn (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) (wl0112 c4)
  q235 : WsL → Eqn
  q235 c4 = eqn (Sw12 ∷ Bx1-240 ∷ []) (Bx2-140 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·240⟩ c4)

-- nat 1 BOX(2;1340): 8 steps
lem-nat-1-BOX⟨2·1340⟩ : WsL → ⟪ (Sw12 ∷ Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2340 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·1340⟩ c4 = derive (Sw12 ∷ Bx2-1340 ∷ []) (Bx1-2340 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-240 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ []) ∷
   rw⁻ 0 (q233 c4) ∷
   rw 1 (q234 c4) ∷
   rw 2 (q235 c4) ∷
   rw 3 (q234 c4) ∷
   rw⁻ 4 (q233 c4) ∷
   rw 5 (q235 c4) ∷
   re 0 6 (Bx1-2340 ∷ []) ∷ []) Eq.refl
