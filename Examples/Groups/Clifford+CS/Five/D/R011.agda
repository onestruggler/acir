{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R011 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0014 ; wl0017 ; wl0018 ; wl0020 ; wl0023 ; wl0024 ; wl0025 ; wl0026 ; wl0037 ; wl0038 ; wl0043 ; wl0044 ; wl0046 ; wl0047 ; wl0056 ; wl0062 ; wl0063 ; wl0064 ; wl0065 ; wl0066 ; wl0078 ; wl0088 ; wl0090 ; wl0095 ; wl0096 ; wl0097 ; wl0098 ; wl0100 ; wl0101 ; wl0102 ; wl0107 ; wl0111 ; wl0112 ; wl0113 ; wl0114 ; wl0119 ; wl0120 ; wl0125 ; wl0126 ; wl0127 ; wl0128 ; wl0129 ; wl0136 ; wl0140 ; wl0144 ; wl0146 ; wl0147 ; wl0148 ; wl0149 ; wl0150 ; wl0151)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF024 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF034 ; lem-nat-2-TOFF102 ; lem-nat-2-TOFF103 ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-TOFF013 ; lem-nat-3-TOFF014 ; lem-nat-3-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF301 ; lem-nat-1-TOFF302 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023 ; lem-nat-3-CZ14 ; lem-nat-3-TOFF203)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ014 ; lem-nat-0-TOFF014 ; lem-nat-0-TOFF104 ; lem-nat-1-TOFF104 ; lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-1-TOFF013 ; lem-nat-2-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-TOFF024 ; lem-nat-1-TOFF023 ; lem-nat-2-CCZ014 ; lem-nat-2-CZ02 ; lem-nat-2-CZ03 ; lem-nat-2-TOFF214 ; lem-nat-3-TOFF103)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-BOXd⟨1·0423⟩ ; lem-nat-1-BOXd⟨2·03⟩ ; lem-nat-1-BOXd⟨2·0413⟩ ; lem-nat-1-CS01 ; lem-nat-1-CS02 ; lem-nat-1-CZ01 ; lem-nat-2-TOFF314 ; lem-nat-3-BOXd⟨0·1423⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-BOX⟨0·12⟩ ; lem-nat-0-BOX⟨2·03⟩ ; lem-nat-0-BOX⟨2·13⟩ ; lem-nat-0-SBOX⟨0·1·3·2⟩ ; lem-nat-0-SBOX⟨1·0·3·2⟩ ; lem-nat-0-SBOXd⟨0·1·3·2⟩ ; lem-nat-0-SBOXd⟨1·0·3·2⟩ ; lem-nat-1-BOX⟨3·02⟩ ; lem-nat-1-CSd02 ; lem-nat-1-SBOX⟨1·0·3·2⟩ ; lem-nat-1-SBOX⟨2·0·3·1⟩ ; lem-nat-1-SBOXd⟨1·0·3·2⟩ ; lem-nat-1-SBOXd⟨2·0·3·1⟩ ; lem-nat-2-BOX⟨3·01⟩ ; lem-nat-2-CS02 ; lem-nat-2-CSd02 ; lem-nat-2-SBOX⟨1·0·2·3⟩ ; lem-nat-2-SBOXd⟨1·0·2·3⟩ ; lem-nat-2-TOFF014 ; lem-nat-2-TOFF124 ; lem-nat-3-SBOX⟨0·1·3·2⟩ ; lem-nat-3-SBOX⟨0·1·4·2⟩ ; lem-nat-3-SBOX⟨1·0·2·4⟩ ; lem-nat-3-SBOXd⟨0·1·3·2⟩ ; lem-nat-3-SBOXd⟨0·1·4·2⟩ ; lem-nat-3-SBOXd⟨1·0·2·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨1·02⟩ ; lem-nat-1-BOX⟨1·02⟩ ; lem-nat-1-BOX⟨2·01⟩ ; lem-nat-1-CSd01 ; lem-nat-1-TOFF034 ; lem-nat-3-TOFF024)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-1-BOX⟨1·34⟩ ; lem-nat-1-BOX⟨2·34⟩ ; lem-nat-2-CS03 ; lem-nat-2-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-TOFF124 ; lem-nat-1-BOX⟨2·3140⟩ ; lem-nat-1-SBOX⟨2·0·3·4⟩ ; lem-nat-1-SBOX⟨2·3·0·4⟩ ; lem-nat-1-SBOXd⟨2·0·3·4⟩ ; lem-nat-2-BOX⟨1·03⟩ ; lem-nat-2-SBOX⟨1·0·3·4⟩ ; lem-nat-2-SBOXd⟨1·0·3·4⟩)

private
  q1 : WsL → Eqn
  q1 c4 = eqn (CS03⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS03⁻ ∷ []) (wl0023 c4)

-- nat 1 SBOXd(2;3;0;4): 3 steps
lem-nat-1-SBOXd⟨2·3·0·4⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-0-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·3·0·4⟩ c4 = derive (Sw12 ∷ Sb⁻2-3-0-4 ∷ []) (Sb⁻1-3-0-4 ∷ Sw12 ∷ [])
  (re 1 1 (CS03⁻ ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 0 1 (Sb⁻1-3-0-4 ∷ []) ∷ []) Eq.refl

private
  q2 : WsL → Eqn
  q2 c4 = eqn (Sw12 ∷ Bx2-3140 ∷ []) (Bx1-3240 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3140⟩ c4)
  q3 : WsL → Eqn
  q3 c4 = eqn (Sw12 ∷ Toff014 ∷ []) (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4)
  q4 : WsL → Eqn
  q4 c4 = eqn (Sw12 ∷ Sb2-3-0-4 ∷ []) (Sb1-3-0-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·3·0·4⟩ c4)
  q5 : WsL → Eqn
  q5 c4 = eqn (Sw12 ∷ Sb⁻2-3-0-4 ∷ []) (Sb⁻1-3-0-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·3·0·4⟩ c4)

-- nat 1 SBOX(2;3;14;0): 7 steps
lem-nat-1-SBOX⟨2·3·14·0⟩ : WsL → ⟪ (Sw12 ∷ Sb2-3-14-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-24-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·3·14·0⟩ c4 = derive (Sw12 ∷ Sb2-3-14-0 ∷ []) (Sb1-3-24-0 ∷ Sw12 ∷ [])
  (re 1 1 (Bx2-3140 ∷ Toff014 ∷ Sb2-3-0-4 ∷ Toff014 ∷ Sb⁻2-3-0-4 ∷ []) ∷
   rw 0 (q2 c4) ∷
   rw 1 (q3 c4) ∷
   rw 2 (q4 c4) ∷
   rw 3 (q3 c4) ∷
   rw 4 (q5 c4) ∷
   re 0 5 (Sb1-3-24-0 ∷ []) ∷ []) Eq.refl

private
  q6 : WsL → Eqn
  q6 c4 = eqn (Sw23 ∷ CZ02 ∷ []) (CZ03 ∷ Sw23 ∷ []) (lem-nat-2-CZ02 c4)

-- nat 2 BOX(1;20): 3 steps
lem-nat-2-BOX⟨1·20⟩ : WsL → ⟪ (Sw23 ∷ Bx1-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-30 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·20⟩ c4 = derive (Sw23 ∷ Bx1-20 ∷ []) (Bx1-30 ∷ Sw23 ∷ [])
  (re 1 1 (CZ02 ∷ []) ∷
   rw 0 (q6 c4) ∷
   re 0 1 (Bx1-30 ∷ []) ∷ []) Eq.refl

private
  q7 : WsL → Eqn
  q7 c4 = eqn (Sw23 ∷ CCZ124 ∷ []) (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4)
  q8 : WsL → Eqn
  q8 c4 = eqn (Sw23 ∷ Toff214 ∷ []) (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4)
  q9 : WsL → Eqn
  q9 c4 = eqn (Sw23 ∷ Bx1-20 ∷ []) (Bx1-30 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·20⟩ c4)

-- nat 2 BOX(2;140): 8 steps
lem-nat-2-BOX⟨2·140⟩ : WsL → ⟪ (Sw23 ∷ Bx2-140 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-140 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·140⟩ c4 = derive (Sw23 ∷ Bx2-140 ∷ []) (Bx3-140 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-20 ∷ Toff214 ∷ CCZ124 ∷ Bx1-20 ∷ []) ∷
   rw 0 (q7 c4) ∷
   rw 1 (q8 c4) ∷
   rw 2 (q9 c4) ∷
   rw 3 (q8 c4) ∷
   rw 4 (q7 c4) ∷
   rw 5 (q9 c4) ∷
   re 0 6 (Bx3-140 ∷ []) ∷ []) Eq.refl

private
  q10 : WsL → Eqn
  q10 c4 = eqn (CCZ123 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ123 ∷ []) (wl0113 c4)
  q11 : WsL → Eqn
  q11 c4 = eqn (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ []) (wl0114 c4)
  q12 : WsL → Eqn
  q12 c4 = eqn (Sw23 ∷ Bx2-140 ∷ []) (Bx3-140 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·140⟩ c4)

-- nat 2 BOX(1;2340): 8 steps
lem-nat-2-BOX⟨1·2340⟩ : WsL → ⟪ (Sw23 ∷ Bx1-2340 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3240 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·2340⟩ c4 = derive (Sw23 ∷ Bx1-2340 ∷ []) (Bx1-3240 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-140 ∷ Toff123 ∷ CCZ123 ∷ Bx2-140 ∷ []) ∷
   rw⁻ 0 (q10 c4) ∷
   rw 1 (q11 c4) ∷
   rw 2 (q12 c4) ∷
   rw 3 (q11 c4) ∷
   rw⁻ 4 (q10 c4) ∷
   rw 5 (q12 c4) ∷
   re 0 6 (Bx1-3240 ∷ []) ∷ []) Eq.refl

private
  q13 : WsL → Eqn
  q13 c4 = eqn (Sw23 ∷ CS02 ∷ []) (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4)

-- nat 2 SBOX(1;2;0;4): 3 steps
lem-nat-2-SBOX⟨1·2·0·4⟩ : WsL → ⟪ (Sw23 ∷ Sb1-2-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-0-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·2·0·4⟩ c4 = derive (Sw23 ∷ Sb1-2-0-4 ∷ []) (Sb1-3-0-4 ∷ Sw23 ∷ [])
  (re 1 1 (CS02 ∷ []) ∷
   rw 0 (q13 c4) ∷
   re 0 1 (Sb1-3-0-4 ∷ []) ∷ []) Eq.refl

private
  q14 : WsL → Eqn
  q14 c4 = eqn (Sw23 ∷ CS02⁻ ∷ []) (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 c4)

-- nat 2 SBOXd(1;2;0;4): 3 steps
lem-nat-2-SBOXd⟨1·2·0·4⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-2-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-0-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·2·0·4⟩ c4 = derive (Sw23 ∷ Sb⁻1-2-0-4 ∷ []) (Sb⁻1-3-0-4 ∷ Sw23 ∷ [])
  (re 1 1 (CS02⁻ ∷ []) ∷
   rw 0 (q14 c4) ∷
   re 0 1 (Sb⁻1-3-0-4 ∷ []) ∷ []) Eq.refl

private
  q15 : WsL → Eqn
  q15 c4 = eqn (Sw23 ∷ Bx1-2340 ∷ []) (Bx1-3240 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·2340⟩ c4)
  q16 : WsL → Eqn
  q16 c4 = eqn (Sw23 ∷ Toff034 ∷ []) (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4)
  q17 : WsL → Eqn
  q17 c4 = eqn (Sw23 ∷ Sb1-2-0-4 ∷ []) (Sb1-3-0-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·2·0·4⟩ c4)
  q18 : WsL → Eqn
  q18 c4 = eqn (Sw23 ∷ Sb⁻1-2-0-4 ∷ []) (Sb⁻1-3-0-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·2·0·4⟩ c4)

-- nat 2 SBOX(1;2;34;0): 7 steps
lem-nat-2-SBOX⟨1·2·34·0⟩ : WsL → ⟪ (Sw23 ∷ Sb1-2-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-24-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·2·34·0⟩ c4 = derive (Sw23 ∷ Sb1-2-34-0 ∷ []) (Sb1-3-24-0 ∷ Sw23 ∷ [])
  (re 1 1 (Bx1-2340 ∷ Toff034 ∷ Sb1-2-0-4 ∷ Toff034 ∷ Sb⁻1-2-0-4 ∷ []) ∷
   rw 0 (q15 c4) ∷
   rw 1 (q16 c4) ∷
   rw 2 (q17 c4) ∷
   rw 3 (q16 c4) ∷
   rw 4 (q18 c4) ∷
   re 0 5 (Sb1-3-24-0 ∷ []) ∷ []) Eq.refl

private
  q19 : WsL → Eqn
  q19 c4 = eqn (Sw23 ∷ CZ03 ∷ []) (CZ02 ∷ Sw23 ∷ []) (lem-nat-2-CZ03 c4)

-- nat 2 BOX(1;30): 3 steps
lem-nat-2-BOX⟨1·30⟩ : WsL → ⟪ (Sw23 ∷ Bx1-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-20 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·30⟩ c4 = derive (Sw23 ∷ Bx1-30 ∷ []) (Bx1-20 ∷ Sw23 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw 0 (q19 c4) ∷
   re 0 1 (Bx1-20 ∷ []) ∷ []) Eq.refl

private
  q20 : WsL → Eqn
  q20 c4 = eqn (Sw23 ∷ CCZ134 ∷ []) (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4)
  q21 : WsL → Eqn
  q21 c4 = eqn (Sw23 ∷ Toff314 ∷ []) (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4)
  q22 : WsL → Eqn
  q22 c4 = eqn (Sw23 ∷ Bx1-30 ∷ []) (Bx1-20 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·30⟩ c4)

-- nat 2 BOX(3;140): 8 steps
lem-nat-2-BOX⟨3·140⟩ : WsL → ⟪ (Sw23 ∷ Bx3-140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-140 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·140⟩ c4 = derive (Sw23 ∷ Bx3-140 ∷ []) (Bx2-140 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-30 ∷ Toff314 ∷ CCZ134 ∷ Bx1-30 ∷ []) ∷
   rw 0 (q20 c4) ∷
   rw 1 (q21 c4) ∷
   rw 2 (q22 c4) ∷
   rw 3 (q21 c4) ∷
   rw 4 (q20 c4) ∷
   rw 5 (q22 c4) ∷
   re 0 6 (Bx2-140 ∷ []) ∷ []) Eq.refl

private
  q23 : WsL → Eqn
  q23 c4 = eqn (Sw23 ∷ Bx3-140 ∷ []) (Bx2-140 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·140⟩ c4)

-- nat 2 BOX(1;3240): 8 steps
lem-nat-2-BOX⟨1·3240⟩ : WsL → ⟪ (Sw23 ∷ Bx1-3240 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2340 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·3240⟩ c4 = derive (Sw23 ∷ Bx1-3240 ∷ []) (Bx1-2340 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-140 ∷ Toff123 ∷ CCZ123 ∷ Bx3-140 ∷ []) ∷
   rw⁻ 0 (q10 c4) ∷
   rw 1 (q11 c4) ∷
   rw 2 (q23 c4) ∷
   rw 3 (q11 c4) ∷
   rw⁻ 4 (q10 c4) ∷
   rw 5 (q23 c4) ∷
   re 0 6 (Bx1-2340 ∷ []) ∷ []) Eq.refl

private
  q24 : WsL → Eqn
  q24 c4 = eqn (Sw23 ∷ CS03 ∷ []) (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4)

-- nat 2 SBOX(1;3;0;4): 3 steps
lem-nat-2-SBOX⟨1·3·0·4⟩ : WsL → ⟪ (Sw23 ∷ Sb1-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-0-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·3·0·4⟩ c4 = derive (Sw23 ∷ Sb1-3-0-4 ∷ []) (Sb1-2-0-4 ∷ Sw23 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   rw 0 (q24 c4) ∷
   re 0 1 (Sb1-2-0-4 ∷ []) ∷ []) Eq.refl

private
  q25 : WsL → Eqn
  q25 c4 = eqn (Sw23 ∷ CS03⁻ ∷ []) (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 c4)

-- nat 2 SBOXd(1;3;0;4): 3 steps
lem-nat-2-SBOXd⟨1·3·0·4⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-0-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·3·0·4⟩ c4 = derive (Sw23 ∷ Sb⁻1-3-0-4 ∷ []) (Sb⁻1-2-0-4 ∷ Sw23 ∷ [])
  (re 1 1 (CS03⁻ ∷ []) ∷
   rw 0 (q25 c4) ∷
   re 0 1 (Sb⁻1-2-0-4 ∷ []) ∷ []) Eq.refl

private
  q26 : WsL → Eqn
  q26 c4 = eqn (Sw23 ∷ Bx1-3240 ∷ []) (Bx1-2340 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·3240⟩ c4)
  q27 : WsL → Eqn
  q27 c4 = eqn (Sw23 ∷ Toff024 ∷ []) (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4)
  q28 : WsL → Eqn
  q28 c4 = eqn (Sw23 ∷ Sb1-3-0-4 ∷ []) (Sb1-2-0-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·0·4⟩ c4)
  q29 : WsL → Eqn
  q29 c4 = eqn (Sw23 ∷ Sb⁻1-3-0-4 ∷ []) (Sb⁻1-2-0-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·3·0·4⟩ c4)

-- nat 2 SBOX(1;3;24;0): 7 steps
lem-nat-2-SBOX⟨1·3·24·0⟩ : WsL → ⟪ (Sw23 ∷ Sb1-3-24-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-34-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·3·24·0⟩ c4 = derive (Sw23 ∷ Sb1-3-24-0 ∷ []) (Sb1-2-34-0 ∷ Sw23 ∷ [])
  (re 1 1 (Bx1-3240 ∷ Toff024 ∷ Sb1-3-0-4 ∷ Toff024 ∷ Sb⁻1-3-0-4 ∷ []) ∷
   rw 0 (q26 c4) ∷
   rw 1 (q27 c4) ∷
   rw 2 (q28 c4) ∷
   rw 3 (q27 c4) ∷
   rw 4 (q29 c4) ∷
   re 0 5 (Sb1-2-34-0 ∷ []) ∷ []) Eq.refl

private
  q30 : WsL → Eqn
  q30 c4 = eqn (Sw34 ∷ CCZ014 ∷ []) (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4)
  q31 : WsL → Eqn
  q31 c4 = eqn (Sw34 ∷ Toff104 ∷ []) (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4)
  q32 : WsL → Eqn
  q32 c4 = eqn (Bx0-12 ∷ Sw34 ∷ []) (Sw34 ∷ Bx0-12 ∷ []) (c₃ (CZ ↑) (Swap))

-- nat 3 BOX(1;042): 8 steps
lem-nat-3-BOX⟨1·042⟩ : WsL → ⟪ (Sw34 ∷ Bx1-042 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-032 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·042⟩ c4 = derive (Sw34 ∷ Bx1-042 ∷ []) (Bx1-032 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-12 ∷ Toff104 ∷ CCZ014 ∷ Bx0-12 ∷ []) ∷
   rw 0 (q30 c4) ∷
   rw 1 (q31 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 3 (q31 c4) ∷
   rw 4 (q30 c4) ∷
   rw⁻ 5 (q32 c4) ∷
   re 0 6 (Bx1-032 ∷ []) ∷ []) Eq.refl

private
  q33 : WsL → Eqn
  q33 c4 = eqn (Sw34 ∷ CCZ013 ∷ []) (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4)
  q34 : WsL → Eqn
  q34 c4 = eqn (Sw34 ∷ Toff013 ∷ []) (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4)
  q35 : WsL → Eqn
  q35 c4 = eqn (Sw34 ∷ Bx1-042 ∷ []) (Bx1-032 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·042⟩ c4)

-- nat 3 BOX(0;1342): 8 steps
lem-nat-3-BOX⟨0·1342⟩ : WsL → ⟪ (Sw34 ∷ Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·1342⟩ c4 = derive (Sw34 ∷ Bx0-1342 ∷ []) (Bx0-1432 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-042 ∷ Toff013 ∷ CCZ013 ∷ Bx1-042 ∷ []) ∷
   rw 0 (q33 c4) ∷
   rw 1 (q34 c4) ∷
   rw 2 (q35 c4) ∷
   rw 3 (q34 c4) ∷
   rw 4 (q33 c4) ∷
   rw 5 (q35 c4) ∷
   re 0 6 (Bx0-1432 ∷ []) ∷ []) Eq.refl

private
  q36 : WsL → Eqn
  q36 c4 = eqn (CCZ013 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ013 ∷ []) (wl0100 c4)
  q37 : WsL → Eqn
  q37 c4 = eqn (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) (wl0102 c4)
  q38 : WsL → Eqn
  q38 c4 = eqn (Sw01 ∷ Bx0-12 ∷ []) (Bx1-02 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·12⟩ c4)

-- nat 0 BOX(1;032): 8 steps
lem-nat-0-BOX⟨1·032⟩ : WsL → ⟪ (Sw01 ∷ Bx1-032 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-132 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·032⟩ c4 = derive (Sw01 ∷ Bx1-032 ∷ []) (Bx0-132 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) ∷
   rw⁻ 0 (q36 c4) ∷
   rw 1 (q37 c4) ∷
   rw 2 (q38 c4) ∷
   rw 3 (q37 c4) ∷
   rw⁻ 4 (q36 c4) ∷
   rw 5 (q38 c4) ∷
   re 0 6 (Bx0-132 ∷ []) ∷ []) Eq.refl

private
  q39 : WsL → Eqn
  q39 c4 = eqn (Sw01 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4)
  q40 : WsL → Eqn
  q40 c4 = eqn (Sw01 ∷ Toff014 ∷ []) (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4)
  q41 : WsL → Eqn
  q41 c4 = eqn (Sw01 ∷ Bx1-032 ∷ []) (Bx0-132 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·032⟩ c4)

-- nat 0 BOX(0;1432): 8 steps
lem-nat-0-BOX⟨0·1432⟩ : WsL → ⟪ (Sw01 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·1432⟩ c4 = derive (Sw01 ∷ Bx0-1432 ∷ []) (Bx1-0432 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) ∷
   rw 0 (q39 c4) ∷
   rw 1 (q40 c4) ∷
   rw 2 (q41 c4) ∷
   rw 3 (q40 c4) ∷
   rw 4 (q39 c4) ∷
   rw 5 (q41 c4) ∷
   re 0 6 (Bx1-0432 ∷ []) ∷ []) Eq.refl

private
  q42 : WsL → Eqn
  q42 c4 = eqn (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4)
  q43 : WsL → Eqn
  q43 c4 = eqn (Sw12 ∷ Toff013 ∷ []) (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4)
  q44 : WsL → Eqn
  q44 c4 = eqn (Sw12 ∷ Bx1-02 ∷ []) (Bx2-01 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·02⟩ c4)

-- nat 1 BOX(0;132): 8 steps
lem-nat-1-BOX⟨0·132⟩ : WsL → ⟪ (Sw12 ∷ Bx0-132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-231 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·132⟩ c4 = derive (Sw12 ∷ Bx0-132 ∷ []) (Bx0-231 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-02 ∷ Toff013 ∷ CCZ013 ∷ Bx1-02 ∷ []) ∷
   rw 0 (q42 c4) ∷
   rw 1 (q43 c4) ∷
   rw 2 (q44 c4) ∷
   rw 3 (q43 c4) ∷
   rw 4 (q42 c4) ∷
   rw 5 (q44 c4) ∷
   re 0 6 (Bx0-231 ∷ []) ∷ []) Eq.refl

private
  q45 : WsL → Eqn
  q45 c4 = eqn (Sw12 ∷ CCZ014 ∷ []) (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4)
  q46 : WsL → Eqn
  q46 c4 = eqn (Sw12 ∷ Toff104 ∷ []) (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4)
  q47 : WsL → Eqn
  q47 c4 = eqn (Sw12 ∷ Bx0-132 ∷ []) (Bx0-231 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·132⟩ c4)

-- nat 1 BOX(1;0432): 8 steps
lem-nat-1-BOX⟨1·0432⟩ : WsL → ⟪ (Sw12 ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·0432⟩ c4 = derive (Sw12 ∷ Bx1-0432 ∷ []) (Bx2-0431 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-132 ∷ Toff104 ∷ CCZ014 ∷ Bx0-132 ∷ []) ∷
   rw 0 (q45 c4) ∷
   rw 1 (q46 c4) ∷
   rw 2 (q47 c4) ∷
   rw 3 (q46 c4) ∷
   rw 4 (q45 c4) ∷
   rw 5 (q47 c4) ∷
   re 0 6 (Bx2-0431 ∷ []) ∷ []) Eq.refl

private
  q48 : WsL → Eqn
  q48 c4 = eqn (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) (wl0101 c4)
  q49 : WsL → Eqn
  q49 c4 = eqn (Sw01 ∷ Bx1-02 ∷ []) (Bx0-12 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·02⟩ c4)

-- nat 0 BOX(0;132): 8 steps
lem-nat-0-BOX⟨0·132⟩ : WsL → ⟪ (Sw01 ∷ Bx0-132 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-032 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·132⟩ c4 = derive (Sw01 ∷ Bx0-132 ∷ []) (Bx1-032 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-02 ∷ Toff013 ∷ CCZ013 ∷ Bx1-02 ∷ []) ∷
   rw⁻ 0 (q36 c4) ∷
   rw 1 (q48 c4) ∷
   rw 2 (q49 c4) ∷
   rw 3 (q48 c4) ∷
   rw⁻ 4 (q36 c4) ∷
   rw 5 (q49 c4) ∷
   re 0 6 (Bx1-032 ∷ []) ∷ []) Eq.refl

private
  q50 : WsL → Eqn
  q50 c4 = eqn (Sw01 ∷ Toff104 ∷ []) (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4)
  q51 : WsL → Eqn
  q51 c4 = eqn (Sw01 ∷ Bx0-132 ∷ []) (Bx1-032 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·132⟩ c4)

-- nat 0 BOX(1;0432): 8 steps
lem-nat-0-BOX⟨1·0432⟩ : WsL → ⟪ (Sw01 ∷ Bx1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·0432⟩ c4 = derive (Sw01 ∷ Bx1-0432 ∷ []) (Bx0-1432 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-132 ∷ Toff104 ∷ CCZ014 ∷ Bx0-132 ∷ []) ∷
   rw 0 (q39 c4) ∷
   rw 1 (q50 c4) ∷
   rw 2 (q51 c4) ∷
   rw 3 (q50 c4) ∷
   rw 4 (q39 c4) ∷
   rw 5 (q51 c4) ∷
   re 0 6 (Bx0-1432 ∷ []) ∷ []) Eq.refl

private
  q52 : WsL → Eqn
  q52 c4 = eqn (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4)
  q53 : WsL → Eqn
  q53 c4 = eqn (Sw12 ∷ Toff023 ∷ []) (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4)
  q54 : WsL → Eqn
  q54 c4 = eqn (Sw12 ∷ Bx2-01 ∷ []) (Bx1-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·01⟩ c4)

-- nat 1 BOX(0;231): 8 steps
lem-nat-1-BOX⟨0·231⟩ : WsL → ⟪ (Sw12 ∷ Bx0-231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-132 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·231⟩ c4 = derive (Sw12 ∷ Bx0-231 ∷ []) (Bx0-132 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) ∷
   rw 0 (q52 c4) ∷
   rw 1 (q53 c4) ∷
   rw 2 (q54 c4) ∷
   rw 3 (q53 c4) ∷
   rw 4 (q52 c4) ∷
   rw 5 (q54 c4) ∷
   re 0 6 (Bx0-132 ∷ []) ∷ []) Eq.refl

private
  q55 : WsL → Eqn
  q55 c4 = eqn (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4)
  q56 : WsL → Eqn
  q56 c4 = eqn (Sw12 ∷ Toff204 ∷ []) (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4)
  q57 : WsL → Eqn
  q57 c4 = eqn (Sw12 ∷ Bx0-231 ∷ []) (Bx0-132 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·231⟩ c4)

-- nat 1 BOX(2;0431): 8 steps
lem-nat-1-BOX⟨2·0431⟩ : WsL → ⟪ (Sw12 ∷ Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·0431⟩ c4 = derive (Sw12 ∷ Bx2-0431 ∷ []) (Bx1-0432 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-231 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ []) ∷
   rw 0 (q55 c4) ∷
   rw 1 (q56 c4) ∷
   rw 2 (q57 c4) ∷
   rw 3 (q56 c4) ∷
   rw 4 (q55 c4) ∷
   rw 5 (q57 c4) ∷
   re 0 6 (Bx1-0432 ∷ []) ∷ []) Eq.refl

private
  q58 : WsL → Eqn
  q58 c4 = eqn (CX41 ∷ Sw12 ∷ []) (Sw12 ∷ CX42 ∷ []) (wl0125 c4)
  q59 : WsL → Eqn
  q59 c4 = eqn (CX42 ∷ Sw23 ∷ []) (Sw23 ∷ CX43 ∷ []) (wl0147 c4)
  q60 : WsL → Eqn
  q60 c4 = eqn (Toff102 ∷ CX43 ∷ []) (CX43 ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (CX₁₀))
  q61 : WsL → Eqn
  q61 c4 = eqn (CX43 ∷ Sw23 ∷ []) (Sw23 ∷ CX42 ∷ []) (wl0148 c4)
  q62 : WsL → Eqn
  q62 c4 = eqn (CX42 ∷ Sw12 ∷ []) (Sw12 ∷ CX41 ∷ []) (wl0149 c4)

-- comm CX41 TOFF203: 7 steps
lem-comm-CX41-TOFF203 : WsL → ⟪ (CX41 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CX41 ∷ []) ⟫ʷ
lem-comm-CX41-TOFF203 c4 = derive (CX41 ∷ Toff203 ∷ []) (Toff203 ∷ CX41 ∷ [])
  (re 1 1 (Sw12 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw12 ∷ []) ∷
   rw 0 (q58 c4) ∷
   rw 1 (q59 c4) ∷
   rw⁻ 2 (q60 c4) ∷
   rw 3 (q61 c4) ∷
   rw 4 (q62 c4) ∷
   re 0 5 (Toff203 ∷ []) ∷ []) Eq.refl

private
  q63 : WsL → Eqn
  q63 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 c4)
  q64 : WsL → Eqn
  q64 c4 = eqn (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) (wl0043 c4)
  q65 : WsL → Eqn
  q65 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 c4)
  q66 : WsL → Eqn
  q66 c4 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (CS • CS • CS))

-- resp CSd13 at 2: 4 steps
lem-resp-CSd13-at-2 : WsL → ⟪ (CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CSd13-at-2 c4 = derive (CS13⁻ ∷ []) (Sw12 ∷ Sw01 ∷ CS23⁻ ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q63 c4) ∷
   rw 0 (q64 c4) ∷
   rw⁻ 2 (q65 c4) ∷
   rw⁻ 1 (q66 c4) ∷ []) Eq.refl

private
  q67 : WsL → Eqn
  q67 c4 = eqn (Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap))
  q68 : WsL → Eqn
  q68 c4 = eqn (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) (wl0014 c4)
  q69 : WsL → Eqn
  q69 c4 = eqn (Sw01 ∷ Sw34 ∷ []) (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑))
  q70 : WsL → Eqn
  q70 c4 = eqn (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) (wl0020 c4)

-- resp CX04 at 2: 12 steps
lem-resp-CX04-at-2 : WsL → ⟪ (CX04 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX14 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX04-at-2 c4 = derive (CX04 ∷ []) (Sw12 ∷ Sw01 ∷ CX14 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q63 c4) ∷
   re 0 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q67 c4) ∷
   rw 1 (q68 c4) ∷
   rw⁻ 0 (q67 c4) ∷
   re 1 3 (CX04 ∷ []) ∷
   rw⁻ 2 (q65 c4) ∷
   re 1 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw⁻ 3 (q69 c4) ∷
   rw 2 (q70 c4) ∷
   rw⁻ 1 (q69 c4) ∷
   re 2 3 (CX14 ∷ []) ∷ []) Eq.refl

private
  q71 : WsL → Eqn
  q71 c4 = eqn (CZ13 ∷ Sw12 ∷ []) (Sw12 ∷ CZ23 ∷ []) (wl0026 c4)

-- nat 1 BOX(1;23): 3 steps
lem-nat-1-BOX⟨1·23⟩ : WsL → ⟪ (Sw12 ∷ Bx1-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-13 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·23⟩ c4 = derive (Sw12 ∷ Bx1-23 ∷ []) (Bx2-13 ∷ Sw12 ∷ [])
  (re 1 1 (CZ23 ∷ []) ∷
   rw⁻ 0 (q71 c4) ∷
   re 0 1 (Bx2-13 ∷ []) ∷ []) Eq.refl

private
  q72 : WsL → Eqn
  q72 c4 = eqn (CCZ124 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ124 ∷ []) (wl0078 c4)
  q73 : WsL → Eqn
  q73 c4 = eqn (Sw12 ∷ Toff214 ∷ []) (Toff124 ∷ Sw12 ∷ []) (wl0126 c4)
  q74 : WsL → Eqn
  q74 c4 = eqn (Sw12 ∷ Bx1-23 ∷ []) (Bx2-13 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·23⟩ c4)

-- nat 1 BOX(2;143): 8 steps
lem-nat-1-BOX⟨2·143⟩ : WsL → ⟪ (Sw12 ∷ Bx2-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-243 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·143⟩ c4 = derive (Sw12 ∷ Bx2-143 ∷ []) (Bx1-243 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-23 ∷ Toff214 ∷ CCZ124 ∷ Bx1-23 ∷ []) ∷
   rw⁻ 0 (q72 c4) ∷
   rw 1 (q73 c4) ∷
   rw 2 (q74 c4) ∷
   rw 3 (q73 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   rw 5 (q74 c4) ∷
   re 0 6 (Bx1-243 ∷ []) ∷ []) Eq.refl

private
  q75 : WsL → Eqn
  q75 c4 = eqn (CCZ012 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ012 ∷ []) (wl0037 c4)
  q76 : WsL → Eqn
  q76 c4 = eqn (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) (wl0047 c4)
  q77 : WsL → Eqn
  q77 c4 = eqn (Sw12 ∷ Bx2-143 ∷ []) (Bx1-243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·143⟩ c4)

-- nat 1 BOX(1;2043): 8 steps
lem-nat-1-BOX⟨1·2043⟩ : WsL → ⟪ (Sw12 ∷ Bx1-2043 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1043 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·2043⟩ c4 = derive (Sw12 ∷ Bx1-2043 ∷ []) (Bx2-1043 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-143 ∷ Toff102 ∷ CCZ012 ∷ Bx2-143 ∷ []) ∷
   rw⁻ 0 (q75 c4) ∷
   rw 1 (q76 c4) ∷
   rw 2 (q77 c4) ∷
   rw 3 (q76 c4) ∷
   rw⁻ 4 (q75 c4) ∷
   rw 5 (q77 c4) ∷
   re 0 6 (Bx2-1043 ∷ []) ∷ []) Eq.refl

private
  q78 : WsL → Eqn
  q78 c4 = eqn (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4)
  q79 : WsL → Eqn
  q79 c4 = eqn (Sw01 ∷ Toff124 ∷ []) (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4)
  q80 : WsL → Eqn
  q80 c4 = eqn (Sw01 ∷ Bx2-13 ∷ []) (Bx2-03 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·13⟩ c4)

-- nat 0 BOX(1;243): 8 steps
lem-nat-0-BOX⟨1·243⟩ : WsL → ⟪ (Sw01 ∷ Bx1-243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-243 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·243⟩ c4 = derive (Sw01 ∷ Bx1-243 ∷ []) (Bx0-243 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-13 ∷ Toff124 ∷ CCZ124 ∷ Bx2-13 ∷ []) ∷
   rw 0 (q78 c4) ∷
   rw 1 (q79 c4) ∷
   rw 2 (q80 c4) ∷
   rw 3 (q79 c4) ∷
   rw 4 (q78 c4) ∷
   rw 5 (q80 c4) ∷
   re 0 6 (Bx0-243 ∷ []) ∷ []) Eq.refl

private
  q81 : WsL → Eqn
  q81 c4 = eqn (CCZ012 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ012 ∷ []) (wl0096 c4)
  q82 : WsL → Eqn
  q82 c4 = eqn (Sw01 ∷ Toff201 ∷ []) (Toff201 ∷ Sw01 ∷ []) (wl0107 c4)
  q83 : WsL → Eqn
  q83 c4 = eqn (Sw01 ∷ Bx1-243 ∷ []) (Bx0-243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·243⟩ c4)

-- nat 0 BOX(2;1043): 8 steps
lem-nat-0-BOX⟨2·1043⟩ : WsL → ⟪ (Sw01 ∷ Bx2-1043 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·1043⟩ c4 = derive (Sw01 ∷ Bx2-1043 ∷ []) (Bx2-0143 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-243 ∷ Toff201 ∷ CCZ012 ∷ Bx1-243 ∷ []) ∷
   rw⁻ 0 (q81 c4) ∷
   rw 1 (q82 c4) ∷
   rw 2 (q83 c4) ∷
   rw 3 (q82 c4) ∷
   rw⁻ 4 (q81 c4) ∷
   rw 5 (q83 c4) ∷
   re 0 6 (Bx2-0143 ∷ []) ∷ []) Eq.refl

private
  q84 : WsL → Eqn
  q84 c4 = eqn (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4)
  q85 : WsL → Eqn
  q85 c4 = eqn (Sw01 ∷ Toff024 ∷ []) (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4)
  q86 : WsL → Eqn
  q86 c4 = eqn (Sw01 ∷ Bx2-03 ∷ []) (Bx2-13 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·03⟩ c4)

-- nat 0 BOX(0;243): 8 steps
lem-nat-0-BOX⟨0·243⟩ : WsL → ⟪ (Sw01 ∷ Bx0-243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-243 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·243⟩ c4 = derive (Sw01 ∷ Bx0-243 ∷ []) (Bx1-243 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) ∷
   rw 0 (q84 c4) ∷
   rw 1 (q85 c4) ∷
   rw 2 (q86 c4) ∷
   rw 3 (q85 c4) ∷
   rw 4 (q84 c4) ∷
   rw 5 (q86 c4) ∷
   re 0 6 (Bx1-243 ∷ []) ∷ []) Eq.refl

private
  q87 : WsL → Eqn
  q87 c4 = eqn (Sw01 ∷ Bx0-243 ∷ []) (Bx1-243 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·243⟩ c4)

-- nat 0 BOX(2;0143): 8 steps
lem-nat-0-BOX⟨2·0143⟩ : WsL → ⟪ (Sw01 ∷ Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1043 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·0143⟩ c4 = derive (Sw01 ∷ Bx2-0143 ∷ []) (Bx2-1043 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ []) ∷
   rw⁻ 0 (q81 c4) ∷
   rw 1 (q82 c4) ∷
   rw 2 (q87 c4) ∷
   rw 3 (q82 c4) ∷
   rw⁻ 4 (q81 c4) ∷
   rw 5 (q87 c4) ∷
   re 0 6 (Bx2-1043 ∷ []) ∷ []) Eq.refl

private
  q88 : WsL → Eqn
  q88 c4 = eqn (Sw12 ∷ Sb2-0-3-1 ∷ []) (Sb1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·1⟩ c4)
  q89 : WsL → Eqn
  q89 c4 = eqn (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) (wl0064 c4)
  q90 : WsL → Eqn
  q90 c4 = eqn (Sw12 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻1-0-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·1⟩ c4)
  q91 : WsL → Eqn
  q91 c4 = eqn (Sw12 ∷ Bx⁻2-0413 ∷ []) (Bx⁻1-0423 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·0413⟩ c4)

-- nat 1 SBOXd(2;0;41;3): 7 steps
lem-nat-1-SBOXd⟨2·0·41·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-42-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·0·41·3⟩ c4 = derive (Sw12 ∷ Sb⁻2-0-41-3 ∷ []) (Sb⁻1-0-42-3 ∷ Sw12 ∷ [])
  (re 1 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw 0 (q88 c4) ∷
   rw 1 (q89 c4) ∷
   rw 2 (q90 c4) ∷
   rw 3 (q89 c4) ∷
   rw 4 (q91 c4) ∷
   re 0 5 (Sb⁻1-0-42-3 ∷ []) ∷ []) Eq.refl

-- nat 2 SBOX(1;0;3;2): 3 steps
lem-nat-2-SBOX⟨1·0·3·2⟩ : WsL → ⟪ (Sw23 ∷ Sb1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·0·3·2⟩ c4 = derive (Sw23 ∷ Sb1-0-3-2 ∷ []) (Sb1-0-2-3 ∷ Sw23 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   rw 0 (q24 c4) ∷
   re 0 1 (Sb1-0-2-3 ∷ []) ∷ []) Eq.refl

-- nat 2 SBOXd(1;0;3;2): 3 steps
lem-nat-2-SBOXd⟨1·0·3·2⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-0-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·3·2⟩ c4 = derive (Sw23 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻1-0-2-3 ∷ Sw23 ∷ [])
  (re 1 1 (CS03⁻ ∷ []) ∷
   rw 0 (q25 c4) ∷
   re 0 1 (Sb⁻1-0-2-3 ∷ []) ∷ []) Eq.refl

-- nat 2 BOXd(1;03): 3 steps
lem-nat-2-BOXd⟨1·03⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-02 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·03⟩ c4 = derive (Sw23 ∷ Bx⁻1-03 ∷ []) (Bx⁻1-02 ∷ Sw23 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw 0 (q19 c4) ∷
   re 0 1 (Bx⁻1-02 ∷ []) ∷ []) Eq.refl

private
  q92 : WsL → Eqn
  q92 c4 = eqn (Sw23 ∷ Bx⁻1-03 ∷ []) (Bx⁻1-02 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·03⟩ c4)
  q93 : WsL → Eqn
  q93 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4)
  q94 : WsL → Eqn
  q94 c4 = eqn (Sw23 ∷ Toff012 ∷ []) (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4)

-- nat 2 BOXd(0;123): 8 steps
lem-nat-2-BOXd⟨0·123⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-132 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·123⟩ c4 = derive (Sw23 ∷ Bx⁻0-123 ∷ []) (Bx⁻0-132 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻1-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   rw 0 (q92 c4) ∷
   rw 1 (q93 c4) ∷
   rw 2 (q94 c4) ∷
   rw 3 (q92 c4) ∷
   rw 4 (q94 c4) ∷
   rw 5 (q93 c4) ∷
   re 0 6 (Bx⁻0-132 ∷ []) ∷ []) Eq.refl

private
  q95 : WsL → Eqn
  q95 c4 = eqn (Sw23 ∷ Bx⁻0-123 ∷ []) (Bx⁻0-132 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·123⟩ c4)
  q96 : WsL → Eqn
  q96 c4 = eqn (Sw23 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4)
  q97 : WsL → Eqn
  q97 c4 = eqn (Sw23 ∷ Toff104 ∷ []) (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4)

-- nat 2 BOXd(1;0423): 8 steps
lem-nat-2-BOXd⟨1·0423⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0432 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·0423⟩ c4 = derive (Sw23 ∷ Bx⁻1-0423 ∷ []) (Bx⁻1-0432 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻0-123 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-123 ∷ Toff104 ∷ CCZ014 ∷ []) ∷
   rw 0 (q95 c4) ∷
   rw 1 (q96 c4) ∷
   rw 2 (q97 c4) ∷
   rw 3 (q95 c4) ∷
   rw 4 (q97 c4) ∷
   rw 5 (q96 c4) ∷
   re 0 6 (Bx⁻1-0432 ∷ []) ∷ []) Eq.refl

private
  q98 : WsL → Eqn
  q98 c4 = eqn (Sw23 ∷ Sb1-0-3-2 ∷ []) (Sb1-0-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·3·2⟩ c4)
  q99 : WsL → Eqn
  q99 c4 = eqn (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) (wl0144 c4)
  q100 : WsL → Eqn
  q100 c4 = eqn (Sw23 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻1-0-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·3·2⟩ c4)
  q101 : WsL → Eqn
  q101 c4 = eqn (Sw23 ∷ Bx⁻1-0423 ∷ []) (Bx⁻1-0432 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·0423⟩ c4)

-- nat 2 SBOXd(1;0;42;3): 7 steps
lem-nat-2-SBOXd⟨1·0·42·3⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-43-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·42·3⟩ c4 = derive (Sw23 ∷ Sb⁻1-0-42-3 ∷ []) (Sb⁻1-0-43-2 ∷ Sw23 ∷ [])
  (re 1 1 (Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Toff324 ∷ Bx⁻1-0423 ∷ []) ∷
   rw 0 (q98 c4) ∷
   rw 1 (q99 c4) ∷
   rw 2 (q100 c4) ∷
   rw 3 (q99 c4) ∷
   rw 4 (q101 c4) ∷
   re 0 5 (Sb⁻1-0-43-2 ∷ []) ∷ []) Eq.refl

private
  q102 : WsL → Eqn
  q102 c4 = eqn (Sb1-0-2-3 ∷ Sw34 ∷ []) (Sw34 ∷ Sb1-0-2-3 ∷ []) (c₃ (Swap ↑ • CS • Swap ↑) (Swap))

-- nat 3 SBOX(1;0;2;3): 2 steps
lem-nat-3-SBOX⟨1·0·2·3⟩ : WsL → ⟪ (Sw34 ∷ Sb1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·0·2·3⟩ c4 = derive (Sw34 ∷ Sb1-0-2-3 ∷ []) (Sb1-0-2-4 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q102 c4) ∷
   re 0 1 (Sb1-0-2-4 ∷ []) ∷ []) Eq.refl

private
  q103 : WsL → Eqn
  q103 c4 = eqn (Sb⁻1-0-2-3 ∷ Sw34 ∷ []) (Sw34 ∷ Sb⁻1-0-2-3 ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (Swap))

-- nat 3 SBOXd(1;0;2;3): 2 steps
lem-nat-3-SBOXd⟨1·0·2·3⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·0·2·3⟩ c4 = derive (Sw34 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻1-0-2-4 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q103 c4) ∷
   re 0 1 (Sb⁻1-0-2-4 ∷ []) ∷ []) Eq.refl

private
  q104 : WsL → Eqn
  q104 c4 = eqn (Bx⁻1-02 ∷ Sw34 ∷ []) (Sw34 ∷ Bx⁻1-02 ∷ []) (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))

-- nat 3 BOXd(0;132): 8 steps
lem-nat-3-BOXd⟨0·132⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻0-132 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-142 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·132⟩ c4 = derive (Sw34 ∷ Bx⁻0-132 ∷ []) (Bx⁻0-142 ∷ Sw34 ∷ [])
  (re 1 1 (Bx⁻1-02 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-02 ∷ Toff013 ∷ CCZ013 ∷ []) ∷
   rw⁻ 0 (q104 c4) ∷
   rw 1 (q33 c4) ∷
   rw 2 (q34 c4) ∷
   rw⁻ 3 (q104 c4) ∷
   rw 4 (q34 c4) ∷
   rw 5 (q33 c4) ∷
   re 0 6 (Bx⁻0-142 ∷ []) ∷ []) Eq.refl

private
  q105 : WsL → Eqn
  q105 c4 = eqn (Sw34 ∷ Bx⁻0-132 ∷ []) (Bx⁻0-142 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·132⟩ c4)

-- nat 3 BOXd(1;0432): 8 steps
lem-nat-3-BOXd⟨1·0432⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0342 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·0432⟩ c4 = derive (Sw34 ∷ Bx⁻1-0432 ∷ []) (Bx⁻1-0342 ∷ Sw34 ∷ [])
  (re 1 1 (Bx⁻0-132 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-132 ∷ Toff104 ∷ CCZ014 ∷ []) ∷
   rw 0 (q105 c4) ∷
   rw 1 (q30 c4) ∷
   rw 2 (q31 c4) ∷
   rw 3 (q105 c4) ∷
   rw 4 (q31 c4) ∷
   rw 5 (q30 c4) ∷
   re 0 6 (Bx⁻1-0342 ∷ []) ∷ []) Eq.refl

private
  q106 : WsL → Eqn
  q106 c4 = eqn (Sw34 ∷ Sb1-0-2-3 ∷ []) (Sb1-0-2-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·2·3⟩ c4)
  q107 : WsL → Eqn
  q107 c4 = eqn (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) (wl0128 c4)
  q108 : WsL → Eqn
  q108 c4 = eqn (Sw34 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻1-0-2-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·2·3⟩ c4)
  q109 : WsL → Eqn
  q109 c4 = eqn (Sw34 ∷ Bx⁻1-0432 ∷ []) (Bx⁻1-0342 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·0432⟩ c4)

-- nat 3 SBOXd(1;0;43;2): 7 steps
lem-nat-3-SBOXd⟨1·0·43·2⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-34-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·0·43·2⟩ c4 = derive (Sw34 ∷ Sb⁻1-0-43-2 ∷ []) (Sb⁻1-0-34-2 ∷ Sw34 ∷ [])
  (re 1 1 (Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ Toff234 ∷ Bx⁻1-0432 ∷ []) ∷
   rw 0 (q106 c4) ∷
   rw 1 (q107 c4) ∷
   rw 2 (q108 c4) ∷
   rw 3 (q107 c4) ∷
   rw 4 (q109 c4) ∷
   re 0 5 (Sb⁻1-0-34-2 ∷ []) ∷ []) Eq.refl

-- nat 2 SBOX(1;0;2;4): 3 steps
lem-nat-2-SBOX⟨1·0·2·4⟩ : WsL → ⟪ (Sw23 ∷ Sb1-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·0·2·4⟩ c4 = derive (Sw23 ∷ Sb1-0-2-4 ∷ []) (Sb1-0-3-4 ∷ Sw23 ∷ [])
  (re 1 1 (CS02 ∷ []) ∷
   rw 0 (q13 c4) ∷
   re 0 1 (Sb1-0-3-4 ∷ []) ∷ []) Eq.refl

-- nat 2 SBOXd(1;0;2;4): 3 steps
lem-nat-2-SBOXd⟨1·0·2·4⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·2·4⟩ c4 = derive (Sw23 ∷ Sb⁻1-0-2-4 ∷ []) (Sb⁻1-0-3-4 ∷ Sw23 ∷ [])
  (re 1 1 (CS02⁻ ∷ []) ∷
   rw 0 (q14 c4) ∷
   re 0 1 (Sb⁻1-0-3-4 ∷ []) ∷ []) Eq.refl

-- nat 2 BOXd(1;02): 3 steps
lem-nat-2-BOXd⟨1·02⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-03 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·02⟩ c4 = derive (Sw23 ∷ Bx⁻1-02 ∷ []) (Bx⁻1-03 ∷ Sw23 ∷ [])
  (re 1 1 (CZ02 ∷ []) ∷
   rw 0 (q6 c4) ∷
   re 0 1 (Bx⁻1-03 ∷ []) ∷ []) Eq.refl

private
  q110 : WsL → Eqn
  q110 c4 = eqn (Sw23 ∷ Bx⁻1-02 ∷ []) (Bx⁻1-03 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·02⟩ c4)
  q111 : WsL → Eqn
  q111 c4 = eqn (Sw23 ∷ Toff014 ∷ []) (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4)

-- nat 2 BOXd(0;142): 8 steps
lem-nat-2-BOXd⟨0·142⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-142 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-143 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·142⟩ c4 = derive (Sw23 ∷ Bx⁻0-142 ∷ []) (Bx⁻0-143 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻1-02 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-02 ∷ Toff014 ∷ CCZ014 ∷ []) ∷
   rw 0 (q110 c4) ∷
   rw 1 (q96 c4) ∷
   rw 2 (q111 c4) ∷
   rw 3 (q110 c4) ∷
   rw 4 (q111 c4) ∷
   rw 5 (q96 c4) ∷
   re 0 6 (Bx⁻0-143 ∷ []) ∷ []) Eq.refl

private
  q112 : WsL → Eqn
  q112 c4 = eqn (Sw23 ∷ Bx⁻0-142 ∷ []) (Bx⁻0-143 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·142⟩ c4)
  q113 : WsL → Eqn
  q113 c4 = eqn (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4)
  q114 : WsL → Eqn
  q114 c4 = eqn (Sw23 ∷ Toff103 ∷ []) (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4)

-- nat 2 BOXd(1;0342): 8 steps
lem-nat-2-BOXd⟨1·0342⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0243 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·0342⟩ c4 = derive (Sw23 ∷ Bx⁻1-0342 ∷ []) (Bx⁻1-0243 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻0-142 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-142 ∷ Toff103 ∷ CCZ013 ∷ []) ∷
   rw 0 (q112 c4) ∷
   rw 1 (q113 c4) ∷
   rw 2 (q114 c4) ∷
   rw 3 (q112 c4) ∷
   rw 4 (q114 c4) ∷
   rw 5 (q113 c4) ∷
   re 0 6 (Bx⁻1-0243 ∷ []) ∷ []) Eq.refl

private
  q115 : WsL → Eqn
  q115 c4 = eqn (Sw23 ∷ Sb1-0-2-4 ∷ []) (Sb1-0-3-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·2·4⟩ c4)
  q116 : WsL → Eqn
  q116 c4 = eqn (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) (wl0127 c4)
  q117 : WsL → Eqn
  q117 c4 = eqn (Sw23 ∷ Sb⁻1-0-2-4 ∷ []) (Sb⁻1-0-3-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·2·4⟩ c4)
  q118 : WsL → Eqn
  q118 c4 = eqn (Sw23 ∷ Bx⁻1-0342 ∷ []) (Bx⁻1-0243 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·0342⟩ c4)

-- nat 2 SBOXd(1;0;34;2): 7 steps
lem-nat-2-SBOXd⟨1·0·34·2⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-0-34-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-24-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·34·2⟩ c4 = derive (Sw23 ∷ Sb⁻1-0-34-2 ∷ []) (Sb⁻1-0-24-3 ∷ Sw23 ∷ [])
  (re 1 1 (Sb1-0-2-4 ∷ Toff234 ∷ Sb⁻1-0-2-4 ∷ Toff234 ∷ Bx⁻1-0342 ∷ []) ∷
   rw 0 (q115 c4) ∷
   rw 1 (q116 c4) ∷
   rw 2 (q117 c4) ∷
   rw 3 (q116 c4) ∷
   rw 4 (q118 c4) ∷
   re 0 5 (Sb⁻1-0-24-3 ∷ []) ∷ []) Eq.refl

private
  q119 : WsL → Eqn
  q119 c4 = eqn (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) (wl0010 c4)

-- nat 1 SBOX(1;0;3;4): 3 steps
lem-nat-1-SBOX⟨1·0·3·4⟩ : WsL → ⟪ (Sw12 ∷ Sb1-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-3-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·0·3·4⟩ c4 = derive (Sw12 ∷ Sb1-0-3-4 ∷ []) (Sb2-0-3-4 ∷ Sw12 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   rw⁻ 0 (q119 c4) ∷
   re 0 1 (Sb2-0-3-4 ∷ []) ∷ []) Eq.refl

-- nat 1 SBOXd(1;0;3;4): 3 steps
lem-nat-1-SBOXd⟨1·0·3·4⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-3-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·0·3·4⟩ c4 = derive (Sw12 ∷ Sb⁻1-0-3-4 ∷ []) (Sb⁻2-0-3-4 ∷ Sw12 ∷ [])
  (re 1 1 (CS03⁻ ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 0 1 (Sb⁻2-0-3-4 ∷ []) ∷ []) Eq.refl

private
  q120 : WsL → Eqn
  q120 c4 = eqn (CZ03 ∷ Sw12 ∷ []) (Sw12 ∷ CZ03 ∷ []) (wl0098 c4)

-- nat 1 BOXd(1;03): 3 steps
lem-nat-1-BOXd⟨1·03⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻1-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-03 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·03⟩ c4 = derive (Sw12 ∷ Bx⁻1-03 ∷ []) (Bx⁻2-03 ∷ Sw12 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw⁻ 0 (q120 c4) ∷
   re 0 1 (Bx⁻2-03 ∷ []) ∷ []) Eq.refl

private
  q121 : WsL → Eqn
  q121 c4 = eqn (Sw12 ∷ Bx⁻1-03 ∷ []) (Bx⁻2-03 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·03⟩ c4)

-- nat 1 BOXd(0;143): 8 steps
lem-nat-1-BOXd⟨0·143⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻0-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-243 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·143⟩ c4 = derive (Sw12 ∷ Bx⁻0-143 ∷ []) (Bx⁻0-243 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻1-03 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-03 ∷ Toff014 ∷ CCZ014 ∷ []) ∷
   rw 0 (q121 c4) ∷
   rw 1 (q45 c4) ∷
   rw 2 (q3 c4) ∷
   rw 3 (q121 c4) ∷
   rw 4 (q3 c4) ∷
   rw 5 (q45 c4) ∷
   re 0 6 (Bx⁻0-243 ∷ []) ∷ []) Eq.refl

private
  q122 : WsL → Eqn
  q122 c4 = eqn (Sw12 ∷ Bx⁻0-143 ∷ []) (Bx⁻0-243 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·143⟩ c4)

-- nat 1 BOXd(1;0243): 8 steps
lem-nat-1-BOXd⟨1·0243⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0143 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·0243⟩ c4 = derive (Sw12 ∷ Bx⁻1-0243 ∷ []) (Bx⁻2-0143 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻0-143 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-143 ∷ Toff102 ∷ CCZ012 ∷ []) ∷
   rw 0 (q122 c4) ∷
   rw⁻ 1 (q75 c4) ∷
   rw 2 (q76 c4) ∷
   rw 3 (q122 c4) ∷
   rw 4 (q76 c4) ∷
   rw⁻ 5 (q75 c4) ∷
   re 0 6 (Bx⁻2-0143 ∷ []) ∷ []) Eq.refl

private
  q123 : WsL → Eqn
  q123 c4 = eqn (Sw12 ∷ Sb1-0-3-4 ∷ []) (Sb2-0-3-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·3·4⟩ c4)
  q124 : WsL → Eqn
  q124 c4 = eqn (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) (wl0063 c4)
  q125 : WsL → Eqn
  q125 c4 = eqn (Sw12 ∷ Sb⁻1-0-3-4 ∷ []) (Sb⁻2-0-3-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·3·4⟩ c4)
  q126 : WsL → Eqn
  q126 c4 = eqn (Sw12 ∷ Bx⁻1-0243 ∷ []) (Bx⁻2-0143 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·0243⟩ c4)

-- nat 1 SBOXd(1;0;24;3): 7 steps
lem-nat-1-SBOXd⟨1·0·24·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-0-24-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-14-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·0·24·3⟩ c4 = derive (Sw12 ∷ Sb⁻1-0-24-3 ∷ []) (Sb⁻2-0-14-3 ∷ Sw12 ∷ [])
  (re 1 1 (Sb1-0-3-4 ∷ Toff324 ∷ Sb⁻1-0-3-4 ∷ Toff324 ∷ Bx⁻1-0243 ∷ []) ∷
   rw 0 (q123 c4) ∷
   rw 1 (q124 c4) ∷
   rw 2 (q125 c4) ∷
   rw 3 (q124 c4) ∷
   rw 4 (q126 c4) ∷
   re 0 5 (Sb⁻2-0-14-3 ∷ []) ∷ []) Eq.refl

private
  q127 : WsL → Eqn
  q127 c4 = eqn (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) (wl0038 c4)

-- nat 1 BOXd(0;123): 8 steps
lem-nat-1-BOXd⟨0·123⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻0-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-213 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·123⟩ c4 = derive (Sw12 ∷ Bx⁻0-123 ∷ []) (Bx⁻0-213 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻1-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻1-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   rw 0 (q121 c4) ∷
   rw⁻ 1 (q75 c4) ∷
   rw 2 (q127 c4) ∷
   rw 3 (q121 c4) ∷
   rw 4 (q127 c4) ∷
   rw⁻ 5 (q75 c4) ∷
   re 0 6 (Bx⁻0-213 ∷ []) ∷ []) Eq.refl

private
  q128 : WsL → Eqn
  q128 c4 = eqn (Sw12 ∷ Bx⁻0-123 ∷ []) (Bx⁻0-213 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·123⟩ c4)

-- nat 1 BOXd(1;0423): 8 steps
lem-nat-1-BOXd⟨1·0423⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0413 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·0423⟩ c4 = derive (Sw12 ∷ Bx⁻1-0423 ∷ []) (Bx⁻2-0413 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻0-123 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-123 ∷ Toff104 ∷ CCZ014 ∷ []) ∷
   rw 0 (q128 c4) ∷
   rw 1 (q45 c4) ∷
   rw 2 (q46 c4) ∷
   rw 3 (q128 c4) ∷
   rw 4 (q46 c4) ∷
   rw 5 (q45 c4) ∷
   re 0 6 (Bx⁻2-0413 ∷ []) ∷ []) Eq.refl

private
  q129 : WsL → Eqn
  q129 c4 = eqn (Sw12 ∷ Sb1-0-3-2 ∷ []) (Sb2-0-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·3·2⟩ c4)
  q130 : WsL → Eqn
  q130 c4 = eqn (Sw12 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻2-0-3-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·3·2⟩ c4)
  q131 : WsL → Eqn
  q131 c4 = eqn (Sw12 ∷ Bx⁻1-0423 ∷ []) (Bx⁻2-0413 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·0423⟩ c4)

-- nat 1 SBOXd(1;0;42;3): 7 steps
lem-nat-1-SBOXd⟨1·0·42·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-41-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·0·42·3⟩ c4 = derive (Sw12 ∷ Sb⁻1-0-42-3 ∷ []) (Sb⁻2-0-41-3 ∷ Sw12 ∷ [])
  (re 1 1 (Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Toff324 ∷ Bx⁻1-0423 ∷ []) ∷
   rw 0 (q129 c4) ∷
   rw 1 (q124 c4) ∷
   rw 2 (q130 c4) ∷
   rw 3 (q124 c4) ∷
   rw 4 (q131 c4) ∷
   re 0 5 (Sb⁻2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q132 : WsL → Eqn
  q132 c4 = eqn (Sw12 ∷ Bx⁻2-03 ∷ []) (Bx⁻1-03 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·03⟩ c4)
  q133 : WsL → Eqn
  q133 c4 = eqn (Sw12 ∷ Toff024 ∷ []) (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4)

-- nat 1 BOXd(0;243): 8 steps
lem-nat-1-BOXd⟨0·243⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻0-243 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-143 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨0·243⟩ c4 = derive (Sw12 ∷ Bx⁻0-243 ∷ []) (Bx⁻0-143 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻2-03 ∷ CCZ024 ∷ Toff024 ∷ Bx⁻2-03 ∷ Toff024 ∷ CCZ024 ∷ []) ∷
   rw 0 (q132 c4) ∷
   rw 1 (q55 c4) ∷
   rw 2 (q133 c4) ∷
   rw 3 (q132 c4) ∷
   rw 4 (q133 c4) ∷
   rw 5 (q55 c4) ∷
   re 0 6 (Bx⁻0-143 ∷ []) ∷ []) Eq.refl

private
  q134 : WsL → Eqn
  q134 c4 = eqn (Sw12 ∷ Bx⁻0-243 ∷ []) (Bx⁻0-143 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨0·243⟩ c4)
  q135 : WsL → Eqn
  q135 c4 = eqn (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) (wl0044 c4)

-- nat 1 BOXd(2;0143): 8 steps
lem-nat-1-BOXd⟨2·0143⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0243 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·0143⟩ c4 = derive (Sw12 ∷ Bx⁻2-0143 ∷ []) (Bx⁻1-0243 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻0-243 ∷ CCZ012 ∷ Toff201 ∷ Bx⁻0-243 ∷ Toff201 ∷ CCZ012 ∷ []) ∷
   rw 0 (q134 c4) ∷
   rw⁻ 1 (q75 c4) ∷
   rw 2 (q135 c4) ∷
   rw 3 (q134 c4) ∷
   rw 4 (q135 c4) ∷
   rw⁻ 5 (q75 c4) ∷
   re 0 6 (Bx⁻1-0243 ∷ []) ∷ []) Eq.refl

private
  q136 : WsL → Eqn
  q136 c4 = eqn (Sw12 ∷ Sb2-0-3-4 ∷ []) (Sb1-0-3-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·4⟩ c4)
  q137 : WsL → Eqn
  q137 c4 = eqn (Sw12 ∷ Sb⁻2-0-3-4 ∷ []) (Sb⁻1-0-3-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·4⟩ c4)
  q138 : WsL → Eqn
  q138 c4 = eqn (Sw12 ∷ Bx⁻2-0143 ∷ []) (Bx⁻1-0243 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·0143⟩ c4)

-- nat 1 SBOXd(2;0;14;3): 7 steps
lem-nat-1-SBOXd⟨2·0·14·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-0-14-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-24-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·0·14·3⟩ c4 = derive (Sw12 ∷ Sb⁻2-0-14-3 ∷ []) (Sb⁻1-0-24-3 ∷ Sw12 ∷ [])
  (re 1 1 (Sb2-0-3-4 ∷ Toff314 ∷ Sb⁻2-0-3-4 ∷ Toff314 ∷ Bx⁻2-0143 ∷ []) ∷
   rw 0 (q136 c4) ∷
   rw 1 (q89 c4) ∷
   rw 2 (q137 c4) ∷
   rw 3 (q89 c4) ∷
   rw 4 (q138 c4) ∷
   re 0 5 (Sb⁻1-0-24-3 ∷ []) ∷ []) Eq.refl

private
  q139 : WsL → Eqn
  q139 c4 = eqn (Sw23 ∷ Toff013 ∷ []) (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4)

-- nat 2 BOXd(0;132): 8 steps
lem-nat-2-BOXd⟨0·132⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-132 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-123 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·132⟩ c4 = derive (Sw23 ∷ Bx⁻0-132 ∷ []) (Bx⁻0-123 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻1-02 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-02 ∷ Toff013 ∷ CCZ013 ∷ []) ∷
   rw 0 (q110 c4) ∷
   rw 1 (q113 c4) ∷
   rw 2 (q139 c4) ∷
   rw 3 (q110 c4) ∷
   rw 4 (q139 c4) ∷
   rw 5 (q113 c4) ∷
   re 0 6 (Bx⁻0-123 ∷ []) ∷ []) Eq.refl

private
  q140 : WsL → Eqn
  q140 c4 = eqn (Sw23 ∷ Bx⁻0-132 ∷ []) (Bx⁻0-123 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·132⟩ c4)

-- nat 2 BOXd(1;0432): 8 steps
lem-nat-2-BOXd⟨1·0432⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-0432 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0423 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·0432⟩ c4 = derive (Sw23 ∷ Bx⁻1-0432 ∷ []) (Bx⁻1-0423 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻0-132 ∷ CCZ014 ∷ Toff104 ∷ Bx⁻0-132 ∷ Toff104 ∷ CCZ014 ∷ []) ∷
   rw 0 (q140 c4) ∷
   rw 1 (q96 c4) ∷
   rw 2 (q97 c4) ∷
   rw 3 (q140 c4) ∷
   rw 4 (q97 c4) ∷
   rw 5 (q96 c4) ∷
   re 0 6 (Bx⁻1-0423 ∷ []) ∷ []) Eq.refl

private
  q141 : WsL → Eqn
  q141 c4 = eqn (Sw23 ∷ Sb1-0-2-3 ∷ []) (Sb1-0-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·2·3⟩ c4)
  q142 : WsL → Eqn
  q142 c4 = eqn (Sw23 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻1-0-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·2·3⟩ c4)
  q143 : WsL → Eqn
  q143 c4 = eqn (Sw23 ∷ Bx⁻1-0432 ∷ []) (Bx⁻1-0423 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·0432⟩ c4)

-- nat 2 SBOXd(1;0;43;2): 7 steps
lem-nat-2-SBOXd⟨1·0·43·2⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-42-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·43·2⟩ c4 = derive (Sw23 ∷ Sb⁻1-0-43-2 ∷ []) (Sb⁻1-0-42-3 ∷ Sw23 ∷ [])
  (re 1 1 (Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ Toff234 ∷ Bx⁻1-0432 ∷ []) ∷
   rw 0 (q141 c4) ∷
   rw 1 (q116 c4) ∷
   rw 2 (q142 c4) ∷
   rw 3 (q116 c4) ∷
   rw 4 (q143 c4) ∷
   re 0 5 (Sb⁻1-0-42-3 ∷ []) ∷ []) Eq.refl

-- nat 2 BOXd(0;143): 8 steps
lem-nat-2-BOXd⟨0·143⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻0-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-142 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨0·143⟩ c4 = derive (Sw23 ∷ Bx⁻0-143 ∷ []) (Bx⁻0-142 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻1-03 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-03 ∷ Toff014 ∷ CCZ014 ∷ []) ∷
   rw 0 (q92 c4) ∷
   rw 1 (q96 c4) ∷
   rw 2 (q111 c4) ∷
   rw 3 (q92 c4) ∷
   rw 4 (q111 c4) ∷
   rw 5 (q96 c4) ∷
   re 0 6 (Bx⁻0-142 ∷ []) ∷ []) Eq.refl

private
  q144 : WsL → Eqn
  q144 c4 = eqn (Sw23 ∷ Bx⁻0-143 ∷ []) (Bx⁻0-142 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨0·143⟩ c4)
  q145 : WsL → Eqn
  q145 c4 = eqn (Sw23 ∷ Toff102 ∷ []) (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4)

-- nat 2 BOXd(1;0243): 8 steps
lem-nat-2-BOXd⟨1·0243⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0342 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·0243⟩ c4 = derive (Sw23 ∷ Bx⁻1-0243 ∷ []) (Bx⁻1-0342 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻0-143 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-143 ∷ Toff102 ∷ CCZ012 ∷ []) ∷
   rw 0 (q144 c4) ∷
   rw 1 (q93 c4) ∷
   rw 2 (q145 c4) ∷
   rw 3 (q144 c4) ∷
   rw 4 (q145 c4) ∷
   rw 5 (q93 c4) ∷
   re 0 6 (Bx⁻1-0342 ∷ []) ∷ []) Eq.refl

private
  q146 : WsL → Eqn
  q146 c4 = eqn (Sw23 ∷ Sb1-0-3-4 ∷ []) (Sb1-0-2-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·3·4⟩ c4)
  q147 : WsL → Eqn
  q147 c4 = eqn (Sw23 ∷ Sb⁻1-0-3-4 ∷ []) (Sb⁻1-0-2-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·3·4⟩ c4)
  q148 : WsL → Eqn
  q148 c4 = eqn (Sw23 ∷ Bx⁻1-0243 ∷ []) (Bx⁻1-0342 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·0243⟩ c4)

-- nat 2 SBOXd(1;0;24;3): 7 steps
lem-nat-2-SBOXd⟨1·0·24·3⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-0-24-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-34-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·24·3⟩ c4 = derive (Sw23 ∷ Sb⁻1-0-24-3 ∷ []) (Sb⁻1-0-34-2 ∷ Sw23 ∷ [])
  (re 1 1 (Sb1-0-3-4 ∷ Toff324 ∷ Sb⁻1-0-3-4 ∷ Toff324 ∷ Bx⁻1-0243 ∷ []) ∷
   rw 0 (q146 c4) ∷
   rw 1 (q99 c4) ∷
   rw 2 (q147 c4) ∷
   rw 3 (q99 c4) ∷
   rw 4 (q148 c4) ∷
   re 0 5 (Sb⁻1-0-34-2 ∷ []) ∷ []) Eq.refl

private
  q149 : WsL → Eqn
  q149 c4 = eqn (Sw34 ∷ Toff014 ∷ []) (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4)

-- nat 3 BOXd(0;142): 8 steps
lem-nat-3-BOXd⟨0·142⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻0-142 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-132 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·142⟩ c4 = derive (Sw34 ∷ Bx⁻0-142 ∷ []) (Bx⁻0-132 ∷ Sw34 ∷ [])
  (re 1 1 (Bx⁻1-02 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-02 ∷ Toff014 ∷ CCZ014 ∷ []) ∷
   rw⁻ 0 (q104 c4) ∷
   rw 1 (q30 c4) ∷
   rw 2 (q149 c4) ∷
   rw⁻ 3 (q104 c4) ∷
   rw 4 (q149 c4) ∷
   rw 5 (q30 c4) ∷
   re 0 6 (Bx⁻0-132 ∷ []) ∷ []) Eq.refl

private
  q150 : WsL → Eqn
  q150 c4 = eqn (Sw34 ∷ Bx⁻0-142 ∷ []) (Bx⁻0-132 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·142⟩ c4)
  q151 : WsL → Eqn
  q151 c4 = eqn (Sw34 ∷ Toff103 ∷ []) (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4)

-- nat 3 BOXd(1;0342): 8 steps
lem-nat-3-BOXd⟨1·0342⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻1-0342 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0432 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·0342⟩ c4 = derive (Sw34 ∷ Bx⁻1-0342 ∷ []) (Bx⁻1-0432 ∷ Sw34 ∷ [])
  (re 1 1 (Bx⁻0-142 ∷ CCZ013 ∷ Toff103 ∷ Bx⁻0-142 ∷ Toff103 ∷ CCZ013 ∷ []) ∷
   rw 0 (q150 c4) ∷
   rw 1 (q33 c4) ∷
   rw 2 (q151 c4) ∷
   rw 3 (q150 c4) ∷
   rw 4 (q151 c4) ∷
   rw 5 (q33 c4) ∷
   re 0 6 (Bx⁻1-0432 ∷ []) ∷ []) Eq.refl

private
  q152 : WsL → Eqn
  q152 c4 = eqn (Sw34 ∷ Sb1-0-2-4 ∷ []) (Sb1-0-2-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·0·2·4⟩ c4)
  q153 : WsL → Eqn
  q153 c4 = eqn (Sw34 ∷ Sb⁻1-0-2-4 ∷ []) (Sb⁻1-0-2-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·0·2·4⟩ c4)
  q154 : WsL → Eqn
  q154 c4 = eqn (Sw34 ∷ Bx⁻1-0342 ∷ []) (Bx⁻1-0432 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·0342⟩ c4)

-- nat 3 SBOXd(1;0;34;2): 7 steps
lem-nat-3-SBOXd⟨1·0·34·2⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻1-0-34-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-43-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·0·34·2⟩ c4 = derive (Sw34 ∷ Sb⁻1-0-34-2 ∷ []) (Sb⁻1-0-43-2 ∷ Sw34 ∷ [])
  (re 1 1 (Sb1-0-2-4 ∷ Toff234 ∷ Sb⁻1-0-2-4 ∷ Toff234 ∷ Bx⁻1-0342 ∷ []) ∷
   rw 0 (q152 c4) ∷
   rw 1 (q107 c4) ∷
   rw 2 (q153 c4) ∷
   rw 3 (q107 c4) ∷
   rw 4 (q154 c4) ∷
   re 0 5 (Sb⁻1-0-43-2 ∷ []) ∷ []) Eq.refl

private
  q155 : WsL → Eqn
  q155 c4 = eqn (Sw34 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·3·2⟩ c4)
  q156 : WsL → Eqn
  q156 c4 = eqn (Sw34 ∷ Toff324 ∷ []) (Toff423 ∷ Sw34 ∷ []) (wl0119 c4)
  q157 : WsL → Eqn
  q157 c4 = eqn (Sw34 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-4-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·3·2⟩ c4)
  q158 : WsL → Eqn
  q158 c4 = eqn (Sw34 ∷ Bx⁻0-1423 ∷ []) (Bx⁻0-1324 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·1423⟩ c4)

-- nat 3 SBOXd(0;1;42;3): 7 steps
lem-nat-3-SBOXd⟨0·1·42·3⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-32-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·1·42·3⟩ c4 = derive (Sw34 ∷ Sb⁻0-1-42-3 ∷ []) (Sb⁻0-1-32-4 ∷ Sw34 ∷ [])
  (re 1 1 (Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Toff324 ∷ Bx⁻0-1423 ∷ []) ∷
   rw 0 (q155 c4) ∷
   rw 1 (q156 c4) ∷
   rw 2 (q157 c4) ∷
   rw 3 (q156 c4) ∷
   rw 4 (q158 c4) ∷
   re 0 5 (Sb⁻0-1-32-4 ∷ []) ∷ []) Eq.refl

private
  q159 : WsL → Eqn
  q159 c4 = eqn (Sw34 ∷ CZ14 ∷ []) (CZ13 ∷ Sw34 ∷ []) (lem-nat-3-CZ14 c4)

-- nat 3 BOXd(0;14): 3 steps
lem-nat-3-BOXd⟨0·14⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻0-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-13 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·14⟩ c4 = derive (Sw34 ∷ Bx⁻0-14 ∷ []) (Bx⁻0-13 ∷ Sw34 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   rw 0 (q159 c4) ∷
   re 0 1 (Bx⁻0-13 ∷ []) ∷ []) Eq.refl

private
  q160 : WsL → Eqn
  q160 c4 = eqn (Sw34 ∷ Bx⁻0-14 ∷ []) (Bx⁻0-13 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·14⟩ c4)
  q161 : WsL → Eqn
  q161 c4 = eqn (CCZ012 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (Swap))
  q162 : WsL → Eqn
  q162 c4 = eqn (Toff102 ∷ Sw34 ∷ []) (Sw34 ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))

-- nat 3 BOXd(1;024): 8 steps
lem-nat-3-BOXd⟨1·024⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻1-024 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-023 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·024⟩ c4 = derive (Sw34 ∷ Bx⁻1-024 ∷ []) (Bx⁻1-023 ∷ Sw34 ∷ [])
  (re 1 1 (Bx⁻0-14 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-14 ∷ Toff102 ∷ CCZ012 ∷ []) ∷
   rw 0 (q160 c4) ∷
   rw⁻ 1 (q161 c4) ∷
   rw⁻ 2 (q162 c4) ∷
   rw 3 (q160 c4) ∷
   rw⁻ 4 (q162 c4) ∷
   rw⁻ 5 (q161 c4) ∷
   re 0 6 (Bx⁻1-023 ∷ []) ∷ []) Eq.refl

private
  q163 : WsL → Eqn
  q163 c4 = eqn (Sw34 ∷ Bx⁻1-024 ∷ []) (Bx⁻1-023 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·024⟩ c4)

-- nat 3 BOXd(0;1324): 8 steps
lem-nat-3-BOXd⟨0·1324⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-1423 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨0·1324⟩ c4 = derive (Sw34 ∷ Bx⁻0-1324 ∷ []) (Bx⁻0-1423 ∷ Sw34 ∷ [])
  (re 1 1 (Bx⁻1-024 ∷ CCZ013 ∷ Toff013 ∷ Bx⁻1-024 ∷ Toff013 ∷ CCZ013 ∷ []) ∷
   rw 0 (q163 c4) ∷
   rw 1 (q33 c4) ∷
   rw 2 (q34 c4) ∷
   rw 3 (q163 c4) ∷
   rw 4 (q34 c4) ∷
   rw 5 (q33 c4) ∷
   re 0 6 (Bx⁻0-1423 ∷ []) ∷ []) Eq.refl

private
  q164 : WsL → Eqn
  q164 c4 = eqn (Sw34 ∷ Sb0-1-4-2 ∷ []) (Sb0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·4·2⟩ c4)
  q165 : WsL → Eqn
  q165 c4 = eqn (Sw34 ∷ Toff423 ∷ []) (Toff324 ∷ Sw34 ∷ []) (wl0120 c4)
  q166 : WsL → Eqn
  q166 c4 = eqn (Sw34 ∷ Sb⁻0-1-4-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨0·1·4·2⟩ c4)
  q167 : WsL → Eqn
  q167 c4 = eqn (Sw34 ∷ Bx⁻0-1324 ∷ []) (Bx⁻0-1423 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨0·1324⟩ c4)

-- nat 3 SBOXd(0;1;32;4): 7 steps
lem-nat-3-SBOXd⟨0·1·32·4⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻0-1-32-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-42-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·1·32·4⟩ c4 = derive (Sw34 ∷ Sb⁻0-1-32-4 ∷ []) (Sb⁻0-1-42-3 ∷ Sw34 ∷ [])
  (re 1 1 (Sb0-1-4-2 ∷ Toff423 ∷ Sb⁻0-1-4-2 ∷ Toff423 ∷ Bx⁻0-1324 ∷ []) ∷
   rw 0 (q164 c4) ∷
   rw 1 (q165 c4) ∷
   rw 2 (q166 c4) ∷
   rw 3 (q165 c4) ∷
   rw 4 (q167 c4) ∷
   re 0 5 (Sb⁻0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q168 : WsL → Eqn
  q168 c4 = eqn (Sw01 ∷ Sb1-0-3-2 ∷ []) (Sb0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·3·2⟩ c4)
  q169 : WsL → Eqn
  q169 c4 = eqn (Sw01 ∷ Toff324 ∷ []) (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))
  q170 : WsL → Eqn
  q170 c4 = eqn (Sw01 ∷ Sb⁻1-0-3-2 ∷ []) (Sb⁻0-1-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·3·2⟩ c4)
  q171 : WsL → Eqn
  q171 c4 = eqn (Sw01 ∷ Bx⁻1-0423 ∷ []) (Bx⁻0-1423 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·0423⟩ c4)

-- nat 0 SBOXd(1;0;42;3): 7 steps
lem-nat-0-SBOXd⟨1·0·42·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-42-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·0·42·3⟩ c4 = derive (Sw01 ∷ Sb⁻1-0-42-3 ∷ []) (Sb⁻0-1-42-3 ∷ Sw01 ∷ [])
  (re 1 1 (Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ Toff324 ∷ Bx⁻1-0423 ∷ []) ∷
   rw 0 (q168 c4) ∷
   rw 1 (q169 c4) ∷
   rw 2 (q170 c4) ∷
   rw 3 (q169 c4) ∷
   rw 4 (q171 c4) ∷
   re 0 5 (Sb⁻0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q172 : WsL → Eqn
  q172 c4 = eqn (CZ03 ∷ Sw01 ∷ []) (Sw01 ∷ CZ13 ∷ []) (wl0088 c4)

-- nat 0 BOXd(0;13): 3 steps
lem-nat-0-BOXd⟨0·13⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻0-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-03 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·13⟩ c4 = derive (Sw01 ∷ Bx⁻0-13 ∷ []) (Bx⁻1-03 ∷ Sw01 ∷ [])
  (re 1 1 (CZ13 ∷ []) ∷
   rw⁻ 0 (q172 c4) ∷
   re 0 1 (Bx⁻1-03 ∷ []) ∷ []) Eq.refl

private
  q173 : WsL → Eqn
  q173 c4 = eqn (Sw01 ∷ Bx⁻0-13 ∷ []) (Bx⁻1-03 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·13⟩ c4)
  q174 : WsL → Eqn
  q174 c4 = eqn (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) (wl0097 c4)

-- nat 0 BOXd(1;023): 8 steps
lem-nat-0-BOXd⟨1·023⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻1-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-123 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·023⟩ c4 = derive (Sw01 ∷ Bx⁻1-023 ∷ []) (Bx⁻0-123 ∷ Sw01 ∷ [])
  (re 1 1 (Bx⁻0-13 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻0-13 ∷ Toff102 ∷ CCZ012 ∷ []) ∷
   rw 0 (q173 c4) ∷
   rw⁻ 1 (q81 c4) ∷
   rw 2 (q174 c4) ∷
   rw 3 (q173 c4) ∷
   rw 4 (q174 c4) ∷
   rw⁻ 5 (q81 c4) ∷
   re 0 6 (Bx⁻0-123 ∷ []) ∷ []) Eq.refl

private
  q175 : WsL → Eqn
  q175 c4 = eqn (Sw01 ∷ Bx⁻1-023 ∷ []) (Bx⁻0-123 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·023⟩ c4)

-- nat 0 BOXd(0;1423): 8 steps
lem-nat-0-BOXd⟨0·1423⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-0423 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·1423⟩ c4 = derive (Sw01 ∷ Bx⁻0-1423 ∷ []) (Bx⁻1-0423 ∷ Sw01 ∷ [])
  (re 1 1 (Bx⁻1-023 ∷ CCZ014 ∷ Toff014 ∷ Bx⁻1-023 ∷ Toff014 ∷ CCZ014 ∷ []) ∷
   rw 0 (q175 c4) ∷
   rw 1 (q39 c4) ∷
   rw 2 (q40 c4) ∷
   rw 3 (q175 c4) ∷
   rw 4 (q40 c4) ∷
   rw 5 (q39 c4) ∷
   re 0 6 (Bx⁻1-0423 ∷ []) ∷ []) Eq.refl

private
  q176 : WsL → Eqn
  q176 c4 = eqn (Sw01 ∷ Sb0-1-3-2 ∷ []) (Sb1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·3·2⟩ c4)
  q177 : WsL → Eqn
  q177 c4 = eqn (Sw01 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻1-0-3-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·3·2⟩ c4)
  q178 : WsL → Eqn
  q178 c4 = eqn (Sw01 ∷ Bx⁻0-1423 ∷ []) (Bx⁻1-0423 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·1423⟩ c4)

-- nat 0 SBOXd(0;1;42;3): 7 steps
lem-nat-0-SBOXd⟨0·1·42·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-42-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·1·42·3⟩ c4 = derive (Sw01 ∷ Sb⁻0-1-42-3 ∷ []) (Sb⁻1-0-42-3 ∷ Sw01 ∷ [])
  (re 1 1 (Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ Toff324 ∷ Bx⁻0-1423 ∷ []) ∷
   rw 0 (q176 c4) ∷
   rw 1 (q169 c4) ∷
   rw 2 (q177 c4) ∷
   rw 3 (q169 c4) ∷
   rw 4 (q178 c4) ∷
   re 0 5 (Sb⁻1-0-42-3 ∷ []) ∷ []) Eq.refl

private
  q179 : WsL → Eqn
  q179 c4 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (c₂ (K ↑) (Swap))
  q180 : WsL → Eqn
  q180 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 c4)
  q181 : WsL → Eqn
  q181 c4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap))
  q182 : WsL → Eqn
  q182 c4 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (c₁ (iI) (Swap ↑))
  q183 : WsL → Eqn
  q183 c4 = eqn (K2 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ []) (wl0056 c4)
  q184 : WsL → Eqn
  q184 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl0025 c4)
  q185 : WsL → Eqn
  q185 c4 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wl0046 c4)
  q186 : WsL → Eqn
  q186 c4 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap))
  q187 : WsL → Eqn
  q187 c4 = eqn (ι ∷ Sw34 ∷ []) (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑))
  q188 : WsL → Eqn
  q188 c4 = eqn (K2 ∷ Sw34 ∷ []) (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap))
  q189 : WsL → Eqn
  q189 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 c4)
  q190 : WsL → Eqn
  q190 c4 = eqn (CX02 ∷ Sw34 ∷ []) (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))
  q191 : WsL → Eqn
  q191 c4 = eqn (K1 ∷ Sw12 ∷ []) (Sw12 ∷ K2 ∷ []) (wl0062 c4)
  q192 : WsL → Eqn
  q192 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl0017 c4)
  q193 : WsL → Eqn
  q193 c4 = eqn (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ []) (wl0018 c4)
  q194 : WsL → Eqn
  q194 c4 = eqn (K1 ∷ Sw34 ∷ []) (Sw34 ∷ K1 ∷ []) (c₂ (K ↑) (Swap ↑))
  q195 : WsL → Eqn
  q195 c4 = eqn (CX01 ∷ Sw34 ∷ []) (Sw34 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap ↑))
  q196 : WsL → Eqn
  q196 c4 = eqn (CX32 ∷ Sw12 ∷ []) (Sw12 ∷ CX31 ∷ []) (wl0150 c4)
  q197 : WsL → Eqn
  q197 c4 = eqn (CX31 ∷ Sw12 ∷ []) (Sw12 ∷ CX32 ∷ []) (wl0151 c4)
  q198 : WsL → Eqn
  q198 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0008 c4)
  q199 : WsL → Eqn
  q199 c4 = eqn (CS24⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS14⁻ ∷ []) (wl0009 c4)
  q200 : WsL → Eqn
  q200 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl0024 c4)

-- comm TOFF203 CX41: 181 steps
lem-comm-TOFF203-CX41 : WsL → ⟪ (Toff203 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (CX41 ∷ Toff203 ∷ []) ⟫ʷ
lem-comm-TOFF203-CX41 c4 = derive (Toff203 ∷ CX41 ∷ []) (CX41 ∷ Toff203 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ CX21 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   re 0 1 (Sw12 ∷ Toff103 ∷ Sw12 ∷ []) ∷
   re 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 1 (q179 c4) ∷
   rw⁻ 4 (q180 c4) ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 (q181 c4) ∷
   rw⁻ 6 (q180 c4) ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 (q181 c4) ∷
   rw⁻ 8 (q180 c4) ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 (q179 c4) ∷
   rw⁻ 8 (q182 c4) ∷
   rw 9 (q180 c4) ∷
   rw⁻ 0 (q183 c4) ∷
   rw⁻ 1 (q184 c4) ∷
   rw⁻ 4 (q63 c4) ∷
   re 2 3 (CX02 ∷ []) ∷
   rw⁻ 3 (q185 c4) ∷
   rw⁻ 6 (q63 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw⁻ 5 (q119 c4) ∷
   rw⁻ 6 (q183 c4) ∷
   rw⁻ 7 (q186 c4) ∷
   rw 8 (q63 c4) ∷
   rw 7 (q187 c4) ∷
   rw 6 (q188 c4) ∷
   rw⁻ 5 (q189 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw 4 (q190 c4) ∷
   rw⁻ 3 (q189 c4) ∷
   re 4 3 (CS24⁻ ∷ []) ∷
   rw 2 (q190 c4) ∷
   rw⁻ 1 (q189 c4) ∷
   re 2 3 (CS24 ∷ []) ∷
   rw 0 (q188 c4) ∷
   rw⁻ 1 (q63 c4) ∷
   rw⁻ 2 (q191 c4) ∷
   rw⁻ 3 (q192 c4) ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 (q63 c4) ∷
   rw⁻ 5 (q193 c4) ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 (q63 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q67 c4) ∷
   rw⁻ 8 (q119 c4) ∷
   rw 9 (q67 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q191 c4) ∷
   rw⁻ 9 (q186 c4) ∷
   rw⁻ 2 (q189 c4) ∷
   rw⁻ 3 (q194 c4) ∷
   re 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 4 (q189 c4) ∷
   rw⁻ 5 (q195 c4) ∷
   re 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q189 c4) ∷
   rw⁻ 7 (q195 c4) ∷
   re 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 8 (q189 c4) ∷
   rw⁻ 9 (q194 c4) ∷
   rw⁻ 10 (q187 c4) ∷
   rw⁻ 3 (q180 c4) ∷
   rw⁻ 4 (q179 c4) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 (q180 c4) ∷
   rw⁻ 6 (q181 c4) ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 (q180 c4) ∷
   rw⁻ 8 (q181 c4) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 (q180 c4) ∷
   rw⁻ 10 (q179 c4) ∷
   rw⁻ 11 (q182 c4) ∷
   re 4 8 (Toff102 ∷ []) ∷
   re 3 3 (Toff103 ∷ []) ∷
   re 2 3 (Toff104 ∷ []) ∷
   re 1 3 (Toff204 ∷ []) ∷
   rw⁻ 1 (q180 c4) ∷
   re 2 3 (Toff304 ∷ []) ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 (q180 c4) ∷
   re 10 3 (CX31 ∷ []) ∷
   rw⁻ 9 (q196 c4) ∷
   rw⁻ 10 (q189 c4) ∷
   re 8 3 (CX42 ∷ []) ∷
   rw⁻ 7 (q61 c4) ∷
   rw 6 (q60 c4) ∷
   rw⁻ 5 (q59 c4) ∷
   re 5 1 (Sw34 ∷ CX32 ∷ Sw34 ∷ []) ∷
   rw 4 (q189 c4) ∷
   rw⁻ 3 (q197 c4) ∷
   re 3 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 2 (q180 c4) ∷
   re 3 9 (Toff304 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) ∷
   rw 5 (q180 c4) ∷
   re 4 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) ∷
   re 5 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) ∷
   re 6 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 7 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 6 (q179 c4) ∷
   rw⁻ 9 (q180 c4) ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 (q181 c4) ∷
   rw⁻ 11 (q180 c4) ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 (q181 c4) ∷
   rw⁻ 13 (q180 c4) ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 (q179 c4) ∷
   rw⁻ 13 (q182 c4) ∷
   rw 14 (q180 c4) ∷
   rw⁻ 5 (q194 c4) ∷
   rw⁻ 8 (q189 c4) ∷
   re 6 3 (CS14 ∷ []) ∷
   rw⁻ 7 (q195 c4) ∷
   rw⁻ 10 (q189 c4) ∷
   re 8 3 (CS14⁻ ∷ []) ∷
   rw⁻ 9 (q195 c4) ∷
   rw⁻ 12 (q189 c4) ∷
   re 10 3 (CS04 ∷ []) ∷
   rw⁻ 11 (q194 c4) ∷
   rw⁻ 12 (q187 c4) ∷
   rw 13 (q189 c4) ∷
   rw⁻ 4 (q183 c4) ∷
   rw⁻ 5 (q198 c4) ∷
   rw⁻ 8 (q63 c4) ∷
   re 6 3 (CX02 ∷ []) ∷
   rw⁻ 7 (q199 c4) ∷
   rw⁻ 10 (q63 c4) ∷
   re 8 3 (CX02 ∷ []) ∷
   re 10 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 9 (q67 c4) ∷
   rw⁻ 10 (q119 c4) ∷
   rw 11 (q67 c4) ∷
   re 9 3 (CS04 ∷ []) ∷
   rw⁻ 10 (q183 c4) ∷
   rw⁻ 11 (q186 c4) ∷
   rw 12 (q63 c4) ∷
   rw 11 (q187 c4) ∷
   rw 10 (q188 c4) ∷
   re 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 11 (q189 c4) ∷
   rw 8 (q190 c4) ∷
   re 7 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 9 (q189 c4) ∷
   rw 6 (q190 c4) ∷
   re 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 7 (q189 c4) ∷
   rw 4 (q188 c4) ∷
   rw⁻ 5 (q63 c4) ∷
   rw⁻ 6 (q191 c4) ∷
   rw⁻ 7 (q200 c4) ∷
   re 9 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 8 (q63 c4) ∷
   rw⁻ 9 (q64 c4) ∷
   re 11 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 10 (q63 c4) ∷
   rw⁻ 11 (q119 c4) ∷
   rw⁻ 12 (q191 c4) ∷
   rw⁻ 13 (q186 c4) ∷
   rw⁻ 6 (q180 c4) ∷
   rw⁻ 7 (q179 c4) ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 (q180 c4) ∷
   rw⁻ 9 (q181 c4) ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 (q180 c4) ∷
   rw⁻ 11 (q181 c4) ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 (q180 c4) ∷
   rw⁻ 13 (q179 c4) ∷
   rw⁻ 14 (q182 c4) ∷
   re 7 8 (Toff102 ∷ []) ∷
   re 6 3 (Toff103 ∷ []) ∷
   re 5 3 (Toff203 ∷ []) ∷
   re 0 5 (CX41 ∷ []) ∷ []) Eq.refl

private
  q201 : WsL → Eqn
  q201 c4 = eqn (Sw01 ∷ CZ23 ∷ []) (CZ23 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ))

-- resp CZ13 at 2: 4 steps
lem-resp-CZ13-at-2 : WsL → ⟪ (CZ13 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CZ13-at-2 c4 = derive (CZ13 ∷ []) (Sw12 ∷ Sw01 ∷ CZ23 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q63 c4) ∷
   rw 0 (q71 c4) ∷
   rw⁻ 2 (q65 c4) ∷
   rw⁻ 1 (q201 c4) ∷ []) Eq.refl

private
  q202 : WsL → Eqn
  q202 c4 = eqn (Sw12 ∷ CZ01 ∷ []) (CZ02 ∷ Sw12 ∷ []) (lem-nat-1-CZ01 c4)

-- nat 1 BOX(3;01): 3 steps
lem-nat-1-BOX⟨3·01⟩ : WsL → ⟪ (Sw12 ∷ Bx3-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-02 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·01⟩ c4 = derive (Sw12 ∷ Bx3-01 ∷ []) (Bx3-02 ∷ Sw12 ∷ [])
  (re 1 1 (CZ01 ∷ []) ∷
   rw 0 (q202 c4) ∷
   re 0 1 (Bx3-02 ∷ []) ∷ []) Eq.refl

private
  q203 : WsL → Eqn
  q203 c4 = eqn (Sw12 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4)
  q204 : WsL → Eqn
  q204 c4 = eqn (Sw12 ∷ Toff034 ∷ []) (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4)
  q205 : WsL → Eqn
  q205 c4 = eqn (Sw12 ∷ Bx3-01 ∷ []) (Bx3-02 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·01⟩ c4)

-- nat 1 BOX(0;341): 8 steps
lem-nat-1-BOX⟨0·341⟩ : WsL → ⟪ (Sw12 ∷ Bx0-341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-342 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·341⟩ c4 = derive (Sw12 ∷ Bx0-341 ∷ []) (Bx0-342 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) ∷
   rw 0 (q203 c4) ∷
   rw 1 (q204 c4) ∷
   rw 2 (q205 c4) ∷
   rw 3 (q204 c4) ∷
   rw 4 (q203 c4) ∷
   rw 5 (q205 c4) ∷
   re 0 6 (Bx0-342 ∷ []) ∷ []) Eq.refl

private
  q206 : WsL → Eqn
  q206 c4 = eqn (Sw12 ∷ Toff302 ∷ []) (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4)
  q207 : WsL → Eqn
  q207 c4 = eqn (Sw12 ∷ Bx0-341 ∷ []) (Bx0-342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·341⟩ c4)

-- nat 1 BOX(3;0241): 8 steps
lem-nat-1-BOX⟨3·0241⟩ : WsL → ⟪ (Sw12 ∷ Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·0241⟩ c4 = derive (Sw12 ∷ Bx3-0241 ∷ []) (Bx3-0142 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-341 ∷ Toff302 ∷ CCZ023 ∷ Bx0-341 ∷ []) ∷
   rw 0 (q52 c4) ∷
   rw 1 (q206 c4) ∷
   rw 2 (q207 c4) ∷
   rw 3 (q206 c4) ∷
   rw 4 (q52 c4) ∷
   rw 5 (q207 c4) ∷
   re 0 6 (Bx3-0142 ∷ []) ∷ []) Eq.refl

private
  q208 : WsL → Eqn
  q208 c4 = eqn (Sw12 ∷ Bx3-02 ∷ []) (Bx3-01 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·02⟩ c4)

-- nat 1 BOX(0;342): 8 steps
lem-nat-1-BOX⟨0·342⟩ : WsL → ⟪ (Sw12 ∷ Bx0-342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-341 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·342⟩ c4 = derive (Sw12 ∷ Bx0-342 ∷ []) (Bx0-341 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) ∷
   rw 0 (q203 c4) ∷
   rw 1 (q204 c4) ∷
   rw 2 (q208 c4) ∷
   rw 3 (q204 c4) ∷
   rw 4 (q203 c4) ∷
   rw 5 (q208 c4) ∷
   re 0 6 (Bx0-341 ∷ []) ∷ []) Eq.refl

private
  q209 : WsL → Eqn
  q209 c4 = eqn (Sw12 ∷ Toff301 ∷ []) (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4)
  q210 : WsL → Eqn
  q210 c4 = eqn (Sw12 ∷ Bx0-342 ∷ []) (Bx0-341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·342⟩ c4)

-- nat 1 BOX(3;0142): 8 steps
lem-nat-1-BOX⟨3·0142⟩ : WsL → ⟪ (Sw12 ∷ Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·0142⟩ c4 = derive (Sw12 ∷ Bx3-0142 ∷ []) (Bx3-0241 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-342 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ []) ∷
   rw 0 (q42 c4) ∷
   rw 1 (q209 c4) ∷
   rw 2 (q210 c4) ∷
   rw 3 (q209 c4) ∷
   rw 4 (q42 c4) ∷
   rw 5 (q210 c4) ∷
   re 0 6 (Bx3-0241 ∷ []) ∷ []) Eq.refl

private
  q211 : WsL → Eqn
  q211 c4 = eqn (Bx2-01 ∷ Sw23 ∷ []) (Sw23 ∷ Bx2-01 ∷ []) (c₂ (CZ) (Swap))

-- nat 2 BOX(2;01): 2 steps
lem-nat-2-BOX⟨2·01⟩ : WsL → ⟪ (Sw23 ∷ Bx2-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-01 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·01⟩ c4 = derive (Sw23 ∷ Bx2-01 ∷ []) (Bx3-01 ∷ Sw23 ∷ [])
  (rw⁻ 0 (q211 c4) ∷
   re 0 1 (Bx3-01 ∷ []) ∷ []) Eq.refl

private
  q212 : WsL → Eqn
  q212 c4 = eqn (Sw23 ∷ CCZ024 ∷ []) (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4)
  q213 : WsL → Eqn
  q213 c4 = eqn (Sw23 ∷ Bx2-01 ∷ []) (Bx3-01 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·01⟩ c4)

-- nat 2 BOX(0;241): 8 steps
lem-nat-2-BOX⟨0·241⟩ : WsL → ⟪ (Sw23 ∷ Bx0-241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-341 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·241⟩ c4 = derive (Sw23 ∷ Bx0-241 ∷ []) (Bx0-341 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) ∷
   rw 0 (q212 c4) ∷
   rw 1 (q27 c4) ∷
   rw 2 (q213 c4) ∷
   rw 3 (q27 c4) ∷
   rw 4 (q212 c4) ∷
   rw 5 (q213 c4) ∷
   re 0 6 (Bx0-341 ∷ []) ∷ []) Eq.refl

private
  q214 : WsL → Eqn
  q214 c4 = eqn (CCZ023 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ023 ∷ []) (wl0065 c4)
  q215 : WsL → Eqn
  q215 c4 = eqn (Sw23 ∷ Toff203 ∷ []) (Toff302 ∷ Sw23 ∷ []) (wl0090 c4)
  q216 : WsL → Eqn
  q216 c4 = eqn (Sw23 ∷ Bx0-241 ∷ []) (Bx0-341 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·241⟩ c4)

-- nat 2 BOX(2;0341): 8 steps
lem-nat-2-BOX⟨2·0341⟩ : WsL → ⟪ (Sw23 ∷ Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·0341⟩ c4 = derive (Sw23 ∷ Bx2-0341 ∷ []) (Bx3-0241 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-241 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ []) ∷
   rw⁻ 0 (q214 c4) ∷
   rw 1 (q215 c4) ∷
   rw 2 (q216 c4) ∷
   rw 3 (q215 c4) ∷
   rw⁻ 4 (q214 c4) ∷
   rw 5 (q216 c4) ∷
   re 0 6 (Bx3-0241 ∷ []) ∷ []) Eq.refl

private
  q217 : WsL → Eqn
  q217 c4 = eqn (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4)
  q218 : WsL → Eqn
  q218 c4 = eqn (Sw23 ∷ Bx3-01 ∷ []) (Bx2-01 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·01⟩ c4)

-- nat 2 BOX(0;341): 8 steps
lem-nat-2-BOX⟨0·341⟩ : WsL → ⟪ (Sw23 ∷ Bx0-341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-241 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·341⟩ c4 = derive (Sw23 ∷ Bx0-341 ∷ []) (Bx0-241 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) ∷
   rw 0 (q217 c4) ∷
   rw 1 (q16 c4) ∷
   rw 2 (q218 c4) ∷
   rw 3 (q16 c4) ∷
   rw 4 (q217 c4) ∷
   rw 5 (q218 c4) ∷
   re 0 6 (Bx0-241 ∷ []) ∷ []) Eq.refl

private
  q219 : WsL → Eqn
  q219 c4 = eqn (Sw23 ∷ Toff302 ∷ []) (Toff203 ∷ Sw23 ∷ []) (wl0066 c4)
  q220 : WsL → Eqn
  q220 c4 = eqn (Sw23 ∷ Bx0-341 ∷ []) (Bx0-241 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·341⟩ c4)

-- nat 2 BOX(3;0241): 8 steps
lem-nat-2-BOX⟨3·0241⟩ : WsL → ⟪ (Sw23 ∷ Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·0241⟩ c4 = derive (Sw23 ∷ Bx3-0241 ∷ []) (Bx2-0341 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-341 ∷ Toff302 ∷ CCZ023 ∷ Bx0-341 ∷ []) ∷
   rw⁻ 0 (q214 c4) ∷
   rw 1 (q219 c4) ∷
   rw 2 (q220 c4) ∷
   rw 3 (q219 c4) ∷
   rw⁻ 4 (q214 c4) ∷
   rw 5 (q220 c4) ∷
   re 0 6 (Bx2-0341 ∷ []) ∷ []) Eq.refl

private
  q221 : WsL → Eqn
  q221 c4 = eqn (Sw34 ∷ CCZ024 ∷ []) (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4)
  q222 : WsL → Eqn
  q222 c4 = eqn (Sw34 ∷ Toff024 ∷ []) (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4)
  q223 : WsL → Eqn
  q223 c4 = eqn (Bx2-01 ∷ Sw34 ∷ []) (Sw34 ∷ Bx2-01 ∷ []) (c₂ (CZ) (Swap ↑))

-- nat 3 BOX(0;241): 8 steps
lem-nat-3-BOX⟨0·241⟩ : WsL → ⟪ (Sw34 ∷ Bx0-241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-231 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·241⟩ c4 = derive (Sw34 ∷ Bx0-241 ∷ []) (Bx0-231 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) ∷
   rw 0 (q221 c4) ∷
   rw 1 (q222 c4) ∷
   rw⁻ 2 (q223 c4) ∷
   rw 3 (q222 c4) ∷
   rw 4 (q221 c4) ∷
   rw⁻ 5 (q223 c4) ∷
   re 0 6 (Bx0-231 ∷ []) ∷ []) Eq.refl

private
  q224 : WsL → Eqn
  q224 c4 = eqn (Sw34 ∷ CCZ023 ∷ []) (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4)
  q225 : WsL → Eqn
  q225 c4 = eqn (Sw34 ∷ Toff203 ∷ []) (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4)
  q226 : WsL → Eqn
  q226 c4 = eqn (Sw34 ∷ Bx0-241 ∷ []) (Bx0-231 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·241⟩ c4)

-- nat 3 BOX(2;0341): 8 steps
lem-nat-3-BOX⟨2·0341⟩ : WsL → ⟪ (Sw34 ∷ Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·0341⟩ c4 = derive (Sw34 ∷ Bx2-0341 ∷ []) (Bx2-0431 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-241 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ []) ∷
   rw 0 (q224 c4) ∷
   rw 1 (q225 c4) ∷
   rw 2 (q226 c4) ∷
   rw 3 (q225 c4) ∷
   rw 4 (q224 c4) ∷
   rw 5 (q226 c4) ∷
   re 0 6 (Bx2-0431 ∷ []) ∷ []) Eq.refl

private
  q227 : WsL → Eqn
  q227 c4 = eqn (Sw23 ∷ Bx1-03 ∷ []) (Bx1-02 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·03⟩ c4)

-- nat 2 BOX(0;123): 8 steps
lem-nat-2-BOX⟨0·123⟩ : WsL → ⟪ (Sw23 ∷ Bx0-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-132 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·123⟩ c4 = derive (Sw23 ∷ Bx0-123 ∷ []) (Bx0-132 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-03 ∷ Toff012 ∷ CCZ012 ∷ Bx1-03 ∷ []) ∷
   rw 0 (q93 c4) ∷
   rw 1 (q94 c4) ∷
   rw 2 (q227 c4) ∷
   rw 3 (q94 c4) ∷
   rw 4 (q93 c4) ∷
   rw 5 (q227 c4) ∷
   re 0 6 (Bx0-132 ∷ []) ∷ []) Eq.refl

private
  q228 : WsL → Eqn
  q228 c4 = eqn (Sw23 ∷ Bx0-123 ∷ []) (Bx0-132 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·123⟩ c4)

-- nat 2 BOX(1;0423): 8 steps
lem-nat-2-BOX⟨1·0423⟩ : WsL → ⟪ (Sw23 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0432 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·0423⟩ c4 = derive (Sw23 ∷ Bx1-0423 ∷ []) (Bx1-0432 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-123 ∷ Toff104 ∷ CCZ014 ∷ Bx0-123 ∷ []) ∷
   rw 0 (q96 c4) ∷
   rw 1 (q97 c4) ∷
   rw 2 (q228 c4) ∷
   rw 3 (q97 c4) ∷
   rw 4 (q96 c4) ∷
   rw 5 (q228 c4) ∷
   re 0 6 (Bx1-0432 ∷ []) ∷ []) Eq.refl

private
  q229 : WsL → Eqn
  q229 c4 = eqn (Sw12 ∷ CS01 ∷ []) (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4)

-- nat 1 SBOX(3;0;1;4): 3 steps
lem-nat-1-SBOX⟨3·0·1·4⟩ : WsL → ⟪ (Sw12 ∷ Sb3-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-2-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·0·1·4⟩ c4 = derive (Sw12 ∷ Sb3-0-1-4 ∷ []) (Sb3-0-2-4 ∷ Sw12 ∷ [])
  (re 1 1 (CS01 ∷ []) ∷
   rw 0 (q229 c4) ∷
   re 0 1 (Sb3-0-2-4 ∷ []) ∷ []) Eq.refl

private
  q230 : WsL → Eqn
  q230 c4 = eqn (Sw12 ∷ CS01⁻ ∷ []) (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4)

-- nat 1 SBOXd(3;0;1;4): 3 steps
lem-nat-1-SBOXd⟨3·0·1·4⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻3-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-2-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·0·1·4⟩ c4 = derive (Sw12 ∷ Sb⁻3-0-1-4 ∷ []) (Sb⁻3-0-2-4 ∷ Sw12 ∷ [])
  (re 1 1 (CS01⁻ ∷ []) ∷
   rw 0 (q230 c4) ∷
   re 0 1 (Sb⁻3-0-2-4 ∷ []) ∷ []) Eq.refl

private
  q231 : WsL → Eqn
  q231 c4 = eqn (Sw12 ∷ Bx3-0241 ∷ []) (Bx3-0142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0241⟩ c4)
  q232 : WsL → Eqn
  q232 c4 = eqn (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) (wl0095 c4)
  q233 : WsL → Eqn
  q233 c4 = eqn (Sw12 ∷ Sb3-0-1-4 ∷ []) (Sb3-0-2-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·1·4⟩ c4)
  q234 : WsL → Eqn
  q234 c4 = eqn (Sw12 ∷ Sb⁻3-0-1-4 ∷ []) (Sb⁻3-0-2-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·0·1·4⟩ c4)

-- nat 1 SBOX(3;0;24;1): 7 steps
lem-nat-1-SBOX⟨3·0·24·1⟩ : WsL → ⟪ (Sw12 ∷ Sb3-0-24-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-14-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·0·24·1⟩ c4 = derive (Sw12 ∷ Sb3-0-24-1 ∷ []) (Sb3-0-14-2 ∷ Sw12 ∷ [])
  (re 1 1 (Bx3-0241 ∷ Toff124 ∷ Sb3-0-1-4 ∷ Toff124 ∷ Sb⁻3-0-1-4 ∷ []) ∷
   rw 0 (q231 c4) ∷
   rw 1 (q232 c4) ∷
   rw 2 (q233 c4) ∷
   rw 3 (q232 c4) ∷
   rw 4 (q234 c4) ∷
   re 0 5 (Sb3-0-14-2 ∷ []) ∷ []) Eq.refl

private
  q235 : WsL → Eqn
  q235 c4 = eqn (Sw12 ∷ CS02 ∷ []) (CS01 ∷ Sw12 ∷ []) (lem-nat-1-CS02 c4)

-- nat 1 SBOX(3;0;2;4): 3 steps
lem-nat-1-SBOX⟨3·0·2·4⟩ : WsL → ⟪ (Sw12 ∷ Sb3-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-1-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·0·2·4⟩ c4 = derive (Sw12 ∷ Sb3-0-2-4 ∷ []) (Sb3-0-1-4 ∷ Sw12 ∷ [])
  (re 1 1 (CS02 ∷ []) ∷
   rw 0 (q235 c4) ∷
   re 0 1 (Sb3-0-1-4 ∷ []) ∷ []) Eq.refl

private
  q236 : WsL → Eqn
  q236 c4 = eqn (Sw12 ∷ CS02⁻ ∷ []) (CS01⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd02 c4)

-- nat 1 SBOXd(3;0;2;4): 3 steps
lem-nat-1-SBOXd⟨3·0·2·4⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻3-0-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-1-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·0·2·4⟩ c4 = derive (Sw12 ∷ Sb⁻3-0-2-4 ∷ []) (Sb⁻3-0-1-4 ∷ Sw12 ∷ [])
  (re 1 1 (CS02⁻ ∷ []) ∷
   rw 0 (q236 c4) ∷
   re 0 1 (Sb⁻3-0-1-4 ∷ []) ∷ []) Eq.refl

private
  q237 : WsL → Eqn
  q237 c4 = eqn (Sw12 ∷ Bx3-0142 ∷ []) (Bx3-0241 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0142⟩ c4)
  q238 : WsL → Eqn
  q238 c4 = eqn (Sw12 ∷ Sb3-0-2-4 ∷ []) (Sb3-0-1-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·2·4⟩ c4)
  q239 : WsL → Eqn
  q239 c4 = eqn (Sw12 ∷ Sb⁻3-0-2-4 ∷ []) (Sb⁻3-0-1-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·0·2·4⟩ c4)

-- nat 1 SBOX(3;0;14;2): 7 steps
lem-nat-1-SBOX⟨3·0·14·2⟩ : WsL → ⟪ (Sw12 ∷ Sb3-0-14-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-24-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·0·14·2⟩ c4 = derive (Sw12 ∷ Sb3-0-14-2 ∷ []) (Sb3-0-24-1 ∷ Sw12 ∷ [])
  (re 1 1 (Bx3-0142 ∷ Toff214 ∷ Sb3-0-2-4 ∷ Toff214 ∷ Sb⁻3-0-2-4 ∷ []) ∷
   rw 0 (q237 c4) ∷
   rw 1 (q73 c4) ∷
   rw 2 (q238 c4) ∷
   rw 3 (q73 c4) ∷
   rw 4 (q239 c4) ∷
   re 0 5 (Sb3-0-24-1 ∷ []) ∷ []) Eq.refl

-- nat 2 TOFF134: 2 steps
lem-nat-2-TOFF134 : WsL → ⟪ (Sw23 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF134 c4 = derive (Sw23 ∷ Toff134 ∷ []) (Toff124 ∷ Sw23 ∷ [])
  (re 1 1 (Sw23 ∷ Toff124 ∷ Sw23 ∷ []) ∷
   rw 0 (q180 c4) ∷ []) Eq.refl

private
  q240 : WsL → Eqn
  q240 c4 = eqn (Sb2-0-1-4 ∷ Sw23 ∷ []) (Sw23 ∷ Sb2-0-1-4 ∷ []) (c₂ (CS) (Swap))

-- nat 2 SBOX(2;0;1;4): 2 steps
lem-nat-2-SBOX⟨2·0·1·4⟩ : WsL → ⟪ (Sw23 ∷ Sb2-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-1-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·0·1·4⟩ c4 = derive (Sw23 ∷ Sb2-0-1-4 ∷ []) (Sb3-0-1-4 ∷ Sw23 ∷ [])
  (rw⁻ 0 (q240 c4) ∷
   re 0 1 (Sb3-0-1-4 ∷ []) ∷ []) Eq.refl

private
  q241 : WsL → Eqn
  q241 c4 = eqn (Sb⁻2-0-1-4 ∷ Sw23 ∷ []) (Sw23 ∷ Sb⁻2-0-1-4 ∷ []) (c₂ (CS • CS • CS) (Swap))

-- nat 2 SBOXd(2;0;1;4): 2 steps
lem-nat-2-SBOXd⟨2·0·1·4⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻2-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-1-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨2·0·1·4⟩ c4 = derive (Sw23 ∷ Sb⁻2-0-1-4 ∷ []) (Sb⁻3-0-1-4 ∷ Sw23 ∷ [])
  (rw⁻ 0 (q241 c4) ∷
   re 0 1 (Sb⁻3-0-1-4 ∷ []) ∷ []) Eq.refl

private
  q242 : WsL → Eqn
  q242 c4 = eqn (Sw23 ∷ Bx2-0341 ∷ []) (Bx3-0241 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0341⟩ c4)
  q243 : WsL → Eqn
  q243 c4 = eqn (Sw23 ∷ Toff134 ∷ []) (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4)
  q244 : WsL → Eqn
  q244 c4 = eqn (Sw23 ∷ Sb2-0-1-4 ∷ []) (Sb3-0-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·1·4⟩ c4)
  q245 : WsL → Eqn
  q245 c4 = eqn (Sw23 ∷ Sb⁻2-0-1-4 ∷ []) (Sb⁻3-0-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨2·0·1·4⟩ c4)

-- nat 2 SBOX(2;0;34;1): 7 steps
lem-nat-2-SBOX⟨2·0·34·1⟩ : WsL → ⟪ (Sw23 ∷ Sb2-0-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-24-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·0·34·1⟩ c4 = derive (Sw23 ∷ Sb2-0-34-1 ∷ []) (Sb3-0-24-1 ∷ Sw23 ∷ [])
  (re 1 1 (Bx2-0341 ∷ Toff134 ∷ Sb2-0-1-4 ∷ Toff134 ∷ Sb⁻2-0-1-4 ∷ []) ∷
   rw 0 (q242 c4) ∷
   rw 1 (q243 c4) ∷
   rw 2 (q244 c4) ∷
   rw 3 (q243 c4) ∷
   rw 4 (q245 c4) ∷
   re 0 5 (Sb3-0-24-1 ∷ []) ∷ []) Eq.refl

private
  q246 : WsL → Eqn
  q246 c4 = eqn (Sb3-0-1-4 ∷ Sw23 ∷ []) (Sw23 ∷ Sb3-0-1-4 ∷ []) (c₂ (CS) (Swap))

-- nat 2 SBOX(3;0;1;4): 2 steps
lem-nat-2-SBOX⟨3·0·1·4⟩ : WsL → ⟪ (Sw23 ∷ Sb3-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-1-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·0·1·4⟩ c4 = derive (Sw23 ∷ Sb3-0-1-4 ∷ []) (Sb2-0-1-4 ∷ Sw23 ∷ [])
  (rw⁻ 0 (q246 c4) ∷
   re 0 1 (Sb2-0-1-4 ∷ []) ∷ []) Eq.refl

private
  q247 : WsL → Eqn
  q247 c4 = eqn (Sb⁻3-0-1-4 ∷ Sw23 ∷ []) (Sw23 ∷ Sb⁻3-0-1-4 ∷ []) (c₂ (CS • CS • CS) (Swap))

-- nat 2 SBOXd(3;0;1;4): 2 steps
lem-nat-2-SBOXd⟨3·0·1·4⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻3-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-1-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·0·1·4⟩ c4 = derive (Sw23 ∷ Sb⁻3-0-1-4 ∷ []) (Sb⁻2-0-1-4 ∷ Sw23 ∷ [])
  (rw⁻ 0 (q247 c4) ∷
   re 0 1 (Sb⁻2-0-1-4 ∷ []) ∷ []) Eq.refl

private
  q248 : WsL → Eqn
  q248 c4 = eqn (Sw23 ∷ Bx3-0241 ∷ []) (Bx2-0341 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0241⟩ c4)
  q249 : WsL → Eqn
  q249 c4 = eqn (Sw23 ∷ Toff124 ∷ []) (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4)
  q250 : WsL → Eqn
  q250 c4 = eqn (Sw23 ∷ Sb3-0-1-4 ∷ []) (Sb2-0-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·1·4⟩ c4)
  q251 : WsL → Eqn
  q251 c4 = eqn (Sw23 ∷ Sb⁻3-0-1-4 ∷ []) (Sb⁻2-0-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·0·1·4⟩ c4)

-- nat 2 SBOX(3;0;24;1): 7 steps
lem-nat-2-SBOX⟨3·0·24·1⟩ : WsL → ⟪ (Sw23 ∷ Sb3-0-24-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-34-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·0·24·1⟩ c4 = derive (Sw23 ∷ Sb3-0-24-1 ∷ []) (Sb2-0-34-1 ∷ Sw23 ∷ [])
  (re 1 1 (Bx3-0241 ∷ Toff124 ∷ Sb3-0-1-4 ∷ Toff124 ∷ Sb⁻3-0-1-4 ∷ []) ∷
   rw 0 (q248 c4) ∷
   rw 1 (q249 c4) ∷
   rw 2 (q250 c4) ∷
   rw 3 (q249 c4) ∷
   rw 4 (q251 c4) ∷
   re 0 5 (Sb2-0-34-1 ∷ []) ∷ []) Eq.refl

private
  q252 : WsL → Eqn
  q252 c4 = eqn (Sb2-0-1-4 ∷ Sw34 ∷ []) (Sw34 ∷ Sb2-0-1-4 ∷ []) (c₂ (CS) (Swap ↑))

-- nat 3 SBOX(2;0;1;4): 2 steps
lem-nat-3-SBOX⟨2·0·1·4⟩ : WsL → ⟪ (Sw34 ∷ Sb2-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-1-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·0·1·4⟩ c4 = derive (Sw34 ∷ Sb2-0-1-4 ∷ []) (Sb2-0-1-3 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q252 c4) ∷
   re 0 1 (Sb2-0-1-3 ∷ []) ∷ []) Eq.refl

private
  q253 : WsL → Eqn
  q253 c4 = eqn (Sb⁻2-0-1-4 ∷ Sw34 ∷ []) (Sw34 ∷ Sb⁻2-0-1-4 ∷ []) (c₂ (CS • CS • CS) (Swap ↑))

-- nat 3 SBOXd(2;0;1;4): 2 steps
lem-nat-3-SBOXd⟨2·0·1·4⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻2-0-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-1-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·0·1·4⟩ c4 = derive (Sw34 ∷ Sb⁻2-0-1-4 ∷ []) (Sb⁻2-0-1-3 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q253 c4) ∷
   re 0 1 (Sb⁻2-0-1-3 ∷ []) ∷ []) Eq.refl

private
  q254 : WsL → Eqn
  q254 c4 = eqn (Sw34 ∷ Bx2-0341 ∷ []) (Bx2-0431 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·0341⟩ c4)
  q255 : WsL → Eqn
  q255 c4 = eqn (Sw34 ∷ Toff134 ∷ []) (Toff134 ∷ Sw34 ∷ []) (wl0129 c4)
  q256 : WsL → Eqn
  q256 c4 = eqn (Sw34 ∷ Sb2-0-1-4 ∷ []) (Sb2-0-1-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·1·4⟩ c4)
  q257 : WsL → Eqn
  q257 c4 = eqn (Sw34 ∷ Sb⁻2-0-1-4 ∷ []) (Sb⁻2-0-1-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·1·4⟩ c4)

-- nat 3 SBOX(2;0;34;1): 7 steps
lem-nat-3-SBOX⟨2·0·34·1⟩ : WsL → ⟪ (Sw34 ∷ Sb2-0-34-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-43-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·0·34·1⟩ c4 = derive (Sw34 ∷ Sb2-0-34-1 ∷ []) (Sb2-0-43-1 ∷ Sw34 ∷ [])
  (re 1 1 (Bx2-0341 ∷ Toff134 ∷ Sb2-0-1-4 ∷ Toff134 ∷ Sb⁻2-0-1-4 ∷ []) ∷
   rw 0 (q254 c4) ∷
   rw 1 (q255 c4) ∷
   rw 2 (q256 c4) ∷
   rw 3 (q255 c4) ∷
   rw 4 (q257 c4) ∷
   re 0 5 (Sb2-0-43-1 ∷ []) ∷ []) Eq.refl

-- nat 1 SBOX(1;0;2;3): 3 steps
lem-nat-1-SBOX⟨1·0·2·3⟩ : WsL → ⟪ (Sw12 ∷ Sb1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-1-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·0·2·3⟩ c4 = derive (Sw12 ∷ Sb1-0-2-3 ∷ []) (Sb2-0-1-3 ∷ Sw12 ∷ [])
  (re 1 1 (CS02 ∷ []) ∷
   rw 0 (q235 c4) ∷
   re 0 1 (Sb2-0-1-3 ∷ []) ∷ []) Eq.refl

-- nat 1 SBOXd(1;0;2;3): 3 steps
lem-nat-1-SBOXd⟨1·0·2·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-1-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·0·2·3⟩ c4 = derive (Sw12 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻2-0-1-3 ∷ Sw12 ∷ [])
  (re 1 1 (CS02⁻ ∷ []) ∷
   rw 0 (q236 c4) ∷
   re 0 1 (Sb⁻2-0-1-3 ∷ []) ∷ []) Eq.refl

private
  q258 : WsL → Eqn
  q258 c4 = eqn (Sw12 ∷ Bx1-0432 ∷ []) (Bx2-0431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·0432⟩ c4)
  q259 : WsL → Eqn
  q259 c4 = eqn (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) (wl0140 c4)
  q260 : WsL → Eqn
  q260 c4 = eqn (Sw12 ∷ Sb1-0-2-3 ∷ []) (Sb2-0-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·2·3⟩ c4)
  q261 : WsL → Eqn
  q261 c4 = eqn (Sw12 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻2-0-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·0·2·3⟩ c4)

-- nat 1 SBOX(1;0;43;2): 7 steps
lem-nat-1-SBOX⟨1·0·43·2⟩ : WsL → ⟪ (Sw12 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-43-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·0·43·2⟩ c4 = derive (Sw12 ∷ Sb1-0-43-2 ∷ []) (Sb2-0-43-1 ∷ Sw12 ∷ [])
  (re 1 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) ∷
   rw 0 (q258 c4) ∷
   rw 1 (q259 c4) ∷
   rw 2 (q260 c4) ∷
   rw 3 (q259 c4) ∷
   rw 4 (q261 c4) ∷
   re 0 5 (Sb2-0-43-1 ∷ []) ∷ []) Eq.refl

-- nat 1 SBOX(2;0;1;3): 3 steps
lem-nat-1-SBOX⟨2·0·1·3⟩ : WsL → ⟪ (Sw12 ∷ Sb2-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·0·1·3⟩ c4 = derive (Sw12 ∷ Sb2-0-1-3 ∷ []) (Sb1-0-2-3 ∷ Sw12 ∷ [])
  (re 1 1 (CS01 ∷ []) ∷
   rw 0 (q229 c4) ∷
   re 0 1 (Sb1-0-2-3 ∷ []) ∷ []) Eq.refl

-- nat 1 SBOXd(2;0;1;3): 3 steps
lem-nat-1-SBOXd⟨2·0·1·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·0·1·3⟩ c4 = derive (Sw12 ∷ Sb⁻2-0-1-3 ∷ []) (Sb⁻1-0-2-3 ∷ Sw12 ∷ [])
  (re 1 1 (CS01⁻ ∷ []) ∷
   rw 0 (q230 c4) ∷
   re 0 1 (Sb⁻1-0-2-3 ∷ []) ∷ []) Eq.refl

private
  q262 : WsL → Eqn
  q262 c4 = eqn (Sw12 ∷ Bx2-0431 ∷ []) (Bx1-0432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0431⟩ c4)
  q263 : WsL → Eqn
  q263 c4 = eqn (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) (wl0136 c4)
  q264 : WsL → Eqn
  q264 c4 = eqn (Sw12 ∷ Sb2-0-1-3 ∷ []) (Sb1-0-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·1·3⟩ c4)
  q265 : WsL → Eqn
  q265 c4 = eqn (Sw12 ∷ Sb⁻2-0-1-3 ∷ []) (Sb⁻1-0-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·1·3⟩ c4)

-- nat 1 SBOX(2;0;43;1): 7 steps
lem-nat-1-SBOX⟨2·0·43·1⟩ : WsL → ⟪ (Sw12 ∷ Sb2-0-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·0·43·1⟩ c4 = derive (Sw12 ∷ Sb2-0-43-1 ∷ []) (Sb1-0-43-2 ∷ Sw12 ∷ [])
  (re 1 1 (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) ∷
   rw 0 (q262 c4) ∷
   rw 1 (q263 c4) ∷
   rw 2 (q264 c4) ∷
   rw 3 (q263 c4) ∷
   rw 4 (q265 c4) ∷
   re 0 5 (Sb1-0-43-2 ∷ []) ∷ []) Eq.refl

private
  q266 : WsL → Eqn
  q266 c4 = eqn (Sw23 ∷ Bx1-0423 ∷ []) (Bx1-0432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0423⟩ c4)

-- nat 2 SBOX(1;0;42;3): 7 steps
lem-nat-2-SBOX⟨1·0·42·3⟩ : WsL → ⟪ (Sw23 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·0·42·3⟩ c4 = derive (Sw23 ∷ Sb1-0-42-3 ∷ []) (Sb1-0-43-2 ∷ Sw23 ∷ [])
  (re 1 1 (Bx1-0423 ∷ Toff324 ∷ Sb1-0-3-2 ∷ Toff324 ∷ Sb⁻1-0-3-2 ∷ []) ∷
   rw 0 (q266 c4) ∷
   rw 1 (q99 c4) ∷
   rw 2 (q98 c4) ∷
   rw 3 (q99 c4) ∷
   rw 4 (q100 c4) ∷
   re 0 5 (Sb1-0-43-2 ∷ []) ∷ []) Eq.refl

private
  q267 : WsL → Eqn
  q267 c4 = eqn (Sw12 ∷ Bx1-34 ∷ []) (Bx2-34 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·34⟩ c4)

-- nat 1 BOX(3;104): 8 steps
lem-nat-1-BOX⟨3·104⟩ : WsL → ⟪ (Sw12 ∷ Bx3-104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-204 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·104⟩ c4 = derive (Sw12 ∷ Bx3-104 ∷ []) (Bx3-204 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-34 ∷ Toff301 ∷ CCZ013 ∷ Bx1-34 ∷ []) ∷
   rw 0 (q42 c4) ∷
   rw 1 (q209 c4) ∷
   rw 2 (q267 c4) ∷
   rw 3 (q209 c4) ∷
   rw 4 (q42 c4) ∷
   rw 5 (q267 c4) ∷
   re 0 6 (Bx3-204 ∷ []) ∷ []) Eq.refl

private
  q268 : WsL → Eqn
  q268 c4 = eqn (CCZ123 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ123 ∷ []) (wl0111 c4)
  q269 : WsL → Eqn
  q269 c4 = eqn (Sw12 ∷ Toff123 ∷ []) (Toff213 ∷ Sw12 ∷ []) (wl0146 c4)
  q270 : WsL → Eqn
  q270 c4 = eqn (Sw12 ∷ Bx3-104 ∷ []) (Bx3-204 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·104⟩ c4)

-- nat 1 BOX(1;3204): 8 steps
lem-nat-1-BOX⟨1·3204⟩ : WsL → ⟪ (Sw12 ∷ Bx1-3204 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·3204⟩ c4 = derive (Sw12 ∷ Bx1-3204 ∷ []) (Bx2-3104 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-104 ∷ Toff123 ∷ CCZ123 ∷ Bx3-104 ∷ []) ∷
   rw⁻ 0 (q268 c4) ∷
   rw 1 (q269 c4) ∷
   rw 2 (q270 c4) ∷
   rw 3 (q269 c4) ∷
   rw⁻ 4 (q268 c4) ∷
   rw 5 (q270 c4) ∷
   re 0 6 (Bx2-3104 ∷ []) ∷ []) Eq.refl

private
  q271 : WsL → Eqn
  q271 c4 = eqn (Sw12 ∷ Bx2-34 ∷ []) (Bx1-34 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·34⟩ c4)

-- nat 1 BOX(3;204): 8 steps
lem-nat-1-BOX⟨3·204⟩ : WsL → ⟪ (Sw12 ∷ Bx3-204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-104 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·204⟩ c4 = derive (Sw12 ∷ Bx3-204 ∷ []) (Bx3-104 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) ∷
   rw 0 (q52 c4) ∷
   rw 1 (q206 c4) ∷
   rw 2 (q271 c4) ∷
   rw 3 (q206 c4) ∷
   rw 4 (q52 c4) ∷
   rw 5 (q271 c4) ∷
   re 0 6 (Bx3-104 ∷ []) ∷ []) Eq.refl

private
  q272 : WsL → Eqn
  q272 c4 = eqn (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) (wl0112 c4)
  q273 : WsL → Eqn
  q273 c4 = eqn (Sw12 ∷ Bx3-204 ∷ []) (Bx3-104 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·204⟩ c4)

-- nat 1 BOX(2;3104): 8 steps
lem-nat-1-BOX⟨2·3104⟩ : WsL → ⟪ (Sw12 ∷ Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3204 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·3104⟩ c4 = derive (Sw12 ∷ Bx2-3104 ∷ []) (Bx1-3204 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-204 ∷ Toff213 ∷ CCZ123 ∷ Bx3-204 ∷ []) ∷
   rw⁻ 0 (q268 c4) ∷
   rw 1 (q272 c4) ∷
   rw 2 (q273 c4) ∷
   rw 3 (q272 c4) ∷
   rw⁻ 4 (q268 c4) ∷
   rw 5 (q273 c4) ∷
   re 0 6 (Bx1-3204 ∷ []) ∷ []) Eq.refl
