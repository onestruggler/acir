{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R015 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0003 ; wl0005 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0015 ; wl0016 ; wl0017 ; wl0018 ; wl0019 ; wl0020 ; wl0021 ; wl0024 ; wl0025 ; wl0027 ; wl0030 ; wl0031 ; wl0032 ; wl0034 ; wl0035 ; wl0036 ; wl0048 ; wl0053 ; wl0061 ; wl0063 ; wl0065 ; wl0066 ; wl0078 ; wl0079 ; wl0084 ; wl0086 ; wl0088 ; wl0089 ; wl0092 ; wl0100 ; wl0102 ; wl0103 ; wl0105 ; wl0108 ; wl0109 ; wl0111 ; wl0112 ; wl0113 ; wl0115 ; wl0117 ; wl0127 ; wl0128 ; wl0130 ; wl0132 ; wl0133 ; wl0136 ; wl0140 ; wl0142 ; wl0144 ; wl0146 ; wl0152 ; wl0155 ; wl0157 ; wl0158 ; wl0159 ; wl0160)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF203 ; lem-nat-2-CCZ012 ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF301 ; lem-nat-1-TOFF302 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF201 ; lem-nat-3-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF304 ; lem-nat-0-TOFF314 ; lem-nat-0-TOFF403 ; lem-nat-2-TOFF413)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-BOX⟨3·41⟩ ; lem-nat-1-TOFF013 ; lem-nat-1-TOFF304 ; lem-nat-2-TOFF412)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-2-BOX⟨2·0314⟩ ; lem-nat-2-BOX⟨3·0214⟩ ; lem-nat-2-CZ02 ; lem-nat-2-CZ03 ; lem-nat-3-BOX⟨2·0413⟩ ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-BOX⟨3·04⟩ ; lem-nat-1-CZ01 ; lem-nat-1-CZ02 ; lem-nat-2-CZ13 ; lem-nat-3-CS13 ; lem-nat-3-CS14)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-TOFF134 ; lem-nat-2-CS02 ; lem-nat-2-CSd02 ; lem-nat-2-TOFF124)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-TOFF034 ; lem-nat-1-TOFF403 ; lem-nat-2-CS04 ; lem-nat-2-CSd04 ; lem-nat-3-BOX⟨4·03⟩ ; lem-nat-3-TOFF412)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-2-CSd03 ; lem-nat-3-CS03 ; lem-nat-3-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-TOFF124)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-0-BOX⟨0·1432⟩ ; lem-nat-2-TOFF134)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-0-BOX⟨3·02⟩ ; lem-nat-1-BOX⟨3·12⟩)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-3-TOFF312)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-1-BOX⟨0·32⟩ ; lem-nat-2-BOX⟨4·0312⟩)

private
  q1 : WsL → Eqn
  q1 c4 = eqn (Sw12 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4)
  q2 : WsL → Eqn
  q2 c4 = eqn (Sw12 ∷ Toff304 ∷ []) (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4)
  q3 : WsL → Eqn
  q3 c4 = eqn (Sw12 ∷ Bx0-32 ∷ []) (Bx0-31 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·32⟩ c4)

-- nat 1 BOX(3;042): 8 steps
lem-nat-1-BOX⟨3·042⟩ : WsL → ⟪ (Sw12 ∷ Bx3-042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-041 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·042⟩ c4 = derive (Sw12 ∷ Bx3-042 ∷ []) (Bx3-041 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) ∷
   rw 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 3 (q2 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q3 c4) ∷
   re 0 6 (Bx3-041 ∷ []) ∷ []) Eq.refl

private
  q4 : WsL → Eqn
  q4 c4 = eqn (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4)
  q5 : WsL → Eqn
  q5 c4 = eqn (Sw12 ∷ Toff013 ∷ []) (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4)
  q6 : WsL → Eqn
  q6 c4 = eqn (Sw12 ∷ Bx3-042 ∷ []) (Bx3-041 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·042⟩ c4)

-- nat 1 BOX(0;3142): 8 steps
lem-nat-1-BOX⟨0·3142⟩ : WsL → ⟪ (Sw12 ∷ Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·3142⟩ c4 = derive (Sw12 ∷ Bx0-3142 ∷ []) (Bx0-3241 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) ∷
   rw 0 (q4 c4) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   rw 3 (q5 c4) ∷
   rw 4 (q4 c4) ∷
   rw 5 (q6 c4) ∷
   re 0 6 (Bx0-3241 ∷ []) ∷ []) Eq.refl

private
  q7 : WsL → Eqn
  q7 c4 = eqn (Sw34 ∷ CCZ014 ∷ []) (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4)
  q8 : WsL → Eqn
  q8 c4 = eqn (Sw34 ∷ Toff014 ∷ []) (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4)
  q9 : WsL → Eqn
  q9 c4 = eqn (Sw34 ∷ Bx4-03 ∷ []) (Bx3-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·03⟩ c4)

-- nat 3 BOX(0;413): 8 steps
lem-nat-3-BOX⟨0·413⟩ : WsL → ⟪ (Sw34 ∷ Bx0-413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-314 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·413⟩ c4 = derive (Sw34 ∷ Bx0-413 ∷ []) (Bx0-314 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ CCZ014 ∷ Bx4-03 ∷ []) ∷
   rw 0 (q7 c4) ∷
   rw 1 (q8 c4) ∷
   rw 2 (q9 c4) ∷
   rw 3 (q8 c4) ∷
   rw 4 (q7 c4) ∷
   rw 5 (q9 c4) ∷
   re 0 6 (Bx0-314 ∷ []) ∷ []) Eq.refl

private
  q10 : WsL → Eqn
  q10 c4 = eqn (Sw34 ∷ CCZ024 ∷ []) (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4)
  q11 : WsL → Eqn
  q11 c4 = eqn (Sw34 ∷ Toff402 ∷ []) (Toff302 ∷ Sw34 ∷ []) (lem-nat-3-TOFF402 c4)
  q12 : WsL → Eqn
  q12 c4 = eqn (Sw34 ∷ Bx0-413 ∷ []) (Bx0-314 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·413⟩ c4)

-- nat 3 BOX(4;0213): 8 steps
lem-nat-3-BOX⟨4·0213⟩ : WsL → ⟪ (Sw34 ∷ Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·0213⟩ c4 = derive (Sw34 ∷ Bx4-0213 ∷ []) (Bx3-0214 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-413 ∷ Toff402 ∷ CCZ024 ∷ Bx0-413 ∷ []) ∷
   rw 0 (q10 c4) ∷
   rw 1 (q11 c4) ∷
   rw 2 (q12 c4) ∷
   rw 3 (q11 c4) ∷
   rw 4 (q10 c4) ∷
   rw 5 (q12 c4) ∷
   re 0 6 (Bx3-0214 ∷ []) ∷ []) Eq.refl

private
  q13 : WsL → Eqn
  q13 c4 = eqn (CZ13 ∷ Sw01 ∷ []) (Sw01 ∷ CZ03 ∷ []) (wl0092 c4)

-- nat 0 BOX(1;30): 3 steps
lem-nat-0-BOX⟨1·30⟩ : WsL → ⟪ (Sw01 ∷ Bx1-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-31 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·30⟩ c4 = derive (Sw01 ∷ Bx1-30 ∷ []) (Bx0-31 ∷ Sw01 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw⁻ 0 (q13 c4) ∷
   re 0 1 (Bx0-31 ∷ []) ∷ []) Eq.refl

private
  q14 : WsL → Eqn
  q14 c4 = eqn (Sw01 ∷ CCZ134 ∷ []) (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4)
  q15 : WsL → Eqn
  q15 c4 = eqn (Sw01 ∷ Toff314 ∷ []) (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4)
  q16 : WsL → Eqn
  q16 c4 = eqn (Sw01 ∷ Bx1-30 ∷ []) (Bx0-31 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·30⟩ c4)

-- nat 0 BOX(3;140): 8 steps
lem-nat-0-BOX⟨3·140⟩ : WsL → ⟪ (Sw01 ∷ Bx3-140 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-041 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·140⟩ c4 = derive (Sw01 ∷ Bx3-140 ∷ []) (Bx3-041 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-30 ∷ Toff314 ∷ CCZ134 ∷ Bx1-30 ∷ []) ∷
   rw 0 (q14 c4) ∷
   rw 1 (q15 c4) ∷
   rw 2 (q16 c4) ∷
   rw 3 (q15 c4) ∷
   rw 4 (q14 c4) ∷
   rw 5 (q16 c4) ∷
   re 0 6 (Bx3-041 ∷ []) ∷ []) Eq.refl

private
  q17 : WsL → Eqn
  q17 c4 = eqn (CCZ023 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ123 ∷ []) (wl0003 c4)
  q18 : WsL → Eqn
  q18 c4 = eqn (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) (wl0053 c4)
  q19 : WsL → Eqn
  q19 c4 = eqn (Sw01 ∷ Bx3-140 ∷ []) (Bx3-041 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·140⟩ c4)

-- nat 0 BOX(1;3240): 8 steps
lem-nat-0-BOX⟨1·3240⟩ : WsL → ⟪ (Sw01 ∷ Bx1-3240 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·3240⟩ c4 = derive (Sw01 ∷ Bx1-3240 ∷ []) (Bx0-3241 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-140 ∷ Toff123 ∷ CCZ123 ∷ Bx3-140 ∷ []) ∷
   rw⁻ 0 (q17 c4) ∷
   rw 1 (q18 c4) ∷
   rw 2 (q19 c4) ∷
   rw 3 (q18 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 5 (q19 c4) ∷
   re 0 6 (Bx0-3241 ∷ []) ∷ []) Eq.refl

private
  q20 : WsL → Eqn
  q20 c4 = eqn (CZ03 ∷ Sw01 ∷ []) (Sw01 ∷ CZ13 ∷ []) (wl0088 c4)

-- nat 0 BOX(0;31): 3 steps
lem-nat-0-BOX⟨0·31⟩ : WsL → ⟪ (Sw01 ∷ Bx0-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-30 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·31⟩ c4 = derive (Sw01 ∷ Bx0-31 ∷ []) (Bx1-30 ∷ Sw01 ∷ [])
  (re 1 1 (CZ13 ∷ []) ∷
   rw⁻ 0 (q20 c4) ∷
   re 0 1 (Bx1-30 ∷ []) ∷ []) Eq.refl

private
  q21 : WsL → Eqn
  q21 c4 = eqn (Sw01 ∷ CCZ034 ∷ []) (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4)
  q22 : WsL → Eqn
  q22 c4 = eqn (Sw01 ∷ Toff304 ∷ []) (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4)
  q23 : WsL → Eqn
  q23 c4 = eqn (Sw01 ∷ Bx0-31 ∷ []) (Bx1-30 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·31⟩ c4)

-- nat 0 BOX(3;041): 8 steps
lem-nat-0-BOX⟨3·041⟩ : WsL → ⟪ (Sw01 ∷ Bx3-041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-140 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·041⟩ c4 = derive (Sw01 ∷ Bx3-041 ∷ []) (Bx3-140 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) ∷
   rw 0 (q21 c4) ∷
   rw 1 (q22 c4) ∷
   rw 2 (q23 c4) ∷
   rw 3 (q22 c4) ∷
   rw 4 (q21 c4) ∷
   rw 5 (q23 c4) ∷
   re 0 6 (Bx3-140 ∷ []) ∷ []) Eq.refl

private
  q24 : WsL → Eqn
  q24 c4 = eqn (CCZ123 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ023 ∷ []) (wl0103 c4)
  q25 : WsL → Eqn
  q25 c4 = eqn (Sw01 ∷ Toff023 ∷ []) (Toff123 ∷ Sw01 ∷ []) (wl0108 c4)
  q26 : WsL → Eqn
  q26 c4 = eqn (Sw01 ∷ Bx3-041 ∷ []) (Bx3-140 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·041⟩ c4)

-- nat 0 BOX(0;3241): 8 steps
lem-nat-0-BOX⟨0·3241⟩ : WsL → ⟪ (Sw01 ∷ Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3240 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·3241⟩ c4 = derive (Sw01 ∷ Bx0-3241 ∷ []) (Bx1-3240 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-041 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ []) ∷
   rw⁻ 0 (q24 c4) ∷
   rw 1 (q25 c4) ∷
   rw 2 (q26 c4) ∷
   rw 3 (q25 c4) ∷
   rw⁻ 4 (q24 c4) ∷
   rw 5 (q26 c4) ∷
   re 0 6 (Bx1-3240 ∷ []) ∷ []) Eq.refl

private
  q27 : WsL → Eqn
  q27 c4 = eqn (Sw23 ∷ CZ02 ∷ []) (CZ03 ∷ Sw23 ∷ []) (lem-nat-2-CZ02 c4)

-- nat 2 BOX(3;20): 3 steps
lem-nat-2-BOX⟨3·20⟩ : WsL → ⟪ (Sw23 ∷ Bx3-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-30 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·20⟩ c4 = derive (Sw23 ∷ Bx3-20 ∷ []) (Bx2-30 ∷ Sw23 ∷ [])
  (re 1 1 (CZ02 ∷ []) ∷
   rw 0 (q27 c4) ∷
   re 0 1 (Bx2-30 ∷ []) ∷ []) Eq.refl

private
  q28 : WsL → Eqn
  q28 c4 = eqn (CCZ234 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ234 ∷ []) (wl0086 c4)
  q29 : WsL → Eqn
  q29 c4 = eqn (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) (wl0127 c4)
  q30 : WsL → Eqn
  q30 c4 = eqn (Sw23 ∷ Bx3-20 ∷ []) (Bx2-30 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·20⟩ c4)

-- nat 2 BOX(2;340): 8 steps
lem-nat-2-BOX⟨2·340⟩ : WsL → ⟪ (Sw23 ∷ Bx2-340 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-240 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·340⟩ c4 = derive (Sw23 ∷ Bx2-340 ∷ []) (Bx3-240 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) ∷
   rw⁻ 0 (q28 c4) ∷
   rw 1 (q29 c4) ∷
   rw 2 (q30 c4) ∷
   rw 3 (q29 c4) ∷
   rw⁻ 4 (q28 c4) ∷
   rw 5 (q30 c4) ∷
   re 0 6 (Bx3-240 ∷ []) ∷ []) Eq.refl

private
  q31 : WsL → Eqn
  q31 c4 = eqn (CCZ123 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ123 ∷ []) (wl0113 c4)
  q32 : WsL → Eqn
  q32 c4 = eqn (Sw23 ∷ Toff312 ∷ []) (Toff213 ∷ Sw23 ∷ []) (wl0157 c4)
  q33 : WsL → Eqn
  q33 c4 = eqn (Sw23 ∷ Bx2-340 ∷ []) (Bx3-240 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·340⟩ c4)

-- nat 2 BOX(3;2140): 8 steps
lem-nat-2-BOX⟨3·2140⟩ : WsL → ⟪ (Sw23 ∷ Bx3-2140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·2140⟩ c4 = derive (Sw23 ∷ Bx3-2140 ∷ []) (Bx2-3140 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-340 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ []) ∷
   rw⁻ 0 (q31 c4) ∷
   rw 1 (q32 c4) ∷
   rw 2 (q33 c4) ∷
   rw 3 (q32 c4) ∷
   rw⁻ 4 (q31 c4) ∷
   rw 5 (q33 c4) ∷
   re 0 6 (Bx2-3140 ∷ []) ∷ []) Eq.refl

private
  q34 : WsL → Eqn
  q34 c4 = eqn (Sw23 ∷ CZ03 ∷ []) (CZ02 ∷ Sw23 ∷ []) (lem-nat-2-CZ03 c4)

-- nat 2 BOX(2;30): 3 steps
lem-nat-2-BOX⟨2·30⟩ : WsL → ⟪ (Sw23 ∷ Bx2-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-20 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·30⟩ c4 = derive (Sw23 ∷ Bx2-30 ∷ []) (Bx3-20 ∷ Sw23 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw 0 (q34 c4) ∷
   re 0 1 (Bx3-20 ∷ []) ∷ []) Eq.refl

private
  q35 : WsL → Eqn
  q35 c4 = eqn (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) (wl0144 c4)
  q36 : WsL → Eqn
  q36 c4 = eqn (Sw23 ∷ Bx2-30 ∷ []) (Bx3-20 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·30⟩ c4)

-- nat 2 BOX(3;240): 8 steps
lem-nat-2-BOX⟨3·240⟩ : WsL → ⟪ (Sw23 ∷ Bx3-240 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-340 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·240⟩ c4 = derive (Sw23 ∷ Bx3-240 ∷ []) (Bx2-340 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) ∷
   rw⁻ 0 (q28 c4) ∷
   rw 1 (q35 c4) ∷
   rw 2 (q36 c4) ∷
   rw 3 (q35 c4) ∷
   rw⁻ 4 (q28 c4) ∷
   rw 5 (q36 c4) ∷
   re 0 6 (Bx2-340 ∷ []) ∷ []) Eq.refl

private
  q37 : WsL → Eqn
  q37 c4 = eqn (Sw23 ∷ Toff213 ∷ []) (Toff312 ∷ Sw23 ∷ []) (wl0158 c4)
  q38 : WsL → Eqn
  q38 c4 = eqn (Sw23 ∷ Bx3-240 ∷ []) (Bx2-340 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·240⟩ c4)

-- nat 2 BOX(2;3140): 8 steps
lem-nat-2-BOX⟨2·3140⟩ : WsL → ⟪ (Sw23 ∷ Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·3140⟩ c4 = derive (Sw23 ∷ Bx2-3140 ∷ []) (Bx3-2140 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ []) ∷
   rw⁻ 0 (q31 c4) ∷
   rw 1 (q37 c4) ∷
   rw 2 (q38 c4) ∷
   rw 3 (q37 c4) ∷
   rw⁻ 4 (q31 c4) ∷
   rw 5 (q38 c4) ∷
   re 0 6 (Bx3-2140 ∷ []) ∷ []) Eq.refl

private
  q39 : WsL → Eqn
  q39 c4 = eqn (Bx4-20 ∷ Sw34 ∷ []) (Sw34 ∷ Bx4-20 ∷ []) (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))

-- nat 3 BOX(4;20): 2 steps
lem-nat-3-BOX⟨4·20⟩ : WsL → ⟪ (Sw34 ∷ Bx4-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-20 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·20⟩ c4 = derive (Sw34 ∷ Bx4-20 ∷ []) (Bx3-20 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q39 c4) ∷
   re 0 1 (Bx3-20 ∷ []) ∷ []) Eq.refl

private
  q40 : WsL → Eqn
  q40 c4 = eqn (CCZ234 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ234 ∷ []) (wl0155 c4)
  q41 : WsL → Eqn
  q41 c4 = eqn (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) (wl0128 c4)
  q42 : WsL → Eqn
  q42 c4 = eqn (Sw34 ∷ Bx4-20 ∷ []) (Bx3-20 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·20⟩ c4)

-- nat 3 BOX(2;430): 8 steps
lem-nat-3-BOX⟨2·430⟩ : WsL → ⟪ (Sw34 ∷ Bx2-430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-340 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·430⟩ c4 = derive (Sw34 ∷ Bx2-430 ∷ []) (Bx2-340 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) ∷
   rw⁻ 0 (q40 c4) ∷
   rw 1 (q41 c4) ∷
   rw 2 (q42 c4) ∷
   rw 3 (q41 c4) ∷
   rw⁻ 4 (q40 c4) ∷
   rw 5 (q42 c4) ∷
   re 0 6 (Bx2-340 ∷ []) ∷ []) Eq.refl

private
  q43 : WsL → Eqn
  q43 c4 = eqn (Sw34 ∷ CCZ124 ∷ []) (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4)
  q44 : WsL → Eqn
  q44 c4 = eqn (Sw34 ∷ Toff412 ∷ []) (Toff312 ∷ Sw34 ∷ []) (lem-nat-3-TOFF412 c4)
  q45 : WsL → Eqn
  q45 c4 = eqn (Sw34 ∷ Bx2-430 ∷ []) (Bx2-340 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·430⟩ c4)

-- nat 3 BOX(4;2130): 8 steps
lem-nat-3-BOX⟨4·2130⟩ : WsL → ⟪ (Sw34 ∷ Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2140 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·2130⟩ c4 = derive (Sw34 ∷ Bx4-2130 ∷ []) (Bx3-2140 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-430 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ []) ∷
   rw 0 (q43 c4) ∷
   rw 1 (q44 c4) ∷
   rw 2 (q45 c4) ∷
   rw 3 (q44 c4) ∷
   rw 4 (q43 c4) ∷
   rw 5 (q45 c4) ∷
   re 0 6 (Bx3-2140 ∷ []) ∷ []) Eq.refl

private
  q46 : WsL → Eqn
  q46 c4 = eqn (Bx3-20 ∷ Sw34 ∷ []) (Sw34 ∷ Bx3-20 ∷ []) (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))

-- nat 3 BOX(3;20): 2 steps
lem-nat-3-BOX⟨3·20⟩ : WsL → ⟪ (Sw34 ∷ Bx3-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-20 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·20⟩ c4 = derive (Sw34 ∷ Bx3-20 ∷ []) (Bx4-20 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q46 c4) ∷
   re 0 1 (Bx4-20 ∷ []) ∷ []) Eq.refl

private
  q47 : WsL → Eqn
  q47 c4 = eqn (Sw34 ∷ Bx3-20 ∷ []) (Bx4-20 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·20⟩ c4)

-- nat 3 BOX(2;340): 8 steps
lem-nat-3-BOX⟨2·340⟩ : WsL → ⟪ (Sw34 ∷ Bx2-340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-430 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·340⟩ c4 = derive (Sw34 ∷ Bx2-340 ∷ []) (Bx2-430 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-20 ∷ Toff234 ∷ CCZ234 ∷ Bx3-20 ∷ []) ∷
   rw⁻ 0 (q40 c4) ∷
   rw 1 (q41 c4) ∷
   rw 2 (q47 c4) ∷
   rw 3 (q41 c4) ∷
   rw⁻ 4 (q40 c4) ∷
   rw 5 (q47 c4) ∷
   re 0 6 (Bx2-430 ∷ []) ∷ []) Eq.refl

private
  q48 : WsL → Eqn
  q48 c4 = eqn (Sw34 ∷ CCZ123 ∷ []) (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4)
  q49 : WsL → Eqn
  q49 c4 = eqn (Sw34 ∷ Toff312 ∷ []) (Toff412 ∷ Sw34 ∷ []) (lem-nat-3-TOFF312 c4)
  q50 : WsL → Eqn
  q50 c4 = eqn (Sw34 ∷ Bx2-340 ∷ []) (Bx2-430 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·340⟩ c4)

-- nat 3 BOX(3;2140): 8 steps
lem-nat-3-BOX⟨3·2140⟩ : WsL → ⟪ (Sw34 ∷ Bx3-2140 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·2140⟩ c4 = derive (Sw34 ∷ Bx3-2140 ∷ []) (Bx4-2130 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-340 ∷ Toff312 ∷ CCZ123 ∷ Bx2-340 ∷ []) ∷
   rw 0 (q48 c4) ∷
   rw 1 (q49 c4) ∷
   rw 2 (q50 c4) ∷
   rw 3 (q49 c4) ∷
   rw 4 (q48 c4) ∷
   rw 5 (q50 c4) ∷
   re 0 6 (Bx4-2130 ∷ []) ∷ []) Eq.refl

private
  q51 : WsL → Eqn
  q51 c4 = eqn (Sw12 ∷ CZ01 ∷ []) (CZ02 ∷ Sw12 ∷ []) (lem-nat-1-CZ01 c4)

-- nat 1 BOX(4;10): 3 steps
lem-nat-1-BOX⟨4·10⟩ : WsL → ⟪ (Sw12 ∷ Bx4-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-20 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·10⟩ c4 = derive (Sw12 ∷ Bx4-10 ∷ []) (Bx4-20 ∷ Sw12 ∷ [])
  (re 1 1 (CZ01 ∷ []) ∷
   rw 0 (q51 c4) ∷
   re 0 1 (Bx4-20 ∷ []) ∷ []) Eq.refl

private
  q52 : WsL → Eqn
  q52 c4 = eqn (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) (wl0084 c4)
  q53 : WsL → Eqn
  q53 c4 = eqn (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) (wl0136 c4)
  q54 : WsL → Eqn
  q54 c4 = eqn (Sw12 ∷ Bx4-10 ∷ []) (Bx4-20 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·10⟩ c4)

-- nat 1 BOX(1;430): 8 steps
lem-nat-1-BOX⟨1·430⟩ : WsL → ⟪ (Sw12 ∷ Bx1-430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-430 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·430⟩ c4 = derive (Sw12 ∷ Bx1-430 ∷ []) (Bx2-430 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) ∷
   rw⁻ 0 (q52 c4) ∷
   rw 1 (q53 c4) ∷
   rw 2 (q54 c4) ∷
   rw 3 (q53 c4) ∷
   rw⁻ 4 (q52 c4) ∷
   rw 5 (q54 c4) ∷
   re 0 6 (Bx2-430 ∷ []) ∷ []) Eq.refl

private
  q55 : WsL → Eqn
  q55 c4 = eqn (CCZ124 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ124 ∷ []) (wl0078 c4)
  q56 : WsL → Eqn
  q56 c4 = eqn (Sw12 ∷ Toff412 ∷ []) (Toff412 ∷ Sw12 ∷ []) (wl0079 c4)
  q57 : WsL → Eqn
  q57 c4 = eqn (Sw12 ∷ Bx1-430 ∷ []) (Bx2-430 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·430⟩ c4)

-- nat 1 BOX(4;1230): 8 steps
lem-nat-1-BOX⟨4·1230⟩ : WsL → ⟪ (Sw12 ∷ Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·1230⟩ c4 = derive (Sw12 ∷ Bx4-1230 ∷ []) (Bx4-2130 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ []) ∷
   rw⁻ 0 (q55 c4) ∷
   rw 1 (q56 c4) ∷
   rw 2 (q57 c4) ∷
   rw 3 (q56 c4) ∷
   rw⁻ 4 (q55 c4) ∷
   rw 5 (q57 c4) ∷
   re 0 6 (Bx4-2130 ∷ []) ∷ []) Eq.refl

private
  q58 : WsL → Eqn
  q58 c4 = eqn (Sw12 ∷ CZ02 ∷ []) (CZ01 ∷ Sw12 ∷ []) (lem-nat-1-CZ02 c4)

-- nat 1 BOX(4;20): 3 steps
lem-nat-1-BOX⟨4·20⟩ : WsL → ⟪ (Sw12 ∷ Bx4-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-10 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·20⟩ c4 = derive (Sw12 ∷ Bx4-20 ∷ []) (Bx4-10 ∷ Sw12 ∷ [])
  (re 1 1 (CZ02 ∷ []) ∷
   rw 0 (q58 c4) ∷
   re 0 1 (Bx4-10 ∷ []) ∷ []) Eq.refl

private
  q59 : WsL → Eqn
  q59 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl0034 c4)
  q60 : WsL → Eqn
  q60 c4 = eqn (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) (wl0140 c4)
  q61 : WsL → Eqn
  q61 c4 = eqn (Sw12 ∷ Bx4-20 ∷ []) (Bx4-10 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·20⟩ c4)

-- nat 1 BOX(2;430): 8 steps
lem-nat-1-BOX⟨2·430⟩ : WsL → ⟪ (Sw12 ∷ Bx2-430 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-430 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·430⟩ c4 = derive (Sw12 ∷ Bx2-430 ∷ []) (Bx1-430 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) ∷
   rw⁻ 0 (q59 c4) ∷
   rw 1 (q60 c4) ∷
   rw 2 (q61 c4) ∷
   rw 3 (q60 c4) ∷
   rw⁻ 4 (q59 c4) ∷
   rw 5 (q61 c4) ∷
   re 0 6 (Bx1-430 ∷ []) ∷ []) Eq.refl

private
  q62 : WsL → Eqn
  q62 c4 = eqn (Sw12 ∷ Bx2-430 ∷ []) (Bx1-430 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·430⟩ c4)

-- nat 1 BOX(4;2130): 8 steps
lem-nat-1-BOX⟨4·2130⟩ : WsL → ⟪ (Sw12 ∷ Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·2130⟩ c4 = derive (Sw12 ∷ Bx4-2130 ∷ []) (Bx4-1230 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-430 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ []) ∷
   rw⁻ 0 (q55 c4) ∷
   rw 1 (q56 c4) ∷
   rw 2 (q62 c4) ∷
   rw 3 (q56 c4) ∷
   rw⁻ 4 (q55 c4) ∷
   rw 5 (q62 c4) ∷
   re 0 6 (Bx4-1230 ∷ []) ∷ []) Eq.refl

private
  q63 : WsL → Eqn
  q63 c4 = eqn (Sw23 ∷ CCZ124 ∷ []) (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4)
  q64 : WsL → Eqn
  q64 c4 = eqn (Sw23 ∷ Toff124 ∷ []) (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4)
  q65 : WsL → Eqn
  q65 c4 = eqn (Bx4-10 ∷ Sw23 ∷ []) (Sw23 ∷ Bx4-10 ∷ []) (c₂ (CZ) (Swap))

-- nat 2 BOX(1;420): 8 steps
lem-nat-2-BOX⟨1·420⟩ : WsL → ⟪ (Sw23 ∷ Bx1-420 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-430 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·420⟩ c4 = derive (Sw23 ∷ Bx1-420 ∷ []) (Bx1-430 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) ∷
   rw 0 (q63 c4) ∷
   rw 1 (q64 c4) ∷
   rw⁻ 2 (q65 c4) ∷
   rw 3 (q64 c4) ∷
   rw 4 (q63 c4) ∷
   rw⁻ 5 (q65 c4) ∷
   re 0 6 (Bx1-430 ∷ []) ∷ []) Eq.refl

private
  q66 : WsL → Eqn
  q66 c4 = eqn (Sw23 ∷ CCZ134 ∷ []) (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4)
  q67 : WsL → Eqn
  q67 c4 = eqn (Sw23 ∷ Toff413 ∷ []) (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4)
  q68 : WsL → Eqn
  q68 c4 = eqn (Sw23 ∷ Bx1-420 ∷ []) (Bx1-430 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·420⟩ c4)

-- nat 2 BOX(4;1320): 8 steps
lem-nat-2-BOX⟨4·1320⟩ : WsL → ⟪ (Sw23 ∷ Bx4-1320 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·1320⟩ c4 = derive (Sw23 ∷ Bx4-1320 ∷ []) (Bx4-1230 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff413 ∷ Bx1-420 ∷ Toff413 ∷ CCZ134 ∷ Bx1-420 ∷ []) ∷
   rw 0 (q66 c4) ∷
   rw 1 (q67 c4) ∷
   rw 2 (q68 c4) ∷
   rw 3 (q67 c4) ∷
   rw 4 (q66 c4) ∷
   rw 5 (q68 c4) ∷
   re 0 6 (Bx4-1230 ∷ []) ∷ []) Eq.refl

private
  q69 : WsL → Eqn
  q69 c4 = eqn (Sw23 ∷ Toff134 ∷ []) (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4)

-- nat 2 BOX(1;430): 8 steps
lem-nat-2-BOX⟨1·430⟩ : WsL → ⟪ (Sw23 ∷ Bx1-430 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-420 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·430⟩ c4 = derive (Sw23 ∷ Bx1-430 ∷ []) (Bx1-420 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) ∷
   rw 0 (q66 c4) ∷
   rw 1 (q69 c4) ∷
   rw⁻ 2 (q65 c4) ∷
   rw 3 (q69 c4) ∷
   rw 4 (q66 c4) ∷
   rw⁻ 5 (q65 c4) ∷
   re 0 6 (Bx1-420 ∷ []) ∷ []) Eq.refl

private
  q70 : WsL → Eqn
  q70 c4 = eqn (Sw23 ∷ Toff412 ∷ []) (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4)
  q71 : WsL → Eqn
  q71 c4 = eqn (Sw23 ∷ Bx1-430 ∷ []) (Bx1-420 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·430⟩ c4)

-- nat 2 BOX(4;1230): 8 steps
lem-nat-2-BOX⟨4·1230⟩ : WsL → ⟪ (Sw23 ∷ Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·1230⟩ c4 = derive (Sw23 ∷ Bx4-1230 ∷ []) (Bx4-1320 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ []) ∷
   rw 0 (q63 c4) ∷
   rw 1 (q70 c4) ∷
   rw 2 (q71 c4) ∷
   rw 3 (q70 c4) ∷
   rw 4 (q63 c4) ∷
   rw 5 (q71 c4) ∷
   re 0 6 (Bx4-1320 ∷ []) ∷ []) Eq.refl

private
  q72 : WsL → Eqn
  q72 c4 = eqn (Sw23 ∷ CS04 ∷ []) (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 c4)

-- nat 2 SBOX(3;0;4;1): 3 steps
lem-nat-2-SBOX⟨3·0·4·1⟩ : WsL → ⟪ (Sw23 ∷ Sb3-0-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-4-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·0·4·1⟩ c4 = derive (Sw23 ∷ Sb3-0-4-1 ∷ []) (Sb2-0-4-1 ∷ Sw23 ∷ [])
  (re 1 1 (CS04 ∷ []) ∷
   rw 0 (q72 c4) ∷
   re 0 1 (Sb2-0-4-1 ∷ []) ∷ []) Eq.refl

private
  q73 : WsL → Eqn
  q73 c4 = eqn (Sw23 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 c4)

-- nat 2 SBOXd(3;0;4;1): 3 steps
lem-nat-2-SBOXd⟨3·0·4·1⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻3-0-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-4-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·0·4·1⟩ c4 = derive (Sw23 ∷ Sb⁻3-0-4-1 ∷ []) (Sb⁻2-0-4-1 ∷ Sw23 ∷ [])
  (re 1 1 (CS04⁻ ∷ []) ∷
   rw 0 (q73 c4) ∷
   re 0 1 (Sb⁻2-0-4-1 ∷ []) ∷ []) Eq.refl

private
  q74 : WsL → Eqn
  q74 c4 = eqn (Sw23 ∷ Bx3-0214 ∷ []) (Bx2-0314 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0214⟩ c4)
  q75 : WsL → Eqn
  q75 c4 = eqn (Sw23 ∷ Sb3-0-4-1 ∷ []) (Sb2-0-4-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·4·1⟩ c4)
  q76 : WsL → Eqn
  q76 c4 = eqn (Sw23 ∷ Sb⁻3-0-4-1 ∷ []) (Sb⁻2-0-4-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·0·4·1⟩ c4)

-- nat 2 SBOX(3;0;21;4): 7 steps
lem-nat-2-SBOX⟨3·0·21·4⟩ : WsL → ⟪ (Sw23 ∷ Sb3-0-21-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-31-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·0·21·4⟩ c4 = derive (Sw23 ∷ Sb3-0-21-4 ∷ []) (Sb2-0-31-4 ∷ Sw23 ∷ [])
  (re 1 1 (Bx3-0214 ∷ Toff412 ∷ Sb3-0-4-1 ∷ Toff412 ∷ Sb⁻3-0-4-1 ∷ []) ∷
   rw 0 (q74 c4) ∷
   rw 1 (q70 c4) ∷
   rw 2 (q75 c4) ∷
   rw 3 (q70 c4) ∷
   rw 4 (q76 c4) ∷
   re 0 5 (Sb2-0-31-4 ∷ []) ∷ []) Eq.refl

private
  q77 : WsL → Eqn
  q77 c4 = eqn (Sw23 ∷ CS02 ∷ []) (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4)

-- nat 2 SBOX(4;0;2;1): 3 steps
lem-nat-2-SBOX⟨4·0·2·1⟩ : WsL → ⟪ (Sw23 ∷ Sb4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨4·0·2·1⟩ c4 = derive (Sw23 ∷ Sb4-0-2-1 ∷ []) (Sb4-0-3-1 ∷ Sw23 ∷ [])
  (re 1 1 (CS02 ∷ []) ∷
   rw 0 (q77 c4) ∷
   re 0 1 (Sb4-0-3-1 ∷ []) ∷ []) Eq.refl

private
  q78 : WsL → Eqn
  q78 c4 = eqn (Sw23 ∷ CS02⁻ ∷ []) (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 c4)

-- nat 2 SBOXd(4;0;2;1): 3 steps
lem-nat-2-SBOXd⟨4·0·2·1⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨4·0·2·1⟩ c4 = derive (Sw23 ∷ Sb⁻4-0-2-1 ∷ []) (Sb⁻4-0-3-1 ∷ Sw23 ∷ [])
  (re 1 1 (CS02⁻ ∷ []) ∷
   rw 0 (q78 c4) ∷
   re 0 1 (Sb⁻4-0-3-1 ∷ []) ∷ []) Eq.refl

private
  q79 : WsL → Eqn
  q79 c4 = eqn (Sw23 ∷ Bx4-0312 ∷ []) (Bx4-0213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·0312⟩ c4)
  q80 : WsL → Eqn
  q80 c4 = eqn (Sw23 ∷ Sb4-0-2-1 ∷ []) (Sb4-0-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨4·0·2·1⟩ c4)
  q81 : WsL → Eqn
  q81 c4 = eqn (Sw23 ∷ Sb⁻4-0-2-1 ∷ []) (Sb⁻4-0-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨4·0·2·1⟩ c4)

-- nat 2 SBOX(4;0;31;2): 7 steps
lem-nat-2-SBOX⟨4·0·31·2⟩ : WsL → ⟪ (Sw23 ∷ Sb4-0-31-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-21-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨4·0·31·2⟩ c4 = derive (Sw23 ∷ Sb4-0-31-2 ∷ []) (Sb4-0-21-3 ∷ Sw23 ∷ [])
  (re 1 1 (Bx4-0312 ∷ Toff213 ∷ Sb4-0-2-1 ∷ Toff213 ∷ Sb⁻4-0-2-1 ∷ []) ∷
   rw 0 (q79 c4) ∷
   rw 1 (q37 c4) ∷
   rw 2 (q80 c4) ∷
   rw 3 (q37 c4) ∷
   rw 4 (q81 c4) ∷
   re 0 5 (Sb4-0-21-3 ∷ []) ∷ []) Eq.refl

private
  q82 : WsL → Eqn
  q82 c4 = eqn (Sw01 ∷ Sb1-4-2-0 ∷ []) (Sb1-4-2-0 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))

-- nat 0 SBOX(1;4;2;0): 2 steps
lem-nat-0-SBOX⟨1·4·2·0⟩ : WsL → ⟪ (Sw01 ∷ Sb1-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-2-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·4·2·0⟩ c4 = derive (Sw01 ∷ Sb1-4-2-0 ∷ []) (Sb0-4-2-1 ∷ Sw01 ∷ [])
  (rw 0 (q82 c4) ∷
   re 0 1 (Sb0-4-2-1 ∷ []) ∷ []) Eq.refl

private
  q83 : WsL → Eqn
  q83 c4 = eqn (Sw01 ∷ Sb0-4-2-1 ∷ []) (Sb0-4-2-1 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))

-- nat 0 SBOX(0;4;2;1): 2 steps
lem-nat-0-SBOX⟨0·4·2·1⟩ : WsL → ⟪ (Sw01 ∷ Sb0-4-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-2-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·4·2·1⟩ c4 = derive (Sw01 ∷ Sb0-4-2-1 ∷ []) (Sb1-4-2-0 ∷ Sw01 ∷ [])
  (rw 0 (q83 c4) ∷
   re 0 1 (Sb1-4-2-0 ∷ []) ∷ []) Eq.refl

private
  q84 : WsL → Eqn
  q84 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl0017 c4)

-- nat 1 SBOX(1;4;2;0): 3 steps
lem-nat-1-SBOX⟨1·4·2·0⟩ : WsL → ⟪ (Sw12 ∷ Sb1-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-1-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·4·2·0⟩ c4 = derive (Sw12 ∷ Sb1-4-2-0 ∷ []) (Sb2-4-1-0 ∷ Sw12 ∷ [])
  (re 1 1 (CS24 ∷ []) ∷
   rw⁻ 0 (q84 c4) ∷
   re 0 1 (Sb2-4-1-0 ∷ []) ∷ []) Eq.refl

private
  q85 : WsL → Eqn
  q85 c4 = eqn (Sw34 ∷ CS13 ∷ []) (CS14 ∷ Sw34 ∷ []) (lem-nat-3-CS13 c4)

-- nat 3 SBOX(4;3;1;0): 3 steps
lem-nat-3-SBOX⟨4·3·1·0⟩ : WsL → ⟪ (Sw34 ∷ Sb4-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-1-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨4·3·1·0⟩ c4 = derive (Sw34 ∷ Sb4-3-1-0 ∷ []) (Sb3-4-1-0 ∷ Sw34 ∷ [])
  (re 1 1 (CS13 ∷ []) ∷
   rw 0 (q85 c4) ∷
   re 0 1 (Sb3-4-1-0 ∷ []) ∷ []) Eq.refl

private
  q86 : WsL → Eqn
  q86 c4 = eqn (Sw34 ∷ CS14 ∷ []) (CS13 ∷ Sw34 ∷ []) (lem-nat-3-CS14 c4)

-- nat 3 SBOX(3;4;1;0): 3 steps
lem-nat-3-SBOX⟨3·4·1·0⟩ : WsL → ⟪ (Sw34 ∷ Sb3-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-3-1-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨3·4·1·0⟩ c4 = derive (Sw34 ∷ Sb3-4-1-0 ∷ []) (Sb4-3-1-0 ∷ Sw34 ∷ [])
  (re 1 1 (CS14 ∷ []) ∷
   rw 0 (q86 c4) ∷
   re 0 1 (Sb4-3-1-0 ∷ []) ∷ []) Eq.refl

private
  q87 : WsL → Eqn
  q87 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl0024 c4)

-- nat 1 SBOX(4;3;2;0): 3 steps
lem-nat-1-SBOX⟨4·3·2·0⟩ : WsL → ⟪ (Sw12 ∷ Sb4-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-3-1-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨4·3·2·0⟩ c4 = derive (Sw12 ∷ Sb4-3-2-0 ∷ []) (Sb4-3-1-0 ∷ Sw12 ∷ [])
  (re 1 1 (CS23 ∷ []) ∷
   rw⁻ 0 (q87 c4) ∷
   re 0 1 (Sb4-3-1-0 ∷ []) ∷ []) Eq.refl

private
  q88 : WsL → Eqn
  q88 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl0025 c4)

-- nat 1 SBOX(4;3;1;0): 3 steps
lem-nat-1-SBOX⟨4·3·1·0⟩ : WsL → ⟪ (Sw12 ∷ Sb4-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-3-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨4·3·1·0⟩ c4 = derive (Sw12 ∷ Sb4-3-1-0 ∷ []) (Sb4-3-2-0 ∷ Sw12 ∷ [])
  (re 1 1 (CS13 ∷ []) ∷
   rw⁻ 0 (q88 c4) ∷
   re 0 1 (Sb4-3-2-0 ∷ []) ∷ []) Eq.refl

private
  q89 : WsL → Eqn
  q89 c4 = eqn (CS23 ∷ Sw23 ∷ []) (Sw23 ∷ CS23 ∷ []) (wl0152 c4)

-- nat 2 SBOX(4;2;3;0): 3 steps
lem-nat-2-SBOX⟨4·2·3·0⟩ : WsL → ⟪ (Sw23 ∷ Sb4-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-3-2-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨4·2·3·0⟩ c4 = derive (Sw23 ∷ Sb4-2-3-0 ∷ []) (Sb4-3-2-0 ∷ Sw23 ∷ [])
  (re 1 1 (CS23 ∷ []) ∷
   rw⁻ 0 (q89 c4) ∷
   re 0 1 (Sb4-3-2-0 ∷ []) ∷ []) Eq.refl

-- nat 2 SBOX(4;3;2;0): 3 steps
lem-nat-2-SBOX⟨4·3·2·0⟩ : WsL → ⟪ (Sw23 ∷ Sb4-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-3-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨4·3·2·0⟩ c4 = derive (Sw23 ∷ Sb4-3-2-0 ∷ []) (Sb4-2-3-0 ∷ Sw23 ∷ [])
  (re 1 1 (CS23 ∷ []) ∷
   rw⁻ 0 (q89 c4) ∷
   re 0 1 (Sb4-2-3-0 ∷ []) ∷ []) Eq.refl

-- nat 1 SBOX(4;1;3;0): 3 steps
lem-nat-1-SBOX⟨4·1·3·0⟩ : WsL → ⟪ (Sw12 ∷ Sb4-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨4·1·3·0⟩ c4 = derive (Sw12 ∷ Sb4-1-3-0 ∷ []) (Sb4-2-3-0 ∷ Sw12 ∷ [])
  (re 1 1 (CS13 ∷ []) ∷
   rw⁻ 0 (q88 c4) ∷
   re 0 1 (Sb4-2-3-0 ∷ []) ∷ []) Eq.refl

-- nat 1 SBOX(4;2;3;0): 3 steps
lem-nat-1-SBOX⟨4·2·3·0⟩ : WsL → ⟪ (Sw12 ∷ Sb4-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨4·2·3·0⟩ c4 = derive (Sw12 ∷ Sb4-2-3-0 ∷ []) (Sb4-1-3-0 ∷ Sw12 ∷ [])
  (re 1 1 (CS23 ∷ []) ∷
   rw⁻ 0 (q87 c4) ∷
   re 0 1 (Sb4-1-3-0 ∷ []) ∷ []) Eq.refl

private
  q90 : WsL → Eqn
  q90 c4 = eqn (CS13 ∷ Sw01 ∷ []) (Sw01 ∷ CS03 ∷ []) (wl0061 c4)

-- nat 0 SBOX(4;0;3;1): 3 steps
lem-nat-0-SBOX⟨4·0·3·1⟩ : WsL → ⟪ (Sw01 ∷ Sb4-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-3-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨4·0·3·1⟩ c4 = derive (Sw01 ∷ Sb4-0-3-1 ∷ []) (Sb4-1-3-0 ∷ Sw01 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   rw⁻ 0 (q90 c4) ∷
   re 0 1 (Sb4-1-3-0 ∷ []) ∷ []) Eq.refl

private
  q91 : WsL → Eqn
  q91 c4 = eqn (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) (wl0019 c4)

-- nat 0 SBOX(4;1;3;0): 3 steps
lem-nat-0-SBOX⟨4·1·3·0⟩ : WsL → ⟪ (Sw01 ∷ Sb4-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨4·1·3·0⟩ c4 = derive (Sw01 ∷ Sb4-1-3-0 ∷ []) (Sb4-0-3-1 ∷ Sw01 ∷ [])
  (re 1 1 (CS13 ∷ []) ∷
   rw⁻ 0 (q91 c4) ∷
   re 0 1 (Sb4-0-3-1 ∷ []) ∷ []) Eq.refl

private
  q92 : WsL → Eqn
  q92 c4 = eqn (Sw23 ∷ CS03⁻ ∷ []) (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 c4)

-- nat 2 SBOXd(4;0;3;1): 3 steps
lem-nat-2-SBOXd⟨4·0·3·1⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻4-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻4-0-2-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨4·0·3·1⟩ c4 = derive (Sw23 ∷ Sb⁻4-0-3-1 ∷ []) (Sb⁻4-0-2-1 ∷ Sw23 ∷ [])
  (re 1 1 (CS03⁻ ∷ []) ∷
   rw 0 (q92 c4) ∷
   re 0 1 (Sb⁻4-0-2-1 ∷ []) ∷ []) Eq.refl

-- nat 2 SBOX(2;0;4;1): 3 steps
lem-nat-2-SBOX⟨2·0·4·1⟩ : WsL → ⟪ (Sw23 ∷ Sb2-0-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-4-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·0·4·1⟩ c4 = derive (Sw23 ∷ Sb2-0-4-1 ∷ []) (Sb3-0-4-1 ∷ Sw23 ∷ [])
  (re 1 1 (CS04 ∷ []) ∷
   rw 0 (q72 c4) ∷
   re 0 1 (Sb3-0-4-1 ∷ []) ∷ []) Eq.refl

-- nat 2 SBOXd(2;0;4;1): 3 steps
lem-nat-2-SBOXd⟨2·0·4·1⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻2-0-4-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-4-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨2·0·4·1⟩ c4 = derive (Sw23 ∷ Sb⁻2-0-4-1 ∷ []) (Sb⁻3-0-4-1 ∷ Sw23 ∷ [])
  (re 1 1 (CS04⁻ ∷ []) ∷
   rw 0 (q73 c4) ∷
   re 0 1 (Sb⁻3-0-4-1 ∷ []) ∷ []) Eq.refl

private
  q93 : WsL → Eqn
  q93 c4 = eqn (Sw23 ∷ Bx2-0314 ∷ []) (Bx3-0214 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0314⟩ c4)
  q94 : WsL → Eqn
  q94 c4 = eqn (Sw23 ∷ Sb2-0-4-1 ∷ []) (Sb3-0-4-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·4·1⟩ c4)
  q95 : WsL → Eqn
  q95 c4 = eqn (Sw23 ∷ Sb⁻2-0-4-1 ∷ []) (Sb⁻3-0-4-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨2·0·4·1⟩ c4)

-- nat 2 SBOX(2;0;31;4): 7 steps
lem-nat-2-SBOX⟨2·0·31·4⟩ : WsL → ⟪ (Sw23 ∷ Sb2-0-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-21-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·0·31·4⟩ c4 = derive (Sw23 ∷ Sb2-0-31-4 ∷ []) (Sb3-0-21-4 ∷ Sw23 ∷ [])
  (re 1 1 (Bx2-0314 ∷ Toff413 ∷ Sb2-0-4-1 ∷ Toff413 ∷ Sb⁻2-0-4-1 ∷ []) ∷
   rw 0 (q93 c4) ∷
   rw 1 (q67 c4) ∷
   rw 2 (q94 c4) ∷
   rw 3 (q67 c4) ∷
   rw 4 (q95 c4) ∷
   re 0 5 (Sb3-0-21-4 ∷ []) ∷ []) Eq.refl

private
  q96 : WsL → Eqn
  q96 c4 = eqn (Sw34 ∷ CS03 ∷ []) (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 c4)

-- nat 3 SBOX(2;0;3;1): 3 steps
lem-nat-3-SBOX⟨2·0·3·1⟩ : WsL → ⟪ (Sw34 ∷ Sb2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-4-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·0·3·1⟩ c4 = derive (Sw34 ∷ Sb2-0-3-1 ∷ []) (Sb2-0-4-1 ∷ Sw34 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   rw 0 (q96 c4) ∷
   re 0 1 (Sb2-0-4-1 ∷ []) ∷ []) Eq.refl

private
  q97 : WsL → Eqn
  q97 c4 = eqn (Sw34 ∷ CS03⁻ ∷ []) (CS04⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd03 c4)

-- nat 3 SBOXd(2;0;3;1): 3 steps
lem-nat-3-SBOXd⟨2·0·3·1⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-4-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·0·3·1⟩ c4 = derive (Sw34 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻2-0-4-1 ∷ Sw34 ∷ [])
  (re 1 1 (CS03⁻ ∷ []) ∷
   rw 0 (q97 c4) ∷
   re 0 1 (Sb⁻2-0-4-1 ∷ []) ∷ []) Eq.refl

private
  q98 : WsL → Eqn
  q98 c4 = eqn (Sw34 ∷ Bx2-0413 ∷ []) (Bx2-0314 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·0413⟩ c4)
  q99 : WsL → Eqn
  q99 c4 = eqn (Sw34 ∷ Toff314 ∷ []) (Toff413 ∷ Sw34 ∷ []) (wl0142 c4)
  q100 : WsL → Eqn
  q100 c4 = eqn (Sw34 ∷ Sb2-0-3-1 ∷ []) (Sb2-0-4-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·3·1⟩ c4)
  q101 : WsL → Eqn
  q101 c4 = eqn (Sw34 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻2-0-4-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·0·3·1⟩ c4)

-- nat 3 SBOX(2;0;41;3): 7 steps
lem-nat-3-SBOX⟨2·0·41·3⟩ : WsL → ⟪ (Sw34 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-31-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·0·41·3⟩ c4 = derive (Sw34 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-31-4 ∷ Sw34 ∷ [])
  (re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 0 (q98 c4) ∷
   rw 1 (q99 c4) ∷
   rw 2 (q100 c4) ∷
   rw 3 (q99 c4) ∷
   rw 4 (q101 c4) ∷
   re 0 5 (Sb2-0-31-4 ∷ []) ∷ []) Eq.refl

private
  q102 : WsL → Eqn
  q102 c4 = eqn (Sw01 ∷ Toff403 ∷ []) (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4)
  q103 : WsL → Eqn
  q103 c4 = eqn (Sw01 ∷ Bx3-41 ∷ []) (Bx3-40 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·41⟩ c4)

-- nat 0 BOX(4;301): 8 steps
lem-nat-0-BOX⟨4·301⟩ : WsL → ⟪ (Sw01 ∷ Bx4-301 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-310 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·301⟩ c4 = derive (Sw01 ∷ Bx4-301 ∷ []) (Bx4-310 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) ∷
   rw 0 (q21 c4) ∷
   rw 1 (q102 c4) ∷
   rw 2 (q103 c4) ∷
   rw 3 (q102 c4) ∷
   rw 4 (q21 c4) ∷
   rw 5 (q103 c4) ∷
   re 0 6 (Bx4-310 ∷ []) ∷ []) Eq.refl

private
  q104 : WsL → Eqn
  q104 c4 = eqn (Sw01 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ))
  q105 : WsL → Eqn
  q105 c4 = eqn (Sw01 ∷ Toff324 ∷ []) (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))
  q106 : WsL → Eqn
  q106 c4 = eqn (Sw01 ∷ Bx4-301 ∷ []) (Bx4-310 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·301⟩ c4)

-- nat 0 BOX(3;4201): 8 steps
lem-nat-0-BOX⟨3·4201⟩ : WsL → ⟪ (Sw01 ∷ Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·4201⟩ c4 = derive (Sw01 ∷ Bx3-4201 ∷ []) (Bx3-4210 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff324 ∷ Bx4-301 ∷ Toff324 ∷ CCZ234 ∷ Bx4-301 ∷ []) ∷
   rw 0 (q104 c4) ∷
   rw 1 (q105 c4) ∷
   rw 2 (q106 c4) ∷
   rw 3 (q105 c4) ∷
   rw 4 (q104 c4) ∷
   rw 5 (q106 c4) ∷
   re 0 6 (Bx3-4210 ∷ []) ∷ []) Eq.refl

private
  q107 : WsL → Eqn
  q107 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 c4)
  q108 : WsL → Eqn
  q108 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 c4)
  q109 : WsL → Eqn
  q109 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 c4)
  q110 : WsL → Eqn
  q110 c4 = eqn (Sw01 ∷ Toff234 ∷ []) (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff))

-- resp TOFF124 at 3: 7 steps
lem-resp-TOFF124-at-3 : WsL → ⟪ (Toff124 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff234 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF124-at-3 c4 = derive (Toff124 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff234 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q107 c4) ∷
   rw⁻ 0 (q107 c4) ∷
   re 1 3 (Toff134 ∷ []) ∷
   rw⁻ 2 (q108 c4) ∷
   rw⁻ 1 (q60 c4) ∷
   rw⁻ 3 (q109 c4) ∷
   rw⁻ 2 (q110 c4) ∷ []) Eq.refl

private
  q111 : WsL → Eqn
  q111 c4 = eqn (Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap))
  q112 : WsL → Eqn
  q112 c4 = eqn (CK30 ∷ Sw12 ∷ []) (Sw12 ∷ CK30 ∷ []) (wl0159 c4)
  q113 : WsL → Eqn
  q113 c4 = eqn (Sw01 ∷ Sw34 ∷ []) (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑))
  q114 : WsL → Eqn
  q114 c4 = eqn (CK30 ∷ Sw01 ∷ []) (Sw01 ∷ CK31 ∷ []) (wl0117 c4)

-- resp CK40 at 2: 12 steps
lem-resp-CK40-at-2 : WsL → ⟪ (CK40 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CK41 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CK40-at-2 c4 = derive (CK40 ∷ []) (Sw12 ∷ Sw01 ∷ CK41 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q108 c4) ∷
   re 0 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q111 c4) ∷
   rw 1 (q112 c4) ∷
   rw⁻ 0 (q111 c4) ∷
   re 1 3 (CK40 ∷ []) ∷
   rw⁻ 2 (q109 c4) ∷
   re 1 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw⁻ 3 (q113 c4) ∷
   rw 2 (q114 c4) ∷
   rw⁻ 1 (q113 c4) ∷
   re 2 3 (CK41 ∷ []) ∷ []) Eq.refl

private
  q115 : WsL → Eqn
  q115 c4 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (c₁ (K) (Swap ↑))
  q116 : WsL → Eqn
  q116 c4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap))
  q117 : WsL → Eqn
  q117 c4 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (c₁ (iI) (Swap ↑))
  q118 : WsL → Eqn
  q118 c4 = eqn (K0 ∷ Sw34 ∷ []) (Sw34 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑))
  q119 : WsL → Eqn
  q119 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 c4)
  q120 : WsL → Eqn
  q120 c4 = eqn (CX01 ∷ Sw34 ∷ []) (Sw34 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap ↑))
  q121 : WsL → Eqn
  q121 c4 = eqn (ι ∷ Sw34 ∷ []) (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑))
  q122 : WsL → Eqn
  q122 c4 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (c₁ (K) (Swap))
  q123 : WsL → Eqn
  q123 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0008 c4)
  q124 : WsL → Eqn
  q124 c4 = eqn (CS24⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS14⁻ ∷ []) (wl0009 c4)
  q125 : WsL → Eqn
  q125 c4 = eqn (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) (wl0010 c4)
  q126 : WsL → Eqn
  q126 c4 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap))
  q127 : WsL → Eqn
  q127 c4 = eqn (Sw01 ∷ ι ∷ []) (ι ∷ Sw01 ∷ []) (wl0030 c4)
  q128 : WsL → Eqn
  q128 c4 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wl0031 c4)
  q129 : WsL → Eqn
  q129 c4 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wl0048 c4)
  q130 : WsL → Eqn
  q130 c4 = eqn (Sw01 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q131 : WsL → Eqn
  q131 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q132 : WsL → Eqn
  q132 c4 = eqn (K1 ∷ Sw34 ∷ []) (Sw34 ∷ K1 ∷ []) (c₂ (K ↑) (Swap ↑))
  q133 : WsL → Eqn
  q133 c4 = eqn (CX12 ∷ Sw34 ∷ []) (Sw34 ∷ CX12 ∷ []) (c₃ (CX₀₁ ↑) (Swap))
  q134 : WsL → Eqn
  q134 c4 = eqn (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wl0032 c4)

-- resp TOFF014 at 2: 74 steps
lem-resp-TOFF014-at-2 : WsL → ⟪ (Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff124 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF014-at-2 c4 = derive (Toff014 ∷ []) (Sw12 ∷ Sw01 ∷ Toff124 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q108 c4) ∷
   rw⁻ 0 (q108 c4) ∷
   re 1 3 (Toff024 ∷ []) ∷
   rw⁻ 2 (q109 c4) ∷
   re 1 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 (q115 c4) ∷
   rw⁻ 6 (q107 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q116 c4) ∷
   rw⁻ 8 (q107 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q116 c4) ∷
   rw⁻ 10 (q107 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 (q115 c4) ∷
   rw⁻ 10 (q117 c4) ∷
   rw 11 (q107 c4) ∷
   rw⁻ 2 (q118 c4) ∷
   rw⁻ 5 (q119 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q120 c4) ∷
   rw⁻ 7 (q119 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q120 c4) ∷
   rw⁻ 9 (q119 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q118 c4) ∷
   rw⁻ 9 (q121 c4) ∷
   rw 10 (q119 c4) ∷
   rw⁻ 1 (q122 c4) ∷
   rw⁻ 2 (q123 c4) ∷
   rw⁻ 5 (q108 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q124 c4) ∷
   rw⁻ 7 (q108 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q111 c4) ∷
   rw⁻ 7 (q125 c4) ∷
   rw 8 (q111 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q122 c4) ∷
   rw⁻ 8 (q126 c4) ∷
   rw 9 (q108 c4) ∷
   rw⁻ 8 (q127 c4) ∷
   rw 7 (q128 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q113 c4) ∷
   rw 7 (q91 c4) ∷
   rw⁻ 6 (q113 c4) ∷
   re 7 3 (CS14 ∷ []) ∷
   rw 5 (q129 c4) ∷
   rw⁻ 4 (q130 c4) ∷
   rw 3 (q129 c4) ∷
   rw⁻ 2 (q131 c4) ∷
   rw 1 (q128 c4) ∷
   rw⁻ 2 (q119 c4) ∷
   rw⁻ 3 (q132 c4) ∷
   re 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 4 (q119 c4) ∷
   rw⁻ 5 (q133 c4) ∷
   re 7 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q119 c4) ∷
   rw⁻ 7 (q133 c4) ∷
   re 9 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 8 (q119 c4) ∷
   rw⁻ 9 (q132 c4) ∷
   rw⁻ 10 (q121 c4) ∷
   rw 3 (q134 c4) ∷
   re 3 8 (Toff123 ∷ []) ∷
   re 2 3 (Toff124 ∷ []) ∷ []) Eq.refl

private
  q135 : WsL → Eqn
  q135 c4 = eqn (CK41 ∷ Sw12 ∷ []) (Sw12 ∷ CK42 ∷ []) (wl0160 c4)
  q136 : WsL → Eqn
  q136 c4 = eqn (Sw01 ∷ CK42 ∷ []) (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))

-- resp CK41 at 2: 4 steps
lem-resp-CK41-at-2 : WsL → ⟪ (CK41 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CK42 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CK41-at-2 c4 = derive (CK41 ∷ []) (Sw12 ∷ Sw01 ∷ CK42 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q108 c4) ∷
   rw 0 (q135 c4) ∷
   rw⁻ 2 (q109 c4) ∷
   rw⁻ 1 (q136 c4) ∷ []) Eq.refl

private
  q137 : WsL → Eqn
  q137 c4 = eqn (CZ01 ∷ Sw01 ∷ []) (Sw01 ∷ CZ01 ∷ []) (wl0130 c4)

-- nat 0 BOX(3;01): 3 steps
lem-nat-0-BOX⟨3·01⟩ : WsL → ⟪ (Sw01 ∷ Bx3-01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-10 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·01⟩ c4 = derive (Sw01 ∷ Bx3-01 ∷ []) (Bx3-10 ∷ Sw01 ∷ [])
  (re 1 1 (CZ01 ∷ []) ∷
   rw⁻ 0 (q137 c4) ∷
   re 0 1 (Bx3-10 ∷ []) ∷ []) Eq.refl

private
  q138 : WsL → Eqn
  q138 c4 = eqn (Sw01 ∷ Bx3-01 ∷ []) (Bx3-10 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·01⟩ c4)

-- nat 0 BOX(0;321): 8 steps
lem-nat-0-BOX⟨0·321⟩ : WsL → ⟪ (Sw01 ∷ Bx0-321 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-320 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·321⟩ c4 = derive (Sw01 ∷ Bx0-321 ∷ []) (Bx1-320 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) ∷
   rw⁻ 0 (q24 c4) ∷
   rw 1 (q25 c4) ∷
   rw 2 (q138 c4) ∷
   rw 3 (q25 c4) ∷
   rw⁻ 4 (q24 c4) ∷
   rw 5 (q138 c4) ∷
   re 0 6 (Bx1-320 ∷ []) ∷ []) Eq.refl

private
  q139 : WsL → Eqn
  q139 c4 = eqn (Sw01 ∷ Bx0-321 ∷ []) (Bx1-320 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·321⟩ c4)

-- nat 0 BOX(3;0421): 8 steps
lem-nat-0-BOX⟨3·0421⟩ : WsL → ⟪ (Sw01 ∷ Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·0421⟩ c4 = derive (Sw01 ∷ Bx3-0421 ∷ []) (Bx3-1420 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-321 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ []) ∷
   rw 0 (q21 c4) ∷
   rw 1 (q22 c4) ∷
   rw 2 (q139 c4) ∷
   rw 3 (q22 c4) ∷
   rw 4 (q21 c4) ∷
   rw 5 (q139 c4) ∷
   re 0 6 (Bx3-1420 ∷ []) ∷ []) Eq.refl

private
  q140 : WsL → Eqn
  q140 c4 = eqn (CS01 ∷ Sw01 ∷ []) (Sw01 ∷ CS01 ∷ []) (wl0132 c4)

-- nat 0 SBOX(3;0;1;2): 3 steps
lem-nat-0-SBOX⟨3·0·1·2⟩ : WsL → ⟪ (Sw01 ∷ Sb3-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-0-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·0·1·2⟩ c4 = derive (Sw01 ∷ Sb3-0-1-2 ∷ []) (Sb3-1-0-2 ∷ Sw01 ∷ [])
  (re 1 1 (CS01 ∷ []) ∷
   rw⁻ 0 (q140 c4) ∷
   re 0 1 (Sb3-1-0-2 ∷ []) ∷ []) Eq.refl

private
  q141 : WsL → Eqn
  q141 c4 = eqn (CS01⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS01⁻ ∷ []) (wl0133 c4)

-- nat 0 SBOXd(3;0;1;2): 3 steps
lem-nat-0-SBOXd⟨3·0·1·2⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻3-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-1-0-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨3·0·1·2⟩ c4 = derive (Sw01 ∷ Sb⁻3-0-1-2 ∷ []) (Sb⁻3-1-0-2 ∷ Sw01 ∷ [])
  (re 1 1 (CS01⁻ ∷ []) ∷
   rw⁻ 0 (q141 c4) ∷
   re 0 1 (Sb⁻3-1-0-2 ∷ []) ∷ []) Eq.refl

private
  q142 : WsL → Eqn
  q142 c4 = eqn (Sw01 ∷ Bx3-0421 ∷ []) (Bx3-1420 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0421⟩ c4)
  q143 : WsL → Eqn
  q143 c4 = eqn (Sw01 ∷ Toff124 ∷ []) (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4)
  q144 : WsL → Eqn
  q144 c4 = eqn (Sw01 ∷ Sb3-0-1-2 ∷ []) (Sb3-1-0-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·1·2⟩ c4)
  q145 : WsL → Eqn
  q145 c4 = eqn (Sw01 ∷ Sb⁻3-0-1-2 ∷ []) (Sb⁻3-1-0-2 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨3·0·1·2⟩ c4)

-- nat 0 SBOX(3;0;42;1): 7 steps
lem-nat-0-SBOX⟨3·0·42·1⟩ : WsL → ⟪ (Sw01 ∷ Sb3-0-42-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·0·42·1⟩ c4 = derive (Sw01 ∷ Sb3-0-42-1 ∷ []) (Sb3-1-42-0 ∷ Sw01 ∷ [])
  (re 1 1 (Bx3-0421 ∷ Toff124 ∷ Sb3-0-1-2 ∷ Toff124 ∷ Sb⁻3-0-1-2 ∷ []) ∷
   rw 0 (q142 c4) ∷
   rw 1 (q143 c4) ∷
   rw 2 (q144 c4) ∷
   rw 3 (q143 c4) ∷
   rw 4 (q145 c4) ∷
   re 0 5 (Sb3-1-42-0 ∷ []) ∷ []) Eq.refl

-- nat 0 BOX(3;10): 3 steps
lem-nat-0-BOX⟨3·10⟩ : WsL → ⟪ (Sw01 ∷ Bx3-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-01 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·10⟩ c4 = derive (Sw01 ∷ Bx3-10 ∷ []) (Bx3-01 ∷ Sw01 ∷ [])
  (re 1 1 (CZ01 ∷ []) ∷
   rw⁻ 0 (q137 c4) ∷
   re 0 1 (Bx3-01 ∷ []) ∷ []) Eq.refl

private
  q146 : WsL → Eqn
  q146 c4 = eqn (Sw01 ∷ Bx3-10 ∷ []) (Bx3-01 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·10⟩ c4)

-- nat 0 BOX(1;320): 8 steps
lem-nat-0-BOX⟨1·320⟩ : WsL → ⟪ (Sw01 ∷ Bx1-320 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-321 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·320⟩ c4 = derive (Sw01 ∷ Bx1-320 ∷ []) (Bx0-321 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) ∷
   rw⁻ 0 (q17 c4) ∷
   rw 1 (q18 c4) ∷
   rw 2 (q146 c4) ∷
   rw 3 (q18 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 5 (q146 c4) ∷
   re 0 6 (Bx0-321 ∷ []) ∷ []) Eq.refl

private
  q147 : WsL → Eqn
  q147 c4 = eqn (Sw01 ∷ Bx1-320 ∷ []) (Bx0-321 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·320⟩ c4)

-- nat 0 BOX(3;1420): 8 steps
lem-nat-0-BOX⟨3·1420⟩ : WsL → ⟪ (Sw01 ∷ Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·1420⟩ c4 = derive (Sw01 ∷ Bx3-1420 ∷ []) (Bx3-0421 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ []) ∷
   rw 0 (q14 c4) ∷
   rw 1 (q15 c4) ∷
   rw 2 (q147 c4) ∷
   rw 3 (q15 c4) ∷
   rw 4 (q14 c4) ∷
   rw 5 (q147 c4) ∷
   re 0 6 (Bx3-0421 ∷ []) ∷ []) Eq.refl

private
  q148 : WsL → Eqn
  q148 c4 = eqn (CZ02 ∷ Sw01 ∷ []) (Sw01 ∷ CZ12 ∷ []) (wl0105 c4)

-- nat 0 BOX(3;12): 3 steps
lem-nat-0-BOX⟨3·12⟩ : WsL → ⟪ (Sw01 ∷ Bx3-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-02 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·12⟩ c4 = derive (Sw01 ∷ Bx3-12 ∷ []) (Bx3-02 ∷ Sw01 ∷ [])
  (re 1 1 (CZ12 ∷ []) ∷
   rw⁻ 0 (q148 c4) ∷
   re 0 1 (Bx3-02 ∷ []) ∷ []) Eq.refl

private
  q149 : WsL → Eqn
  q149 c4 = eqn (CCZ013 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ013 ∷ []) (wl0100 c4)
  q150 : WsL → Eqn
  q150 c4 = eqn (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) (wl0102 c4)
  q151 : WsL → Eqn
  q151 c4 = eqn (Sw01 ∷ Bx3-12 ∷ []) (Bx3-02 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·12⟩ c4)

-- nat 0 BOX(1;302): 8 steps
lem-nat-0-BOX⟨1·302⟩ : WsL → ⟪ (Sw01 ∷ Bx1-302 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-312 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·302⟩ c4 = derive (Sw01 ∷ Bx1-302 ∷ []) (Bx0-312 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) ∷
   rw⁻ 0 (q149 c4) ∷
   rw 1 (q150 c4) ∷
   rw 2 (q151 c4) ∷
   rw 3 (q150 c4) ∷
   rw⁻ 4 (q149 c4) ∷
   rw 5 (q151 c4) ∷
   re 0 6 (Bx0-312 ∷ []) ∷ []) Eq.refl

private
  q152 : WsL → Eqn
  q152 c4 = eqn (Sw01 ∷ Bx1-302 ∷ []) (Bx0-312 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·302⟩ c4)

-- nat 0 BOX(3;1402): 8 steps
lem-nat-0-BOX⟨3·1402⟩ : WsL → ⟪ (Sw01 ∷ Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·1402⟩ c4 = derive (Sw01 ∷ Bx3-1402 ∷ []) (Bx3-0412 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-302 ∷ Toff314 ∷ CCZ134 ∷ Bx1-302 ∷ []) ∷
   rw 0 (q14 c4) ∷
   rw 1 (q15 c4) ∷
   rw 2 (q152 c4) ∷
   rw 3 (q15 c4) ∷
   rw 4 (q14 c4) ∷
   rw 5 (q152 c4) ∷
   re 0 6 (Bx3-0412 ∷ []) ∷ []) Eq.refl

private
  q153 : WsL → Eqn
  q153 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl0011 c4)
  q154 : WsL → Eqn
  q154 c4 = eqn (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) (wl0012 c4)
  q155 : WsL → Eqn
  q155 c4 = eqn (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4)
  q156 : WsL → Eqn
  q156 c4 = eqn (CS01 ∷ Sw34 ∷ []) (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑))
  q157 : WsL → Eqn
  q157 c4 = eqn (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) (wl0014 c4)
  q158 : WsL → Eqn
  q158 c4 = eqn (Sw12 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS))
  q159 : WsL → Eqn
  q159 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q160 : WsL → Eqn
  q160 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl0015 c4)
  q161 : WsL → Eqn
  q161 c4 = eqn (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) (wl0016 c4)
  q162 : WsL → Eqn
  q162 c4 = eqn (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ []) (wl0018 c4)
  q163 : WsL → Eqn
  q163 c4 = eqn (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) (wl0020 c4)
  q164 : WsL → Eqn
  q164 c4 = eqn (Sw01 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑))
  q165 : WsL → Eqn
  q165 c4 = eqn (Sw01 ∷ CS34 ∷ []) (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))
  q166 : WsL → Eqn
  q166 c4 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (c₂ (K ↑) (Swap))
  q167 : WsL → Eqn
  q167 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl0021 c4)

-- resp TOFF024 at 3: 239 steps
lem-resp-TOFF024-at-3 : WsL → ⟪ (Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff134 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF024-at-3 c4 = derive (Toff024 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff134 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q107 c4) ∷
   rw⁻ 0 (q107 c4) ∷
   re 1 3 (Toff034 ∷ []) ∷
   rw⁻ 2 (q108 c4) ∷
   re 1 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) ∷
   re 3 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   re 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 4 (q115 c4) ∷
   rw⁻ 7 (q107 c4) ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 (q116 c4) ∷
   rw⁻ 9 (q107 c4) ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 (q116 c4) ∷
   rw⁻ 11 (q107 c4) ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 (q115 c4) ∷
   rw⁻ 11 (q117 c4) ∷
   rw 12 (q107 c4) ∷
   rw⁻ 3 (q118 c4) ∷
   rw⁻ 6 (q119 c4) ∷
   re 4 3 (CS14 ∷ []) ∷
   rw⁻ 5 (q120 c4) ∷
   rw⁻ 8 (q119 c4) ∷
   re 6 3 (CS14⁻ ∷ []) ∷
   rw⁻ 7 (q120 c4) ∷
   rw⁻ 10 (q119 c4) ∷
   re 8 3 (CS04 ∷ []) ∷
   rw⁻ 9 (q118 c4) ∷
   rw⁻ 10 (q121 c4) ∷
   rw 11 (q119 c4) ∷
   rw⁻ 2 (q122 c4) ∷
   rw⁻ 3 (q123 c4) ∷
   rw⁻ 6 (q108 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw⁻ 5 (q124 c4) ∷
   rw⁻ 8 (q108 c4) ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q111 c4) ∷
   rw⁻ 8 (q125 c4) ∷
   rw 9 (q111 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q122 c4) ∷
   rw⁻ 9 (q126 c4) ∷
   rw 10 (q108 c4) ∷
   rw⁻ 1 (q115 c4) ∷
   rw⁻ 2 (q153 c4) ∷
   rw⁻ 5 (q107 c4) ∷
   re 3 3 (CX03 ∷ []) ∷
   rw⁻ 4 (q154 c4) ∷
   rw⁻ 7 (q107 c4) ∷
   re 5 3 (CX03 ∷ []) ∷
   re 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 6 (q155 c4) ∷
   rw⁻ 8 (q111 c4) ∷
   rw⁻ 9 (q156 c4) ∷
   rw⁻ 10 (q111 c4) ∷
   rw⁻ 11 (q155 c4) ∷
   re 6 7 (CS04 ∷ []) ∷
   rw⁻ 7 (q115 c4) ∷
   rw⁻ 8 (q117 c4) ∷
   rw 9 (q107 c4) ∷
   rw 8 (q126 c4) ∷
   rw 7 (q122 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q111 c4) ∷
   rw 7 (q125 c4) ∷
   rw⁻ 6 (q111 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw 5 (q157 c4) ∷
   rw⁻ 4 (q158 c4) ∷
   rw 3 (q157 c4) ∷
   rw⁻ 2 (q159 c4) ∷
   rw 1 (q122 c4) ∷
   rw⁻ 2 (q107 c4) ∷
   rw⁻ 3 (q115 c4) ∷
   rw⁻ 4 (q160 c4) ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 5 (q107 c4) ∷
   rw⁻ 6 (q161 c4) ∷
   re 8 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 7 (q107 c4) ∷
   re 9 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 8 (q155 c4) ∷
   rw⁻ 10 (q111 c4) ∷
   rw⁻ 11 (q156 c4) ∷
   rw⁻ 12 (q111 c4) ∷
   rw⁻ 13 (q155 c4) ∷
   re 8 7 (CS04 ∷ []) ∷
   rw⁻ 9 (q115 c4) ∷
   rw⁻ 10 (q117 c4) ∷
   rw⁻ 3 (q108 c4) ∷
   rw⁻ 4 (q122 c4) ∷
   rw⁻ 5 (q84 c4) ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 (q108 c4) ∷
   rw⁻ 7 (q162 c4) ∷
   re 9 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 8 (q108 c4) ∷
   re 10 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 9 (q111 c4) ∷
   rw⁻ 10 (q125 c4) ∷
   rw 11 (q111 c4) ∷
   re 9 3 (CS04 ∷ []) ∷
   rw⁻ 10 (q122 c4) ∷
   rw⁻ 11 (q126 c4) ∷
   rw⁻ 4 (q119 c4) ∷
   rw⁻ 5 (q118 c4) ∷
   re 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 6 (q119 c4) ∷
   rw⁻ 7 (q120 c4) ∷
   re 9 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 8 (q119 c4) ∷
   rw⁻ 9 (q120 c4) ∷
   re 11 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 10 (q119 c4) ∷
   rw⁻ 11 (q118 c4) ∷
   rw⁻ 12 (q121 c4) ∷
   rw⁻ 5 (q107 c4) ∷
   rw⁻ 6 (q115 c4) ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 (q107 c4) ∷
   rw⁻ 8 (q116 c4) ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 (q107 c4) ∷
   rw⁻ 10 (q116 c4) ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 (q107 c4) ∷
   rw⁻ 12 (q115 c4) ∷
   rw⁻ 13 (q117 c4) ∷
   re 6 8 (Toff012 ∷ []) ∷
   re 5 3 (Toff013 ∷ []) ∷
   re 4 3 (Toff014 ∷ []) ∷
   re 3 3 (Toff024 ∷ []) ∷
   re 2 3 (Toff034 ∷ []) ∷
   rw⁻ 3 (q109 c4) ∷
   re 2 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) ∷
   re 3 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) ∷
   re 4 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   re 5 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 5 (q115 c4) ∷
   rw⁻ 8 (q107 c4) ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 (q116 c4) ∷
   rw⁻ 10 (q107 c4) ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 (q116 c4) ∷
   rw⁻ 12 (q107 c4) ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 (q115 c4) ∷
   rw⁻ 12 (q117 c4) ∷
   rw 13 (q107 c4) ∷
   rw⁻ 4 (q118 c4) ∷
   rw⁻ 7 (q119 c4) ∷
   re 5 3 (CS14 ∷ []) ∷
   rw⁻ 6 (q120 c4) ∷
   rw⁻ 9 (q119 c4) ∷
   re 7 3 (CS14⁻ ∷ []) ∷
   rw⁻ 8 (q120 c4) ∷
   rw⁻ 11 (q119 c4) ∷
   re 9 3 (CS04 ∷ []) ∷
   rw⁻ 10 (q118 c4) ∷
   rw⁻ 11 (q121 c4) ∷
   rw 12 (q119 c4) ∷
   rw⁻ 3 (q122 c4) ∷
   rw⁻ 4 (q123 c4) ∷
   rw⁻ 7 (q108 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   rw⁻ 6 (q124 c4) ∷
   rw⁻ 9 (q108 c4) ∷
   re 7 3 (CX02 ∷ []) ∷
   re 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 8 (q111 c4) ∷
   rw⁻ 9 (q125 c4) ∷
   rw 10 (q111 c4) ∷
   re 8 3 (CS04 ∷ []) ∷
   rw⁻ 9 (q122 c4) ∷
   rw⁻ 10 (q126 c4) ∷
   rw 11 (q108 c4) ∷
   rw⁻ 2 (q115 c4) ∷
   rw⁻ 3 (q153 c4) ∷
   rw⁻ 6 (q107 c4) ∷
   re 4 3 (CX03 ∷ []) ∷
   rw⁻ 5 (q154 c4) ∷
   rw⁻ 8 (q107 c4) ∷
   re 6 3 (CX03 ∷ []) ∷
   re 8 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 7 (q155 c4) ∷
   rw⁻ 9 (q111 c4) ∷
   rw⁻ 10 (q156 c4) ∷
   rw⁻ 11 (q111 c4) ∷
   rw⁻ 12 (q155 c4) ∷
   re 7 7 (CS04 ∷ []) ∷
   rw⁻ 8 (q115 c4) ∷
   rw⁻ 9 (q117 c4) ∷
   rw 10 (q107 c4) ∷
   rw⁻ 9 (q127 c4) ∷
   rw 8 (q128 c4) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 9 (q113 c4) ∷
   rw 8 (q91 c4) ∷
   rw⁻ 7 (q113 c4) ∷
   re 8 3 (CS14 ∷ []) ∷
   rw 6 (q163 c4) ∷
   rw⁻ 5 (q164 c4) ∷
   rw 4 (q163 c4) ∷
   rw⁻ 3 (q165 c4) ∷
   rw 2 (q128 c4) ∷
   rw⁻ 3 (q107 c4) ∷
   rw⁻ 4 (q166 c4) ∷
   rw⁻ 5 (q160 c4) ∷
   re 7 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 6 (q107 c4) ∷
   rw⁻ 7 (q161 c4) ∷
   re 9 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 8 (q107 c4) ∷
   rw⁻ 9 (q167 c4) ∷
   rw⁻ 10 (q166 c4) ∷
   rw⁻ 11 (q117 c4) ∷
   rw⁻ 4 (q119 c4) ∷
   rw⁻ 5 (q132 c4) ∷
   re 7 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 6 (q119 c4) ∷
   rw⁻ 7 (q133 c4) ∷
   re 9 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 8 (q119 c4) ∷
   rw⁻ 9 (q133 c4) ∷
   re 11 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 10 (q119 c4) ∷
   rw⁻ 11 (q132 c4) ∷
   rw⁻ 12 (q121 c4) ∷
   rw 5 (q134 c4) ∷
   re 5 8 (Toff123 ∷ []) ∷
   re 4 3 (Toff124 ∷ []) ∷
   re 3 3 (Toff134 ∷ []) ∷ []) Eq.refl

private
  q168 : WsL → Eqn
  q168 c4 = eqn (CZ24 ∷ Sw23 ∷ []) (Sw23 ∷ CZ34 ∷ []) (wl0027 c4)
  q169 : WsL → Eqn
  q169 c4 = eqn (Sw12 ∷ CZ34 ∷ []) (CZ34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ))
  q170 : WsL → Eqn
  q170 c4 = eqn (Sw01 ∷ CZ34 ∷ []) (CZ34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑))

-- resp CZ24 at 3: 6 steps
lem-resp-CZ24-at-3 : WsL → ⟪ (CZ24 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CZ34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CZ24-at-3 c4 = derive (CZ24 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CZ34 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q107 c4) ∷
   rw 0 (q168 c4) ∷
   rw⁻ 2 (q108 c4) ∷
   rw⁻ 1 (q169 c4) ∷
   rw⁻ 3 (q109 c4) ∷
   rw⁻ 2 (q170 c4) ∷ []) Eq.refl

private
  q171 : WsL → Eqn
  q171 c4 = eqn (Sw23 ∷ CZ13 ∷ []) (CZ12 ∷ Sw23 ∷ []) (lem-nat-2-CZ13 c4)

-- nat 2 BOX(2;13): 3 steps
lem-nat-2-BOX⟨2·13⟩ : WsL → ⟪ (Sw23 ∷ Bx2-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-12 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·13⟩ c4 = derive (Sw23 ∷ Bx2-13 ∷ []) (Bx3-12 ∷ Sw23 ∷ [])
  (re 1 1 (CZ13 ∷ []) ∷
   rw 0 (q171 c4) ∷
   re 0 1 (Bx3-12 ∷ []) ∷ []) Eq.refl

private
  q172 : WsL → Eqn
  q172 c4 = eqn (Sw23 ∷ Bx2-13 ∷ []) (Bx3-12 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·13⟩ c4)

-- nat 2 BOX(1;243): 8 steps
lem-nat-2-BOX⟨1·243⟩ : WsL → ⟪ (Sw23 ∷ Bx1-243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-342 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·243⟩ c4 = derive (Sw23 ∷ Bx1-243 ∷ []) (Bx1-342 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-13 ∷ Toff124 ∷ CCZ124 ∷ Bx2-13 ∷ []) ∷
   rw 0 (q63 c4) ∷
   rw 1 (q64 c4) ∷
   rw 2 (q172 c4) ∷
   rw 3 (q64 c4) ∷
   rw 4 (q63 c4) ∷
   rw 5 (q172 c4) ∷
   re 0 6 (Bx1-342 ∷ []) ∷ []) Eq.refl

private
  q173 : WsL → Eqn
  q173 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4)
  q174 : WsL → Eqn
  q174 c4 = eqn (Sw23 ∷ Toff201 ∷ []) (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4)
  q175 : WsL → Eqn
  q175 c4 = eqn (Sw23 ∷ Bx1-243 ∷ []) (Bx1-342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·243⟩ c4)

-- nat 2 BOX(2;1043): 8 steps
lem-nat-2-BOX⟨2·1043⟩ : WsL → ⟪ (Sw23 ∷ Bx2-1043 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1042 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·1043⟩ c4 = derive (Sw23 ∷ Bx2-1043 ∷ []) (Bx3-1042 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-243 ∷ Toff201 ∷ CCZ012 ∷ Bx1-243 ∷ []) ∷
   rw 0 (q173 c4) ∷
   rw 1 (q174 c4) ∷
   rw 2 (q175 c4) ∷
   rw 3 (q174 c4) ∷
   rw 4 (q173 c4) ∷
   rw 5 (q175 c4) ∷
   re 0 6 (Bx3-1042 ∷ []) ∷ []) Eq.refl

private
  q176 : WsL → Eqn
  q176 c4 = eqn (Sw12 ∷ Bx3-12 ∷ []) (Bx3-21 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·12⟩ c4)

-- nat 1 BOX(1;342): 8 steps
lem-nat-1-BOX⟨1·342⟩ : WsL → ⟪ (Sw12 ∷ Bx1-342 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-341 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·342⟩ c4 = derive (Sw12 ∷ Bx1-342 ∷ []) (Bx2-341 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff134 ∷ Bx3-12 ∷ Toff134 ∷ CCZ134 ∷ Bx3-12 ∷ []) ∷
   rw⁻ 0 (q52 c4) ∷
   rw 1 (q53 c4) ∷
   rw 2 (q176 c4) ∷
   rw 3 (q53 c4) ∷
   rw⁻ 4 (q52 c4) ∷
   rw 5 (q176 c4) ∷
   re 0 6 (Bx2-341 ∷ []) ∷ []) Eq.refl

private
  q177 : WsL → Eqn
  q177 c4 = eqn (Sw12 ∷ Toff301 ∷ []) (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4)
  q178 : WsL → Eqn
  q178 c4 = eqn (Sw12 ∷ Bx1-342 ∷ []) (Bx2-341 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·342⟩ c4)

-- nat 1 BOX(3;1042): 8 steps
lem-nat-1-BOX⟨3·1042⟩ : WsL → ⟪ (Sw12 ∷ Bx3-1042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·1042⟩ c4 = derive (Sw12 ∷ Bx3-1042 ∷ []) (Bx3-2041 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-342 ∷ Toff301 ∷ CCZ013 ∷ Bx1-342 ∷ []) ∷
   rw 0 (q4 c4) ∷
   rw 1 (q177 c4) ∷
   rw 2 (q178 c4) ∷
   rw 3 (q177 c4) ∷
   rw 4 (q4 c4) ∷
   rw 5 (q178 c4) ∷
   re 0 6 (Bx3-2041 ∷ []) ∷ []) Eq.refl

private
  q179 : WsL → Eqn
  q179 c4 = eqn (Sw01 ∷ Toff134 ∷ []) (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4)

-- nat 0 BOX(1;342): 8 steps
lem-nat-0-BOX⟨1·342⟩ : WsL → ⟪ (Sw01 ∷ Bx1-342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-342 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·342⟩ c4 = derive (Sw01 ∷ Bx1-342 ∷ []) (Bx0-342 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff134 ∷ Bx3-12 ∷ Toff134 ∷ CCZ134 ∷ Bx3-12 ∷ []) ∷
   rw 0 (q14 c4) ∷
   rw 1 (q179 c4) ∷
   rw 2 (q151 c4) ∷
   rw 3 (q179 c4) ∷
   rw 4 (q14 c4) ∷
   rw 5 (q151 c4) ∷
   re 0 6 (Bx0-342 ∷ []) ∷ []) Eq.refl

private
  q180 : WsL → Eqn
  q180 c4 = eqn (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) (wl0115 c4)
  q181 : WsL → Eqn
  q181 c4 = eqn (Sw01 ∷ Bx1-342 ∷ []) (Bx0-342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·342⟩ c4)

-- nat 0 BOX(3;1042): 8 steps
lem-nat-0-BOX⟨3·1042⟩ : WsL → ⟪ (Sw01 ∷ Bx3-1042 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·1042⟩ c4 = derive (Sw01 ∷ Bx3-1042 ∷ []) (Bx3-0142 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-342 ∷ Toff301 ∷ CCZ013 ∷ Bx1-342 ∷ []) ∷
   rw⁻ 0 (q149 c4) ∷
   rw 1 (q180 c4) ∷
   rw 2 (q181 c4) ∷
   rw 3 (q180 c4) ∷
   rw⁻ 4 (q149 c4) ∷
   rw 5 (q181 c4) ∷
   re 0 6 (Bx3-0142 ∷ []) ∷ []) Eq.refl

private
  q182 : WsL → Eqn
  q182 c4 = eqn (CZ12 ∷ Sw12 ∷ []) (Sw12 ∷ CZ12 ∷ []) (wl0109 c4)

-- nat 1 BOX(3;21): 3 steps
lem-nat-1-BOX⟨3·21⟩ : WsL → ⟪ (Sw12 ∷ Bx3-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-12 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·21⟩ c4 = derive (Sw12 ∷ Bx3-21 ∷ []) (Bx3-12 ∷ Sw12 ∷ [])
  (re 1 1 (CZ12 ∷ []) ∷
   rw⁻ 0 (q182 c4) ∷
   re 0 1 (Bx3-12 ∷ []) ∷ []) Eq.refl

private
  q183 : WsL → Eqn
  q183 c4 = eqn (Sw12 ∷ Bx3-21 ∷ []) (Bx3-12 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·21⟩ c4)

-- nat 1 BOX(2;341): 8 steps
lem-nat-1-BOX⟨2·341⟩ : WsL → ⟪ (Sw12 ∷ Bx2-341 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-342 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·341⟩ c4 = derive (Sw12 ∷ Bx2-341 ∷ []) (Bx1-342 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ []) ∷
   rw⁻ 0 (q59 c4) ∷
   rw 1 (q60 c4) ∷
   rw 2 (q183 c4) ∷
   rw 3 (q60 c4) ∷
   rw⁻ 4 (q59 c4) ∷
   rw 5 (q183 c4) ∷
   re 0 6 (Bx1-342 ∷ []) ∷ []) Eq.refl

private
  q184 : WsL → Eqn
  q184 c4 = eqn (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4)
  q185 : WsL → Eqn
  q185 c4 = eqn (Sw12 ∷ Toff302 ∷ []) (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4)
  q186 : WsL → Eqn
  q186 c4 = eqn (Sw12 ∷ Bx2-341 ∷ []) (Bx1-342 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·341⟩ c4)

-- nat 1 BOX(3;2041): 8 steps
lem-nat-1-BOX⟨3·2041⟩ : WsL → ⟪ (Sw12 ∷ Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1042 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·2041⟩ c4 = derive (Sw12 ∷ Bx3-2041 ∷ []) (Bx3-1042 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-341 ∷ Toff302 ∷ CCZ023 ∷ Bx2-341 ∷ []) ∷
   rw 0 (q184 c4) ∷
   rw 1 (q185 c4) ∷
   rw 2 (q186 c4) ∷
   rw 3 (q185 c4) ∷
   rw 4 (q184 c4) ∷
   rw 5 (q186 c4) ∷
   re 0 6 (Bx3-1042 ∷ []) ∷ []) Eq.refl

private
  q187 : WsL → Eqn
  q187 c4 = eqn (Sw12 ∷ Toff203 ∷ []) (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4)

-- nat 1 BOX(2;301): 8 steps
lem-nat-1-BOX⟨2·301⟩ : WsL → ⟪ (Sw12 ∷ Bx2-301 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-302 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·301⟩ c4 = derive (Sw12 ∷ Bx2-301 ∷ []) (Bx1-302 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) ∷
   rw 0 (q184 c4) ∷
   rw 1 (q187 c4) ∷
   rw 2 (q183 c4) ∷
   rw 3 (q187 c4) ∷
   rw 4 (q184 c4) ∷
   rw 5 (q183 c4) ∷
   re 0 6 (Bx1-302 ∷ []) ∷ []) Eq.refl

private
  q188 : WsL → Eqn
  q188 c4 = eqn (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) (wl0063 c4)
  q189 : WsL → Eqn
  q189 c4 = eqn (Sw12 ∷ Bx2-301 ∷ []) (Bx1-302 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·301⟩ c4)

-- nat 1 BOX(3;2401): 8 steps
lem-nat-1-BOX⟨3·2401⟩ : WsL → ⟪ (Sw12 ∷ Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·2401⟩ c4 = derive (Sw12 ∷ Bx3-2401 ∷ []) (Bx3-1402 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-301 ∷ Toff324 ∷ CCZ234 ∷ Bx2-301 ∷ []) ∷
   rw⁻ 0 (q59 c4) ∷
   rw 1 (q188 c4) ∷
   rw 2 (q189 c4) ∷
   rw 3 (q188 c4) ∷
   rw⁻ 4 (q59 c4) ∷
   rw 5 (q189 c4) ∷
   re 0 6 (Bx3-1402 ∷ []) ∷ []) Eq.refl

private
  q190 : WsL → Eqn
  q190 c4 = eqn (Sw01 ∷ Toff034 ∷ []) (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4)
  q191 : WsL → Eqn
  q191 c4 = eqn (Sw01 ∷ Bx3-02 ∷ []) (Bx3-12 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·02⟩ c4)

-- nat 0 BOX(0;342): 8 steps
lem-nat-0-BOX⟨0·342⟩ : WsL → ⟪ (Sw01 ∷ Bx0-342 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-342 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·342⟩ c4 = derive (Sw01 ∷ Bx0-342 ∷ []) (Bx1-342 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) ∷
   rw 0 (q21 c4) ∷
   rw 1 (q190 c4) ∷
   rw 2 (q191 c4) ∷
   rw 3 (q190 c4) ∷
   rw 4 (q21 c4) ∷
   rw 5 (q191 c4) ∷
   re 0 6 (Bx1-342 ∷ []) ∷ []) Eq.refl

private
  q192 : WsL → Eqn
  q192 c4 = eqn (Sw01 ∷ Bx0-342 ∷ []) (Bx1-342 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·342⟩ c4)

-- nat 0 BOX(3;0142): 8 steps
lem-nat-0-BOX⟨3·0142⟩ : WsL → ⟪ (Sw01 ∷ Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1042 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·0142⟩ c4 = derive (Sw01 ∷ Bx3-0142 ∷ []) (Bx3-1042 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-342 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ []) ∷
   rw⁻ 0 (q149 c4) ∷
   rw 1 (q180 c4) ∷
   rw 2 (q192 c4) ∷
   rw 3 (q180 c4) ∷
   rw⁻ 4 (q149 c4) ∷
   rw 5 (q192 c4) ∷
   re 0 6 (Bx3-1042 ∷ []) ∷ []) Eq.refl

private
  q193 : WsL → Eqn
  q193 c4 = eqn (Sw01 ∷ Bx3-04 ∷ []) (Bx3-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·04⟩ c4)

-- nat 0 BOX(0;324): 8 steps
lem-nat-0-BOX⟨0·324⟩ : WsL → ⟪ (Sw01 ∷ Bx0-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-324 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·324⟩ c4 = derive (Sw01 ∷ Bx0-324 ∷ []) (Bx1-324 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) ∷
   rw⁻ 0 (q24 c4) ∷
   rw 1 (q25 c4) ∷
   rw 2 (q193 c4) ∷
   rw 3 (q25 c4) ∷
   rw⁻ 4 (q24 c4) ∷
   rw 5 (q193 c4) ∷
   re 0 6 (Bx1-324 ∷ []) ∷ []) Eq.refl

private
  q194 : WsL → Eqn
  q194 c4 = eqn (Sw01 ∷ Bx0-324 ∷ []) (Bx1-324 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·324⟩ c4)

-- nat 0 BOX(3;0124): 8 steps
lem-nat-0-BOX⟨3·0124⟩ : WsL → ⟪ (Sw01 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·0124⟩ c4 = derive (Sw01 ∷ Bx3-0124 ∷ []) (Bx3-1024 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) ∷
   rw⁻ 0 (q149 c4) ∷
   rw 1 (q180 c4) ∷
   rw 2 (q194 c4) ∷
   rw 3 (q180 c4) ∷
   rw⁻ 4 (q149 c4) ∷
   rw 5 (q194 c4) ∷
   re 0 6 (Bx3-1024 ∷ []) ∷ []) Eq.refl

private
  q195 : WsL → Eqn
  q195 c4 = eqn (CZ24 ∷ Sw12 ∷ []) (Sw12 ∷ CZ14 ∷ []) (wl0089 c4)

-- nat 1 BOX(3;14): 3 steps
lem-nat-1-BOX⟨3·14⟩ : WsL → ⟪ (Sw12 ∷ Bx3-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-24 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·14⟩ c4 = derive (Sw12 ∷ Bx3-14 ∷ []) (Bx3-24 ∷ Sw12 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   rw⁻ 0 (q195 c4) ∷
   re 0 1 (Bx3-24 ∷ []) ∷ []) Eq.refl

private
  q196 : WsL → Eqn
  q196 c4 = eqn (CCZ123 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ123 ∷ []) (wl0111 c4)
  q197 : WsL → Eqn
  q197 c4 = eqn (Sw12 ∷ Toff123 ∷ []) (Toff213 ∷ Sw12 ∷ []) (wl0146 c4)
  q198 : WsL → Eqn
  q198 c4 = eqn (Sw12 ∷ Bx3-14 ∷ []) (Bx3-24 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·14⟩ c4)

-- nat 1 BOX(1;324): 8 steps
lem-nat-1-BOX⟨1·324⟩ : WsL → ⟪ (Sw12 ∷ Bx1-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-314 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·324⟩ c4 = derive (Sw12 ∷ Bx1-324 ∷ []) (Bx2-314 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-14 ∷ Toff123 ∷ CCZ123 ∷ Bx3-14 ∷ []) ∷
   rw⁻ 0 (q196 c4) ∷
   rw 1 (q197 c4) ∷
   rw 2 (q198 c4) ∷
   rw 3 (q197 c4) ∷
   rw⁻ 4 (q196 c4) ∷
   rw 5 (q198 c4) ∷
   re 0 6 (Bx2-314 ∷ []) ∷ []) Eq.refl

private
  q199 : WsL → Eqn
  q199 c4 = eqn (Sw12 ∷ Bx1-324 ∷ []) (Bx2-314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·324⟩ c4)

-- nat 1 BOX(3;1024): 8 steps
lem-nat-1-BOX⟨3·1024⟩ : WsL → ⟪ (Sw12 ∷ Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·1024⟩ c4 = derive (Sw12 ∷ Bx3-1024 ∷ []) (Bx3-2014 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-324 ∷ Toff301 ∷ CCZ013 ∷ Bx1-324 ∷ []) ∷
   rw 0 (q4 c4) ∷
   rw 1 (q177 c4) ∷
   rw 2 (q199 c4) ∷
   rw 3 (q177 c4) ∷
   rw 4 (q4 c4) ∷
   rw 5 (q199 c4) ∷
   re 0 6 (Bx3-2014 ∷ []) ∷ []) Eq.refl

private
  q200 : WsL → Eqn
  q200 c4 = eqn (CZ14 ∷ Sw12 ∷ []) (Sw12 ∷ CZ24 ∷ []) (wl0005 c4)

-- nat 1 BOX(3;24): 3 steps
lem-nat-1-BOX⟨3·24⟩ : WsL → ⟪ (Sw12 ∷ Bx3-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-14 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·24⟩ c4 = derive (Sw12 ∷ Bx3-24 ∷ []) (Bx3-14 ∷ Sw12 ∷ [])
  (re 1 1 (CZ24 ∷ []) ∷
   rw⁻ 0 (q200 c4) ∷
   re 0 1 (Bx3-14 ∷ []) ∷ []) Eq.refl

private
  q201 : WsL → Eqn
  q201 c4 = eqn (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) (wl0112 c4)
  q202 : WsL → Eqn
  q202 c4 = eqn (Sw12 ∷ Bx3-24 ∷ []) (Bx3-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·24⟩ c4)

-- nat 1 BOX(2;314): 8 steps
lem-nat-1-BOX⟨2·314⟩ : WsL → ⟪ (Sw12 ∷ Bx2-314 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-324 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·314⟩ c4 = derive (Sw12 ∷ Bx2-314 ∷ []) (Bx1-324 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) ∷
   rw⁻ 0 (q196 c4) ∷
   rw 1 (q201 c4) ∷
   rw 2 (q202 c4) ∷
   rw 3 (q201 c4) ∷
   rw⁻ 4 (q196 c4) ∷
   rw 5 (q202 c4) ∷
   re 0 6 (Bx1-324 ∷ []) ∷ []) Eq.refl

private
  q203 : WsL → Eqn
  q203 c4 = eqn (Sw12 ∷ Bx2-314 ∷ []) (Bx1-324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·314⟩ c4)

-- nat 1 BOX(3;2014): 8 steps
lem-nat-1-BOX⟨3·2014⟩ : WsL → ⟪ (Sw12 ∷ Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·2014⟩ c4 = derive (Sw12 ∷ Bx3-2014 ∷ []) (Bx3-1024 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-314 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ []) ∷
   rw 0 (q184 c4) ∷
   rw 1 (q185 c4) ∷
   rw 2 (q203 c4) ∷
   rw 3 (q185 c4) ∷
   rw 4 (q184 c4) ∷
   rw 5 (q203 c4) ∷
   re 0 6 (Bx3-1024 ∷ []) ∷ []) Eq.refl

-- nat 2 BOX(2;31): 3 steps
lem-nat-2-BOX⟨2·31⟩ : WsL → ⟪ (Sw23 ∷ Bx2-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-21 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·31⟩ c4 = derive (Sw23 ∷ Bx2-31 ∷ []) (Bx3-21 ∷ Sw23 ∷ [])
  (re 1 1 (CZ13 ∷ []) ∷
   rw 0 (q171 c4) ∷
   re 0 1 (Bx3-21 ∷ []) ∷ []) Eq.refl

private
  q204 : WsL → Eqn
  q204 c4 = eqn (CCZ023 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ023 ∷ []) (wl0065 c4)
  q205 : WsL → Eqn
  q205 c4 = eqn (Sw23 ∷ Toff302 ∷ []) (Toff203 ∷ Sw23 ∷ []) (wl0066 c4)
  q206 : WsL → Eqn
  q206 c4 = eqn (Sw23 ∷ Bx2-31 ∷ []) (Bx3-21 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·31⟩ c4)

-- nat 2 BOX(3;201): 8 steps
lem-nat-2-BOX⟨3·201⟩ : WsL → ⟪ (Sw23 ∷ Bx3-201 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-301 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·201⟩ c4 = derive (Sw23 ∷ Bx3-201 ∷ []) (Bx2-301 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) ∷
   rw⁻ 0 (q204 c4) ∷
   rw 1 (q205 c4) ∷
   rw 2 (q206 c4) ∷
   rw 3 (q205 c4) ∷
   rw⁻ 4 (q204 c4) ∷
   rw 5 (q206 c4) ∷
   re 0 6 (Bx2-301 ∷ []) ∷ []) Eq.refl

private
  q207 : WsL → Eqn
  q207 c4 = eqn (Sw23 ∷ Bx3-201 ∷ []) (Bx2-301 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·201⟩ c4)

-- nat 2 BOX(2;3401): 8 steps
lem-nat-2-BOX⟨2·3401⟩ : WsL → ⟪ (Sw23 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·3401⟩ c4 = derive (Sw23 ∷ Bx2-3401 ∷ []) (Bx3-2401 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-201 ∷ Toff234 ∷ CCZ234 ∷ Bx3-201 ∷ []) ∷
   rw⁻ 0 (q28 c4) ∷
   rw 1 (q29 c4) ∷
   rw 2 (q207 c4) ∷
   rw 3 (q29 c4) ∷
   rw⁻ 4 (q28 c4) ∷
   rw 5 (q207 c4) ∷
   re 0 6 (Bx3-2401 ∷ []) ∷ []) Eq.refl

private
  q208 : WsL → Eqn
  q208 c4 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wl0035 c4)

-- nat 0 SBOX(0;1;2;3): 3 steps
lem-nat-0-SBOX⟨0·1·2·3⟩ : WsL → ⟪ (Sw01 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·1·2·3⟩ c4 = derive (Sw01 ∷ Sb0-1-2-3 ∷ []) (Sb1-0-2-3 ∷ Sw01 ∷ [])
  (re 1 1 (CS12 ∷ []) ∷
   rw⁻ 0 (q208 c4) ∷
   re 0 1 (Sb1-0-2-3 ∷ []) ∷ []) Eq.refl

private
  q209 : WsL → Eqn
  q209 c4 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wl0036 c4)

-- nat 0 SBOXd(0;1;2;3): 3 steps
lem-nat-0-SBOXd⟨0·1·2·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·1·2·3⟩ c4 = derive (Sw01 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻1-0-2-3 ∷ Sw01 ∷ [])
  (re 1 1 (CS12⁻ ∷ []) ∷
   rw⁻ 0 (q209 c4) ∷
   re 0 1 (Sb⁻1-0-2-3 ∷ []) ∷ []) Eq.refl

private
  q210 : WsL → Eqn
  q210 c4 = eqn (Sw01 ∷ Bx0-1432 ∷ []) (Bx1-0432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·1432⟩ c4)
  q211 : WsL → Eqn
  q211 c4 = eqn (Sw01 ∷ Sb0-1-2-3 ∷ []) (Sb1-0-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·2·3⟩ c4)
  q212 : WsL → Eqn
  q212 c4 = eqn (Sw01 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻1-0-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·1·2·3⟩ c4)

-- nat 0 SBOX(0;1;43;2): 7 steps
lem-nat-0-SBOX⟨0·1·43·2⟩ : WsL → ⟪ (Sw01 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-43-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·1·43·2⟩ c4 = derive (Sw01 ∷ Sb0-1-43-2 ∷ []) (Sb1-0-43-2 ∷ Sw01 ∷ [])
  (re 1 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) ∷
   rw 0 (q210 c4) ∷
   rw 1 (q110 c4) ∷
   rw 2 (q211 c4) ∷
   rw 3 (q110 c4) ∷
   rw 4 (q212 c4) ∷
   re 0 5 (Sb1-0-43-2 ∷ []) ∷ []) Eq.refl

-- nat 1 BOX(0;42): 3 steps
lem-nat-1-BOX⟨0·42⟩ : WsL → ⟪ (Sw12 ∷ Bx0-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-41 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·42⟩ c4 = derive (Sw12 ∷ Bx0-42 ∷ []) (Bx0-41 ∷ Sw12 ∷ [])
  (re 1 1 (CZ24 ∷ []) ∷
   rw⁻ 0 (q200 c4) ∷
   re 0 1 (Bx0-41 ∷ []) ∷ []) Eq.refl

private
  q213 : WsL → Eqn
  q213 c4 = eqn (Sw12 ∷ Toff403 ∷ []) (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4)
  q214 : WsL → Eqn
  q214 c4 = eqn (Sw12 ∷ Bx0-42 ∷ []) (Bx0-41 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·42⟩ c4)

-- nat 1 BOX(4;032): 8 steps
lem-nat-1-BOX⟨4·032⟩ : WsL → ⟪ (Sw12 ∷ Bx4-032 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-031 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·032⟩ c4 = derive (Sw12 ∷ Bx4-032 ∷ []) (Bx4-031 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) ∷
   rw 0 (q1 c4) ∷
   rw 1 (q213 c4) ∷
   rw 2 (q214 c4) ∷
   rw 3 (q213 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q214 c4) ∷
   re 0 6 (Bx4-031 ∷ []) ∷ []) Eq.refl

private
  q215 : WsL → Eqn
  q215 c4 = eqn (Sw12 ∷ CCZ014 ∷ []) (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4)
  q216 : WsL → Eqn
  q216 c4 = eqn (Sw12 ∷ Toff014 ∷ []) (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4)
  q217 : WsL → Eqn
  q217 c4 = eqn (Sw12 ∷ Bx4-032 ∷ []) (Bx4-031 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·032⟩ c4)

-- nat 1 BOX(0;4132): 8 steps
lem-nat-1-BOX⟨0·4132⟩ : WsL → ⟪ (Sw12 ∷ Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·4132⟩ c4 = derive (Sw12 ∷ Bx0-4132 ∷ []) (Bx0-4231 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-032 ∷ Toff014 ∷ CCZ014 ∷ Bx4-032 ∷ []) ∷
   rw 0 (q215 c4) ∷
   rw 1 (q216 c4) ∷
   rw 2 (q217 c4) ∷
   rw 3 (q216 c4) ∷
   rw 4 (q215 c4) ∷
   rw 5 (q217 c4) ∷
   re 0 6 (Bx0-4231 ∷ []) ∷ []) Eq.refl
