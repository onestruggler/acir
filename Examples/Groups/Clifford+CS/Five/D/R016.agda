{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R016 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0003 ; wl0004 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0015 ; wl0016 ; wl0017 ; wl0018 ; wl0019 ; wl0020 ; wl0021 ; wl0025 ; wl0030 ; wl0034 ; wl0042 ; wl0046 ; wl0053 ; wl0057 ; wl0058 ; wl0061 ; wl0065 ; wl0067 ; wl0068 ; wl0078 ; wl0082 ; wl0084 ; wl0089 ; wl0090 ; wl0091 ; wl0093 ; wl0095 ; wl0103 ; wl0104 ; wl0108 ; wl0110 ; wl0111 ; wl0112 ; wl0116 ; wl0117 ; wl0121 ; wl0122 ; wl0124 ; wl0126 ; wl0132 ; wl0133 ; wl0136 ; wl0138 ; wl0139 ; wl0140 ; wl0143 ; wl0146 ; wl0159 ; wl0160 ; wl0161 ; wl0162 ; wl0163 ; wl0164 ; wl0165)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-CCZ034 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF024 ; lem-nat-1-TOFF203 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF034 ; lem-nat-2-TOFF102 ; lem-nat-2-TOFF103 ; lem-nat-3-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF103 ; lem-nat-1-TOFF301 ; lem-nat-1-TOFF302 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF304 ; lem-nat-3-CCZ023 ; lem-nat-3-TOFF203 ; lem-nat-3-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-TOFF204 ; lem-nat-0-TOFF214 ; lem-nat-3-TOFF023 ; lem-nat-3-TOFF214)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-TOFF024 ; lem-nat-1-TOFF401 ; lem-nat-2-CCZ014 ; lem-nat-2-TOFF214 ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-CZ02 ; lem-nat-2-CS13 ; lem-nat-2-CSd13 ; lem-nat-2-CZ12 ; lem-nat-2-CZ13 ; lem-nat-2-TOFF314)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-BOX⟨2·01⟩ ; lem-nat-0-TOFF134 ; lem-nat-1-BOX⟨2·10⟩ ; lem-nat-2-BOX⟨0·42⟩ ; lem-nat-2-BOX⟨0·43⟩ ; lem-nat-2-TOFF124 ; lem-nat-2-TOFF403)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨0·3142⟩ ; lem-nat-0-TOFF034 ; lem-nat-1-TOFF034 ; lem-nat-1-TOFF403 ; lem-nat-3-TOFF024)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-1-TOFF402 ; lem-nat-2-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-1-BOX⟨1·30⟩ ; lem-nat-1-BOX⟨2·30⟩ ; lem-nat-3-TOFF213)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-0-BOX⟨1·0432⟩)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-0-BOX⟨2·10⟩ ; lem-nat-2-BOX⟨1·32⟩ ; lem-nat-3-BOX⟨1·23⟩ ; lem-nat-3-BOX⟨1·24⟩)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-2-BOX⟨1·23⟩)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-1-BOX⟨0·31⟩ ; lem-nat-1-BOX⟨0·32⟩ ; lem-nat-1-BOX⟨0·3241⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-BOX⟨0·31⟩ ; lem-nat-0-BOX⟨1·30⟩ ; lem-nat-0-BOX⟨1·3240⟩ ; lem-nat-1-BOX⟨0·42⟩ ; lem-nat-1-BOX⟨3·14⟩ ; lem-nat-1-BOX⟨3·24⟩)

private
  q1 : WsL → Eqn
  q1 c4 = eqn (CZ24 ∷ Sw12 ∷ []) (Sw12 ∷ CZ14 ∷ []) (wl0089 c4)

-- nat 1 BOX(0;41): 3 steps
lem-nat-1-BOX⟨0·41⟩ : WsL → ⟪ (Sw12 ∷ Bx0-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-42 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·41⟩ c4 = derive (Sw12 ∷ Bx0-41 ∷ []) (Bx0-42 ∷ Sw12 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 0 1 (Bx0-42 ∷ []) ∷ []) Eq.refl

private
  q2 : WsL → Eqn
  q2 c4 = eqn (Sw12 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw12 ∷ []) (lem-nat-1-CCZ034 c4)
  q3 : WsL → Eqn
  q3 c4 = eqn (Sw12 ∷ Toff403 ∷ []) (Toff403 ∷ Sw12 ∷ []) (lem-nat-1-TOFF403 c4)
  q4 : WsL → Eqn
  q4 c4 = eqn (Sw12 ∷ Bx0-41 ∷ []) (Bx0-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·41⟩ c4)

-- nat 1 BOX(4;031): 8 steps
lem-nat-1-BOX⟨4·031⟩ : WsL → ⟪ (Sw12 ∷ Bx4-031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-032 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·031⟩ c4 = derive (Sw12 ∷ Bx4-031 ∷ []) (Bx4-032 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) ∷
   rw 0 (q2 c4) ∷
   rw 1 (q3 c4) ∷
   rw 2 (q4 c4) ∷
   rw 3 (q3 c4) ∷
   rw 4 (q2 c4) ∷
   rw 5 (q4 c4) ∷
   re 0 6 (Bx4-032 ∷ []) ∷ []) Eq.refl

private
  q5 : WsL → Eqn
  q5 c4 = eqn (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4)
  q6 : WsL → Eqn
  q6 c4 = eqn (Sw12 ∷ Toff024 ∷ []) (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4)
  q7 : WsL → Eqn
  q7 c4 = eqn (Sw12 ∷ Bx4-031 ∷ []) (Bx4-032 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·031⟩ c4)

-- nat 1 BOX(0;4231): 8 steps
lem-nat-1-BOX⟨0·4231⟩ : WsL → ⟪ (Sw12 ∷ Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·4231⟩ c4 = derive (Sw12 ∷ Bx0-4231 ∷ []) (Bx0-4132 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-031 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ []) ∷
   rw 0 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw 2 (q7 c4) ∷
   rw 3 (q6 c4) ∷
   rw 4 (q5 c4) ∷
   rw 5 (q7 c4) ∷
   re 0 6 (Bx0-4132 ∷ []) ∷ []) Eq.refl

private
  q8 : WsL → Eqn
  q8 c4 = eqn (Sw12 ∷ Toff402 ∷ []) (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4)
  q9 : WsL → Eqn
  q9 c4 = eqn (Sw12 ∷ Bx0-43 ∷ []) (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ))

-- nat 1 BOX(4;023): 8 steps
lem-nat-1-BOX⟨4·023⟩ : WsL → ⟪ (Sw12 ∷ Bx4-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-013 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·023⟩ c4 = derive (Sw12 ∷ Bx4-023 ∷ []) (Bx4-013 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) ∷
   rw 0 (q5 c4) ∷
   rw 1 (q8 c4) ∷
   rw 2 (q9 c4) ∷
   rw 3 (q8 c4) ∷
   rw 4 (q5 c4) ∷
   rw 5 (q9 c4) ∷
   re 0 6 (Bx4-013 ∷ []) ∷ []) Eq.refl

private
  q10 : WsL → Eqn
  q10 c4 = eqn (Sw12 ∷ CCZ014 ∷ []) (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4)
  q11 : WsL → Eqn
  q11 c4 = eqn (Sw12 ∷ Toff014 ∷ []) (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4)
  q12 : WsL → Eqn
  q12 c4 = eqn (Sw12 ∷ Bx4-023 ∷ []) (Bx4-013 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·023⟩ c4)

-- nat 1 BOX(0;4123): 8 steps
lem-nat-1-BOX⟨0·4123⟩ : WsL → ⟪ (Sw12 ∷ Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·4123⟩ c4 = derive (Sw12 ∷ Bx0-4123 ∷ []) (Bx0-4213 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) ∷
   rw 0 (q10 c4) ∷
   rw 1 (q11 c4) ∷
   rw 2 (q12 c4) ∷
   rw 3 (q11 c4) ∷
   rw 4 (q10 c4) ∷
   rw 5 (q12 c4) ∷
   re 0 6 (Bx0-4213 ∷ []) ∷ []) Eq.refl

private
  q13 : WsL → Eqn
  q13 c4 = eqn (Sw23 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4)
  q14 : WsL → Eqn
  q14 c4 = eqn (Sw23 ∷ Toff401 ∷ []) (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4)
  q15 : WsL → Eqn
  q15 c4 = eqn (Sw23 ∷ Bx0-43 ∷ []) (Bx0-42 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·43⟩ c4)

-- nat 2 BOX(4;013): 8 steps
lem-nat-2-BOX⟨4·013⟩ : WsL → ⟪ (Sw23 ∷ Bx4-013 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-012 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·013⟩ c4 = derive (Sw23 ∷ Bx4-013 ∷ []) (Bx4-012 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) ∷
   rw 0 (q13 c4) ∷
   rw 1 (q14 c4) ∷
   rw 2 (q15 c4) ∷
   rw 3 (q14 c4) ∷
   rw 4 (q13 c4) ∷
   rw 5 (q15 c4) ∷
   re 0 6 (Bx4-012 ∷ []) ∷ []) Eq.refl

private
  q16 : WsL → Eqn
  q16 c4 = eqn (Sw23 ∷ CCZ024 ∷ []) (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4)
  q17 : WsL → Eqn
  q17 c4 = eqn (Sw23 ∷ Toff024 ∷ []) (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4)
  q18 : WsL → Eqn
  q18 c4 = eqn (Sw23 ∷ Bx4-013 ∷ []) (Bx4-012 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·013⟩ c4)

-- nat 2 BOX(0;4213): 8 steps
lem-nat-2-BOX⟨0·4213⟩ : WsL → ⟪ (Sw23 ∷ Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·4213⟩ c4 = derive (Sw23 ∷ Bx0-4213 ∷ []) (Bx0-4312 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ Bx4-013 ∷ []) ∷
   rw 0 (q16 c4) ∷
   rw 1 (q17 c4) ∷
   rw 2 (q18 c4) ∷
   rw 3 (q17 c4) ∷
   rw 4 (q16 c4) ∷
   rw 5 (q18 c4) ∷
   re 0 6 (Bx0-4312 ∷ []) ∷ []) Eq.refl

private
  q19 : WsL → Eqn
  q19 c4 = eqn (Sw12 ∷ Toff401 ∷ []) (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4)
  q20 : WsL → Eqn
  q20 c4 = eqn (Sw12 ∷ Bx0-42 ∷ []) (Bx0-41 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·42⟩ c4)

-- nat 1 BOX(4;012): 8 steps
lem-nat-1-BOX⟨4·012⟩ : WsL → ⟪ (Sw12 ∷ Bx4-012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-021 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·012⟩ c4 = derive (Sw12 ∷ Bx4-012 ∷ []) (Bx4-021 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) ∷
   rw 0 (q10 c4) ∷
   rw 1 (q19 c4) ∷
   rw 2 (q20 c4) ∷
   rw 3 (q19 c4) ∷
   rw 4 (q10 c4) ∷
   rw 5 (q20 c4) ∷
   re 0 6 (Bx4-021 ∷ []) ∷ []) Eq.refl

private
  q21 : WsL → Eqn
  q21 c4 = eqn (Sw12 ∷ Toff034 ∷ []) (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4)
  q22 : WsL → Eqn
  q22 c4 = eqn (Sw12 ∷ Bx4-012 ∷ []) (Bx4-021 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·012⟩ c4)

-- nat 1 BOX(0;4312): 8 steps
lem-nat-1-BOX⟨0·4312⟩ : WsL → ⟪ (Sw12 ∷ Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·4312⟩ c4 = derive (Sw12 ∷ Bx0-4312 ∷ []) (Bx0-4321 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) ∷
   rw 0 (q2 c4) ∷
   rw 1 (q21 c4) ∷
   rw 2 (q22 c4) ∷
   rw 3 (q21 c4) ∷
   rw 4 (q2 c4) ∷
   rw 5 (q22 c4) ∷
   re 0 6 (Bx0-4321 ∷ []) ∷ []) Eq.refl

private
  q23 : WsL → Eqn
  q23 c4 = eqn (Sw23 ∷ Bx0-42 ∷ []) (Bx0-43 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·42⟩ c4)

-- nat 2 BOX(4;012): 8 steps
lem-nat-2-BOX⟨4·012⟩ : WsL → ⟪ (Sw23 ∷ Bx4-012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-013 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·012⟩ c4 = derive (Sw23 ∷ Bx4-012 ∷ []) (Bx4-013 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) ∷
   rw 0 (q13 c4) ∷
   rw 1 (q14 c4) ∷
   rw 2 (q23 c4) ∷
   rw 3 (q14 c4) ∷
   rw 4 (q13 c4) ∷
   rw 5 (q23 c4) ∷
   re 0 6 (Bx4-013 ∷ []) ∷ []) Eq.refl

private
  q24 : WsL → Eqn
  q24 c4 = eqn (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4)
  q25 : WsL → Eqn
  q25 c4 = eqn (Sw23 ∷ Toff034 ∷ []) (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4)
  q26 : WsL → Eqn
  q26 c4 = eqn (Sw23 ∷ Bx4-012 ∷ []) (Bx4-013 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·012⟩ c4)

-- nat 2 BOX(0;4312): 8 steps
lem-nat-2-BOX⟨0·4312⟩ : WsL → ⟪ (Sw23 ∷ Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·4312⟩ c4 = derive (Sw23 ∷ Bx0-4312 ∷ []) (Bx0-4213 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) ∷
   rw 0 (q24 c4) ∷
   rw 1 (q25 c4) ∷
   rw 2 (q26 c4) ∷
   rw 3 (q25 c4) ∷
   rw 4 (q24 c4) ∷
   rw 5 (q26 c4) ∷
   re 0 6 (Bx0-4213 ∷ []) ∷ []) Eq.refl

-- nat 1 BOX(4;021): 8 steps
lem-nat-1-BOX⟨4·021⟩ : WsL → ⟪ (Sw12 ∷ Bx4-021 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-012 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·021⟩ c4 = derive (Sw12 ∷ Bx4-021 ∷ []) (Bx4-012 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) ∷
   rw 0 (q5 c4) ∷
   rw 1 (q8 c4) ∷
   rw 2 (q4 c4) ∷
   rw 3 (q8 c4) ∷
   rw 4 (q5 c4) ∷
   rw 5 (q4 c4) ∷
   re 0 6 (Bx4-012 ∷ []) ∷ []) Eq.refl

private
  q27 : WsL → Eqn
  q27 c4 = eqn (Sw12 ∷ Bx4-021 ∷ []) (Bx4-012 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·021⟩ c4)

-- nat 1 BOX(0;4321): 8 steps
lem-nat-1-BOX⟨0·4321⟩ : WsL → ⟪ (Sw12 ∷ Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·4321⟩ c4 = derive (Sw12 ∷ Bx0-4321 ∷ []) (Bx0-4312 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) ∷
   rw 0 (q2 c4) ∷
   rw 1 (q21 c4) ∷
   rw 2 (q27 c4) ∷
   rw 3 (q21 c4) ∷
   rw 4 (q2 c4) ∷
   rw 5 (q27 c4) ∷
   re 0 6 (Bx0-4312 ∷ []) ∷ []) Eq.refl

private
  q28 : WsL → Eqn
  q28 c4 = eqn (CZ14 ∷ Sw23 ∷ []) (Sw23 ∷ CZ14 ∷ []) (wl0042 c4)

-- nat 2 BOX(0;41): 3 steps
lem-nat-2-BOX⟨0·41⟩ : WsL → ⟪ (Sw23 ∷ Bx0-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-41 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·41⟩ c4 = derive (Sw23 ∷ Bx0-41 ∷ []) (Bx0-41 ∷ Sw23 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   rw⁻ 0 (q28 c4) ∷
   re 0 1 (Bx0-41 ∷ []) ∷ []) Eq.refl

private
  q29 : WsL → Eqn
  q29 c4 = eqn (Sw23 ∷ Toff403 ∷ []) (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4)
  q30 : WsL → Eqn
  q30 c4 = eqn (Sw23 ∷ Bx0-41 ∷ []) (Bx0-41 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·41⟩ c4)

-- nat 2 BOX(4;031): 8 steps
lem-nat-2-BOX⟨4·031⟩ : WsL → ⟪ (Sw23 ∷ Bx4-031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-021 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·031⟩ c4 = derive (Sw23 ∷ Bx4-031 ∷ []) (Bx4-021 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) ∷
   rw 0 (q24 c4) ∷
   rw 1 (q29 c4) ∷
   rw 2 (q30 c4) ∷
   rw 3 (q29 c4) ∷
   rw 4 (q24 c4) ∷
   rw 5 (q30 c4) ∷
   re 0 6 (Bx4-021 ∷ []) ∷ []) Eq.refl

private
  q31 : WsL → Eqn
  q31 c4 = eqn (Sw23 ∷ Bx4-031 ∷ []) (Bx4-021 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·031⟩ c4)

-- nat 2 BOX(0;4231): 8 steps
lem-nat-2-BOX⟨0·4231⟩ : WsL → ⟪ (Sw23 ∷ Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·4231⟩ c4 = derive (Sw23 ∷ Bx0-4231 ∷ []) (Bx0-4321 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-031 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ []) ∷
   rw 0 (q16 c4) ∷
   rw 1 (q17 c4) ∷
   rw 2 (q31 c4) ∷
   rw 3 (q17 c4) ∷
   rw 4 (q16 c4) ∷
   rw 5 (q31 c4) ∷
   re 0 6 (Bx0-4321 ∷ []) ∷ []) Eq.refl

private
  q32 : WsL → Eqn
  q32 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 c4)
  q33 : WsL → Eqn
  q33 c4 = eqn (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4)
  q34 : WsL → Eqn
  q34 c4 = eqn (Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap))
  q35 : WsL → Eqn
  q35 c4 = eqn (CX10 ∷ Sw34 ∷ []) (Sw34 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Swap ↑))
  q36 : WsL → Eqn
  q36 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 c4)
  q37 : WsL → Eqn
  q37 c4 = eqn (CX30 ∷ Sw12 ∷ []) (Sw12 ∷ CX30 ∷ []) (wl0124 c4)
  q38 : WsL → Eqn
  q38 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 c4)
  q39 : WsL → Eqn
  q39 c4 = eqn (Sw01 ∷ Sw34 ∷ []) (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑))
  q40 : WsL → Eqn
  q40 c4 = eqn (CX30 ∷ Sw01 ∷ []) (Sw01 ∷ CX31 ∷ []) (wl0122 c4)

-- resp CX40 at 3: 20 steps
lem-resp-CX40-at-3 : WsL → ⟪ (CX40 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX41 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CX40-at-3 c4 = derive (CX40 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX41 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q32 c4) ∷
   re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q33 c4) ∷
   rw 4 (q34 c4) ∷
   rw 3 (q35 c4) ∷
   rw 2 (q34 c4) ∷
   rw⁻ 0 (q33 c4) ∷
   re 1 7 (CX40 ∷ []) ∷
   rw⁻ 2 (q36 c4) ∷
   re 1 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) ∷
   rw⁻ 3 (q34 c4) ∷
   rw 2 (q37 c4) ∷
   rw⁻ 1 (q34 c4) ∷
   re 2 3 (CX40 ∷ []) ∷
   rw⁻ 3 (q38 c4) ∷
   re 2 1 (Sw34 ∷ CX30 ∷ Sw34 ∷ []) ∷
   rw⁻ 4 (q39 c4) ∷
   rw 3 (q40 c4) ∷
   rw⁻ 2 (q39 c4) ∷
   re 3 3 (CX41 ∷ []) ∷ []) Eq.refl

private
  q41 : WsL → Eqn
  q41 c4 = eqn (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4)
  q42 : WsL → Eqn
  q42 c4 = eqn (Sw12 ∷ Toff103 ∷ []) (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4)
  q43 : WsL → Eqn
  q43 c4 = eqn (Sw12 ∷ Bx3-14 ∷ []) (Bx3-24 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·14⟩ c4)

-- nat 1 BOX(1;304): 8 steps
lem-nat-1-BOX⟨1·304⟩ : WsL → ⟪ (Sw12 ∷ Bx1-304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-304 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·304⟩ c4 = derive (Sw12 ∷ Bx1-304 ∷ []) (Bx2-304 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) ∷
   rw 0 (q41 c4) ∷
   rw 1 (q42 c4) ∷
   rw 2 (q43 c4) ∷
   rw 3 (q42 c4) ∷
   rw 4 (q41 c4) ∷
   rw 5 (q43 c4) ∷
   re 0 6 (Bx2-304 ∷ []) ∷ []) Eq.refl

private
  q44 : WsL → Eqn
  q44 c4 = eqn (CCZ123 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ123 ∷ []) (wl0111 c4)
  q45 : WsL → Eqn
  q45 c4 = eqn (Sw12 ∷ Toff312 ∷ []) (Toff312 ∷ Sw12 ∷ []) (wl0143 c4)
  q46 : WsL → Eqn
  q46 c4 = eqn (Sw12 ∷ Bx1-304 ∷ []) (Bx2-304 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·304⟩ c4)

-- nat 1 BOX(3;1204): 8 steps
lem-nat-1-BOX⟨3·1204⟩ : WsL → ⟪ (Sw12 ∷ Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·1204⟩ c4 = derive (Sw12 ∷ Bx3-1204 ∷ []) (Bx3-2104 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-304 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ []) ∷
   rw⁻ 0 (q44 c4) ∷
   rw 1 (q45 c4) ∷
   rw 2 (q46 c4) ∷
   rw 3 (q45 c4) ∷
   rw⁻ 4 (q44 c4) ∷
   rw 5 (q46 c4) ∷
   re 0 6 (Bx3-2104 ∷ []) ∷ []) Eq.refl

private
  q47 : WsL → Eqn
  q47 c4 = eqn (CCZ123 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ023 ∷ []) (wl0103 c4)
  q48 : WsL → Eqn
  q48 c4 = eqn (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) (wl0104 c4)
  q49 : WsL → Eqn
  q49 c4 = eqn (Sw01 ∷ Bx3-24 ∷ []) (Bx3-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑))

-- nat 0 BOX(2;304): 8 steps
lem-nat-0-BOX⟨2·304⟩ : WsL → ⟪ (Sw01 ∷ Bx2-304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-314 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·304⟩ c4 = derive (Sw01 ∷ Bx2-304 ∷ []) (Bx2-314 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) ∷
   rw⁻ 0 (q47 c4) ∷
   rw 1 (q48 c4) ∷
   rw 2 (q49 c4) ∷
   rw 3 (q48 c4) ∷
   rw⁻ 4 (q47 c4) ∷
   rw 5 (q49 c4) ∷
   re 0 6 (Bx2-314 ∷ []) ∷ []) Eq.refl

private
  q50 : WsL → Eqn
  q50 c4 = eqn (CCZ023 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ123 ∷ []) (wl0003 c4)
  q51 : WsL → Eqn
  q51 c4 = eqn (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) (wl0110 c4)
  q52 : WsL → Eqn
  q52 c4 = eqn (Sw01 ∷ Bx2-304 ∷ []) (Bx2-314 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·304⟩ c4)

-- nat 0 BOX(3;2104): 8 steps
lem-nat-0-BOX⟨3·2104⟩ : WsL → ⟪ (Sw01 ∷ Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·2104⟩ c4 = derive (Sw01 ∷ Bx3-2104 ∷ []) (Bx3-2014 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-304 ∷ Toff312 ∷ CCZ123 ∷ Bx2-304 ∷ []) ∷
   rw⁻ 0 (q50 c4) ∷
   rw 1 (q51 c4) ∷
   rw 2 (q52 c4) ∷
   rw 3 (q51 c4) ∷
   rw⁻ 4 (q50 c4) ∷
   rw 5 (q52 c4) ∷
   re 0 6 (Bx3-2014 ∷ []) ∷ []) Eq.refl

private
  q53 : WsL → Eqn
  q53 c4 = eqn (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) (wl0004 c4)

-- nat 0 BOX(2;314): 8 steps
lem-nat-0-BOX⟨2·314⟩ : WsL → ⟪ (Sw01 ∷ Bx2-314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-304 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·314⟩ c4 = derive (Sw01 ∷ Bx2-314 ∷ []) (Bx2-304 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) ∷
   rw⁻ 0 (q50 c4) ∷
   rw 1 (q53 c4) ∷
   rw 2 (q49 c4) ∷
   rw 3 (q53 c4) ∷
   rw⁻ 4 (q50 c4) ∷
   rw 5 (q49 c4) ∷
   re 0 6 (Bx2-304 ∷ []) ∷ []) Eq.refl

private
  q54 : WsL → Eqn
  q54 c4 = eqn (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) (wl0116 c4)
  q55 : WsL → Eqn
  q55 c4 = eqn (Sw01 ∷ Bx2-314 ∷ []) (Bx2-304 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·314⟩ c4)

-- nat 0 BOX(3;2014): 8 steps
lem-nat-0-BOX⟨3·2014⟩ : WsL → ⟪ (Sw01 ∷ Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·2014⟩ c4 = derive (Sw01 ∷ Bx3-2014 ∷ []) (Bx3-2104 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-314 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ []) ∷
   rw⁻ 0 (q47 c4) ∷
   rw 1 (q54 c4) ∷
   rw 2 (q55 c4) ∷
   rw 3 (q54 c4) ∷
   rw⁻ 4 (q47 c4) ∷
   rw 5 (q55 c4) ∷
   re 0 6 (Bx3-2104 ∷ []) ∷ []) Eq.refl

private
  q56 : WsL → Eqn
  q56 c4 = eqn (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4)
  q57 : WsL → Eqn
  q57 c4 = eqn (Sw12 ∷ Toff203 ∷ []) (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4)
  q58 : WsL → Eqn
  q58 c4 = eqn (Sw12 ∷ Bx3-24 ∷ []) (Bx3-14 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·24⟩ c4)

-- nat 1 BOX(2;304): 8 steps
lem-nat-1-BOX⟨2·304⟩ : WsL → ⟪ (Sw12 ∷ Bx2-304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-304 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·304⟩ c4 = derive (Sw12 ∷ Bx2-304 ∷ []) (Bx1-304 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) ∷
   rw 0 (q56 c4) ∷
   rw 1 (q57 c4) ∷
   rw 2 (q58 c4) ∷
   rw 3 (q57 c4) ∷
   rw 4 (q56 c4) ∷
   rw 5 (q58 c4) ∷
   re 0 6 (Bx1-304 ∷ []) ∷ []) Eq.refl

private
  q59 : WsL → Eqn
  q59 c4 = eqn (Sw12 ∷ Bx2-304 ∷ []) (Bx1-304 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·304⟩ c4)

-- nat 1 BOX(3;2104): 8 steps
lem-nat-1-BOX⟨3·2104⟩ : WsL → ⟪ (Sw12 ∷ Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·2104⟩ c4 = derive (Sw12 ∷ Bx3-2104 ∷ []) (Bx3-1204 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-304 ∷ Toff312 ∷ CCZ123 ∷ Bx2-304 ∷ []) ∷
   rw⁻ 0 (q44 c4) ∷
   rw 1 (q45 c4) ∷
   rw 2 (q59 c4) ∷
   rw 3 (q45 c4) ∷
   rw⁻ 4 (q44 c4) ∷
   rw 5 (q59 c4) ∷
   re 0 6 (Bx3-1204 ∷ []) ∷ []) Eq.refl

private
  q60 : WsL → Eqn
  q60 c4 = eqn (Sw12 ∷ Toff301 ∷ []) (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4)
  q61 : WsL → Eqn
  q61 c4 = eqn (Sw12 ∷ Bx0-32 ∷ []) (Bx0-31 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·32⟩ c4)

-- nat 1 BOX(3;012): 8 steps
lem-nat-1-BOX⟨3·012⟩ : WsL → ⟪ (Sw12 ∷ Bx3-012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-021 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·012⟩ c4 = derive (Sw12 ∷ Bx3-012 ∷ []) (Bx3-021 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) ∷
   rw 0 (q41 c4) ∷
   rw 1 (q60 c4) ∷
   rw 2 (q61 c4) ∷
   rw 3 (q60 c4) ∷
   rw 4 (q41 c4) ∷
   rw 5 (q61 c4) ∷
   re 0 6 (Bx3-021 ∷ []) ∷ []) Eq.refl

private
  q62 : WsL → Eqn
  q62 c4 = eqn (Sw12 ∷ Bx3-012 ∷ []) (Bx3-021 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·012⟩ c4)

-- nat 1 BOX(0;3412): 8 steps
lem-nat-1-BOX⟨0·3412⟩ : WsL → ⟪ (Sw12 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·3412⟩ c4 = derive (Sw12 ∷ Bx0-3412 ∷ []) (Bx0-3421 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) ∷
   rw 0 (q2 c4) ∷
   rw 1 (q21 c4) ∷
   rw 2 (q62 c4) ∷
   rw 3 (q21 c4) ∷
   rw 4 (q2 c4) ∷
   rw 5 (q62 c4) ∷
   re 0 6 (Bx0-3421 ∷ []) ∷ []) Eq.refl

private
  q63 : WsL → Eqn
  q63 c4 = eqn (Sw12 ∷ Bx1-30 ∷ []) (Bx2-30 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·30⟩ c4)

-- nat 1 BOX(3;120): 8 steps
lem-nat-1-BOX⟨3·120⟩ : WsL → ⟪ (Sw12 ∷ Bx3-120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-210 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·120⟩ c4 = derive (Sw12 ∷ Bx3-120 ∷ []) (Bx3-210 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-30 ∷ Toff312 ∷ CCZ123 ∷ Bx1-30 ∷ []) ∷
   rw⁻ 0 (q44 c4) ∷
   rw 1 (q45 c4) ∷
   rw 2 (q63 c4) ∷
   rw 3 (q45 c4) ∷
   rw⁻ 4 (q44 c4) ∷
   rw 5 (q63 c4) ∷
   re 0 6 (Bx3-210 ∷ []) ∷ []) Eq.refl

private
  q64 : WsL → Eqn
  q64 c4 = eqn (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) (wl0084 c4)
  q65 : WsL → Eqn
  q65 c4 = eqn (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) (wl0136 c4)
  q66 : WsL → Eqn
  q66 c4 = eqn (Sw12 ∷ Bx3-120 ∷ []) (Bx3-210 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·120⟩ c4)

-- nat 1 BOX(1;3420): 8 steps
lem-nat-1-BOX⟨1·3420⟩ : WsL → ⟪ (Sw12 ∷ Bx1-3420 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·3420⟩ c4 = derive (Sw12 ∷ Bx1-3420 ∷ []) (Bx2-3410 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff134 ∷ Bx3-120 ∷ Toff134 ∷ CCZ134 ∷ Bx3-120 ∷ []) ∷
   rw⁻ 0 (q64 c4) ∷
   rw 1 (q65 c4) ∷
   rw 2 (q66 c4) ∷
   rw 3 (q65 c4) ∷
   rw⁻ 4 (q64 c4) ∷
   rw 5 (q66 c4) ∷
   re 0 6 (Bx2-3410 ∷ []) ∷ []) Eq.refl

private
  q67 : WsL → Eqn
  q67 c4 = eqn (Sw12 ∷ Bx2-30 ∷ []) (Bx1-30 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·30⟩ c4)

-- nat 1 BOX(3;210): 8 steps
lem-nat-1-BOX⟨3·210⟩ : WsL → ⟪ (Sw12 ∷ Bx3-210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-120 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·210⟩ c4 = derive (Sw12 ∷ Bx3-210 ∷ []) (Bx3-120 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) ∷
   rw⁻ 0 (q44 c4) ∷
   rw 1 (q45 c4) ∷
   rw 2 (q67 c4) ∷
   rw 3 (q45 c4) ∷
   rw⁻ 4 (q44 c4) ∷
   rw 5 (q67 c4) ∷
   re 0 6 (Bx3-120 ∷ []) ∷ []) Eq.refl

private
  q68 : WsL → Eqn
  q68 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl0034 c4)
  q69 : WsL → Eqn
  q69 c4 = eqn (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) (wl0140 c4)
  q70 : WsL → Eqn
  q70 c4 = eqn (Sw12 ∷ Bx3-210 ∷ []) (Bx3-120 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·210⟩ c4)

-- nat 1 BOX(2;3410): 8 steps
lem-nat-1-BOX⟨2·3410⟩ : WsL → ⟪ (Sw12 ∷ Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3420 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·3410⟩ c4 = derive (Sw12 ∷ Bx2-3410 ∷ []) (Bx1-3420 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-210 ∷ Toff234 ∷ CCZ234 ∷ Bx3-210 ∷ []) ∷
   rw⁻ 0 (q68 c4) ∷
   rw 1 (q69 c4) ∷
   rw 2 (q70 c4) ∷
   rw 3 (q69 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   rw 5 (q70 c4) ∷
   re 0 6 (Bx1-3420 ∷ []) ∷ []) Eq.refl

private
  q71 : WsL → Eqn
  q71 c4 = eqn (Sw01 ∷ Bx0-31 ∷ []) (Bx1-30 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·31⟩ c4)

-- nat 0 BOX(3;021): 8 steps
lem-nat-0-BOX⟨3·021⟩ : WsL → ⟪ (Sw01 ∷ Bx3-021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-120 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·021⟩ c4 = derive (Sw01 ∷ Bx3-021 ∷ []) (Bx3-120 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) ∷
   rw⁻ 0 (q47 c4) ∷
   rw 1 (q54 c4) ∷
   rw 2 (q71 c4) ∷
   rw 3 (q54 c4) ∷
   rw⁻ 4 (q47 c4) ∷
   rw 5 (q71 c4) ∷
   re 0 6 (Bx3-120 ∷ []) ∷ []) Eq.refl

private
  q72 : WsL → Eqn
  q72 c4 = eqn (Sw01 ∷ CCZ034 ∷ []) (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4)
  q73 : WsL → Eqn
  q73 c4 = eqn (Sw01 ∷ Toff034 ∷ []) (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4)
  q74 : WsL → Eqn
  q74 c4 = eqn (Sw01 ∷ Bx3-021 ∷ []) (Bx3-120 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·021⟩ c4)

-- nat 0 BOX(0;3421): 8 steps
lem-nat-0-BOX⟨0·3421⟩ : WsL → ⟪ (Sw01 ∷ Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3420 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·3421⟩ c4 = derive (Sw01 ∷ Bx0-3421 ∷ []) (Bx1-3420 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) ∷
   rw 0 (q72 c4) ∷
   rw 1 (q73 c4) ∷
   rw 2 (q74 c4) ∷
   rw 3 (q73 c4) ∷
   rw 4 (q72 c4) ∷
   rw 5 (q74 c4) ∷
   re 0 6 (Bx1-3420 ∷ []) ∷ []) Eq.refl

private
  q75 : WsL → Eqn
  q75 c4 = eqn (Sw01 ∷ Bx1-30 ∷ []) (Bx0-31 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·30⟩ c4)

-- nat 0 BOX(3;120): 8 steps
lem-nat-0-BOX⟨3·120⟩ : WsL → ⟪ (Sw01 ∷ Bx3-120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-021 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·120⟩ c4 = derive (Sw01 ∷ Bx3-120 ∷ []) (Bx3-021 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-30 ∷ Toff312 ∷ CCZ123 ∷ Bx1-30 ∷ []) ∷
   rw⁻ 0 (q50 c4) ∷
   rw 1 (q51 c4) ∷
   rw 2 (q75 c4) ∷
   rw 3 (q51 c4) ∷
   rw⁻ 4 (q50 c4) ∷
   rw 5 (q75 c4) ∷
   re 0 6 (Bx3-021 ∷ []) ∷ []) Eq.refl

private
  q76 : WsL → Eqn
  q76 c4 = eqn (Sw01 ∷ CCZ134 ∷ []) (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4)
  q77 : WsL → Eqn
  q77 c4 = eqn (Sw01 ∷ Toff134 ∷ []) (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4)
  q78 : WsL → Eqn
  q78 c4 = eqn (Sw01 ∷ Bx3-120 ∷ []) (Bx3-021 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·120⟩ c4)

-- nat 0 BOX(1;3420): 8 steps
lem-nat-0-BOX⟨1·3420⟩ : WsL → ⟪ (Sw01 ∷ Bx1-3420 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·3420⟩ c4 = derive (Sw01 ∷ Bx1-3420 ∷ []) (Bx0-3421 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff134 ∷ Bx3-120 ∷ Toff134 ∷ CCZ134 ∷ Bx3-120 ∷ []) ∷
   rw 0 (q76 c4) ∷
   rw 1 (q77 c4) ∷
   rw 2 (q78 c4) ∷
   rw 3 (q77 c4) ∷
   rw 4 (q76 c4) ∷
   rw 5 (q78 c4) ∷
   re 0 6 (Bx0-3421 ∷ []) ∷ []) Eq.refl

private
  q79 : WsL → Eqn
  q79 c4 = eqn (Sw12 ∷ Toff302 ∷ []) (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4)
  q80 : WsL → Eqn
  q80 c4 = eqn (Sw12 ∷ Bx0-31 ∷ []) (Bx0-32 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·31⟩ c4)

-- nat 1 BOX(3;021): 8 steps
lem-nat-1-BOX⟨3·021⟩ : WsL → ⟪ (Sw12 ∷ Bx3-021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-012 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·021⟩ c4 = derive (Sw12 ∷ Bx3-021 ∷ []) (Bx3-012 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) ∷
   rw 0 (q56 c4) ∷
   rw 1 (q79 c4) ∷
   rw 2 (q80 c4) ∷
   rw 3 (q79 c4) ∷
   rw 4 (q56 c4) ∷
   rw 5 (q80 c4) ∷
   re 0 6 (Bx3-012 ∷ []) ∷ []) Eq.refl

private
  q81 : WsL → Eqn
  q81 c4 = eqn (Sw12 ∷ Bx3-021 ∷ []) (Bx3-012 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·021⟩ c4)

-- nat 1 BOX(0;3421): 8 steps
lem-nat-1-BOX⟨0·3421⟩ : WsL → ⟪ (Sw12 ∷ Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·3421⟩ c4 = derive (Sw12 ∷ Bx0-3421 ∷ []) (Bx0-3412 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) ∷
   rw 0 (q2 c4) ∷
   rw 1 (q21 c4) ∷
   rw 2 (q81 c4) ∷
   rw 3 (q21 c4) ∷
   rw 4 (q2 c4) ∷
   rw 5 (q81 c4) ∷
   re 0 6 (Bx0-3412 ∷ []) ∷ []) Eq.refl

private
  q82 : WsL → Eqn
  q82 c4 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wl0138 c4)

-- nat 0 SBOX(1;0;2;3): 3 steps
lem-nat-0-SBOX⟨1·0·2·3⟩ : WsL → ⟪ (Sw01 ∷ Sb1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-2-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·0·2·3⟩ c4 = derive (Sw01 ∷ Sb1-0-2-3 ∷ []) (Sb0-1-2-3 ∷ Sw01 ∷ [])
  (re 1 1 (CS02 ∷ []) ∷
   rw⁻ 0 (q82 c4) ∷
   re 0 1 (Sb0-1-2-3 ∷ []) ∷ []) Eq.refl

private
  q83 : WsL → Eqn
  q83 c4 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wl0139 c4)

-- nat 0 SBOXd(1;0;2;3): 3 steps
lem-nat-0-SBOXd⟨1·0·2·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻1-0-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-2-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·0·2·3⟩ c4 = derive (Sw01 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻0-1-2-3 ∷ Sw01 ∷ [])
  (re 1 1 (CS02⁻ ∷ []) ∷
   rw⁻ 0 (q83 c4) ∷
   re 0 1 (Sb⁻0-1-2-3 ∷ []) ∷ []) Eq.refl

private
  q84 : WsL → Eqn
  q84 c4 = eqn (Sw01 ∷ Bx1-0432 ∷ []) (Bx0-1432 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·0432⟩ c4)
  q85 : WsL → Eqn
  q85 c4 = eqn (Sw01 ∷ Toff234 ∷ []) (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff))
  q86 : WsL → Eqn
  q86 c4 = eqn (Sw01 ∷ Sb1-0-2-3 ∷ []) (Sb0-1-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·2·3⟩ c4)
  q87 : WsL → Eqn
  q87 c4 = eqn (Sw01 ∷ Sb⁻1-0-2-3 ∷ []) (Sb⁻0-1-2-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·0·2·3⟩ c4)

-- nat 0 SBOX(1;0;43;2): 7 steps
lem-nat-0-SBOX⟨1·0·43·2⟩ : WsL → ⟪ (Sw01 ∷ Sb1-0-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·0·43·2⟩ c4 = derive (Sw01 ∷ Sb1-0-43-2 ∷ []) (Sb0-1-43-2 ∷ Sw01 ∷ [])
  (re 1 1 (Bx1-0432 ∷ Toff234 ∷ Sb1-0-2-3 ∷ Toff234 ∷ Sb⁻1-0-2-3 ∷ []) ∷
   rw 0 (q84 c4) ∷
   rw 1 (q85 c4) ∷
   rw 2 (q86 c4) ∷
   rw 3 (q85 c4) ∷
   rw 4 (q87 c4) ∷
   re 0 5 (Sb0-1-43-2 ∷ []) ∷ []) Eq.refl

private
  q88 : WsL → Eqn
  q88 c4 = eqn (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ []) (wl0057 c4)
  q89 : WsL → Eqn
  q89 c4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap))
  q90 : WsL → Eqn
  q90 c4 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (c₁ (iI) (Swap ↑))
  q91 : WsL → Eqn
  q91 c4 = eqn (K4 ∷ Sw34 ∷ []) (Sw34 ∷ K3 ∷ []) (wl0067 c4)
  q92 : WsL → Eqn
  q92 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 c4)
  q93 : WsL → Eqn
  q93 c4 = eqn (CX01 ∷ Sw34 ∷ []) (Sw34 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap ↑))
  q94 : WsL → Eqn
  q94 c4 = eqn (ι ∷ Sw34 ∷ []) (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑))
  q95 : WsL → Eqn
  q95 c4 = eqn (Sw12 ∷ K4 ∷ []) (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑))
  q96 : WsL → Eqn
  q96 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0008 c4)
  q97 : WsL → Eqn
  q97 c4 = eqn (CS24⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS14⁻ ∷ []) (wl0009 c4)
  q98 : WsL → Eqn
  q98 c4 = eqn (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) (wl0010 c4)
  q99 : WsL → Eqn
  q99 c4 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap))
  q100 : WsL → Eqn
  q100 c4 = eqn (Sw23 ∷ K4 ∷ []) (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K))
  q101 : WsL → Eqn
  q101 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl0011 c4)
  q102 : WsL → Eqn
  q102 c4 = eqn (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) (wl0012 c4)
  q103 : WsL → Eqn
  q103 c4 = eqn (CS01 ∷ Sw34 ∷ []) (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑))
  q104 : WsL → Eqn
  q104 c4 = eqn (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) (wl0014 c4)
  q105 : WsL → Eqn
  q105 c4 = eqn (Sw12 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS))
  q106 : WsL → Eqn
  q106 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q107 : WsL → Eqn
  q107 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl0015 c4)
  q108 : WsL → Eqn
  q108 c4 = eqn (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) (wl0016 c4)
  q109 : WsL → Eqn
  q109 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl0017 c4)
  q110 : WsL → Eqn
  q110 c4 = eqn (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ []) (wl0018 c4)
  q111 : WsL → Eqn
  q111 c4 = eqn (K3 ∷ Sw34 ∷ []) (Sw34 ∷ K4 ∷ []) (wl0068 c4)
  q112 : WsL → Eqn
  q112 c4 = eqn (K2 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ []) (wl0058 c4)
  q113 : WsL → Eqn
  q113 c4 = eqn (Sw01 ∷ ι ∷ []) (ι ∷ Sw01 ∷ []) (wl0030 c4)
  q114 : WsL → Eqn
  q114 c4 = eqn (Sw01 ∷ K4 ∷ []) (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑))
  q115 : WsL → Eqn
  q115 c4 = eqn (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) (wl0019 c4)
  q116 : WsL → Eqn
  q116 c4 = eqn (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) (wl0020 c4)
  q117 : WsL → Eqn
  q117 c4 = eqn (Sw01 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑))
  q118 : WsL → Eqn
  q118 c4 = eqn (Sw01 ∷ CS34 ∷ []) (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))
  q119 : WsL → Eqn
  q119 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl0021 c4)
  q120 : WsL → Eqn
  q120 c4 = eqn (CX12 ∷ Sw34 ∷ []) (Sw34 ∷ CX12 ∷ []) (c₃ (CX₀₁ ↑) (Swap))
  q121 : WsL → Eqn
  q121 c4 = eqn (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (wl0082 c4)

-- resp TOFF403 at 2: 236 steps
lem-resp-TOFF403-at-2 : WsL → ⟪ (Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff413 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF403-at-2 c4 = derive (Toff403 ∷ []) (Sw12 ∷ Sw01 ∷ Toff413 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q36 c4) ∷
   re 0 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) ∷
   re 1 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 4 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw⁻ 3 (q88 c4) ∷
   rw⁻ 6 (q32 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q89 c4) ∷
   rw⁻ 8 (q32 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q89 c4) ∷
   rw⁻ 10 (q32 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 (q88 c4) ∷
   rw⁻ 10 (q90 c4) ∷
   rw 11 (q32 c4) ∷
   rw⁻ 2 (q91 c4) ∷
   rw⁻ 5 (q92 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q93 c4) ∷
   rw⁻ 7 (q92 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q93 c4) ∷
   rw⁻ 9 (q92 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q91 c4) ∷
   rw⁻ 9 (q94 c4) ∷
   rw 10 (q92 c4) ∷
   rw 1 (q95 c4) ∷
   rw⁻ 2 (q96 c4) ∷
   rw⁻ 5 (q36 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q97 c4) ∷
   rw⁻ 7 (q36 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q34 c4) ∷
   rw⁻ 7 (q98 c4) ∷
   rw 8 (q34 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw 7 (q95 c4) ∷
   rw⁻ 8 (q99 c4) ∷
   rw 9 (q36 c4) ∷
   rw 0 (q100 c4) ∷
   rw⁻ 1 (q101 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   re 2 3 (CX03 ∷ []) ∷
   rw⁻ 3 (q102 c4) ∷
   rw⁻ 6 (q32 c4) ∷
   re 4 3 (CX03 ∷ []) ∷
   re 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q33 c4) ∷
   rw⁻ 7 (q34 c4) ∷
   rw⁻ 8 (q103 c4) ∷
   rw⁻ 9 (q34 c4) ∷
   rw⁻ 10 (q33 c4) ∷
   re 5 7 (CS04 ∷ []) ∷
   rw 6 (q100 c4) ∷
   rw⁻ 7 (q90 c4) ∷
   rw 8 (q32 c4) ∷
   rw 7 (q99 c4) ∷
   rw⁻ 6 (q95 c4) ∷
   re 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 7 (q34 c4) ∷
   rw 6 (q98 c4) ∷
   rw⁻ 5 (q34 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw 4 (q104 c4) ∷
   rw⁻ 3 (q105 c4) ∷
   rw 2 (q104 c4) ∷
   rw⁻ 1 (q106 c4) ∷
   rw⁻ 0 (q95 c4) ∷
   rw⁻ 1 (q32 c4) ∷
   rw 2 (q100 c4) ∷
   rw⁻ 3 (q107 c4) ∷
   re 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 4 (q32 c4) ∷
   rw⁻ 5 (q108 c4) ∷
   re 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 6 (q32 c4) ∷
   re 8 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 7 (q33 c4) ∷
   rw⁻ 9 (q34 c4) ∷
   rw⁻ 10 (q103 c4) ∷
   rw⁻ 11 (q34 c4) ∷
   rw⁻ 12 (q33 c4) ∷
   re 7 7 (CS04 ∷ []) ∷
   rw 8 (q100 c4) ∷
   rw⁻ 9 (q90 c4) ∷
   rw⁻ 2 (q36 c4) ∷
   rw 3 (q95 c4) ∷
   rw⁻ 4 (q109 c4) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 (q36 c4) ∷
   rw⁻ 6 (q110 c4) ∷
   re 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 7 (q36 c4) ∷
   re 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 8 (q34 c4) ∷
   rw⁻ 9 (q98 c4) ∷
   rw 10 (q34 c4) ∷
   re 8 3 (CS04 ∷ []) ∷
   rw 9 (q95 c4) ∷
   rw⁻ 10 (q99 c4) ∷
   rw⁻ 3 (q92 c4) ∷
   rw⁻ 4 (q111 c4) ∷
   re 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 5 (q92 c4) ∷
   rw⁻ 6 (q93 c4) ∷
   re 8 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 7 (q92 c4) ∷
   rw⁻ 8 (q93 c4) ∷
   re 10 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 9 (q92 c4) ∷
   rw⁻ 10 (q111 c4) ∷
   rw⁻ 11 (q94 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   rw⁻ 5 (q112 c4) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 (q32 c4) ∷
   rw⁻ 7 (q89 c4) ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 (q32 c4) ∷
   rw⁻ 9 (q89 c4) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 (q32 c4) ∷
   rw⁻ 11 (q112 c4) ∷
   rw⁻ 12 (q90 c4) ∷
   re 5 8 (Toff201 ∷ []) ∷
   re 4 3 (Toff301 ∷ []) ∷
   re 3 3 (Toff401 ∷ []) ∷
   re 2 3 (Toff402 ∷ []) ∷
   re 1 3 (Toff403 ∷ []) ∷
   rw⁻ 2 (q38 c4) ∷
   re 1 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) ∷
   re 3 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) ∷
   re 4 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 5 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw⁻ 4 (q88 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 (q89 c4) ∷
   rw⁻ 9 (q32 c4) ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 (q89 c4) ∷
   rw⁻ 11 (q32 c4) ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 (q88 c4) ∷
   rw⁻ 11 (q90 c4) ∷
   rw 12 (q32 c4) ∷
   rw⁻ 3 (q91 c4) ∷
   rw⁻ 6 (q92 c4) ∷
   re 4 3 (CS14 ∷ []) ∷
   rw⁻ 5 (q93 c4) ∷
   rw⁻ 8 (q92 c4) ∷
   re 6 3 (CS14⁻ ∷ []) ∷
   rw⁻ 7 (q93 c4) ∷
   rw⁻ 10 (q92 c4) ∷
   re 8 3 (CS04 ∷ []) ∷
   rw⁻ 9 (q91 c4) ∷
   rw⁻ 10 (q94 c4) ∷
   rw 11 (q92 c4) ∷
   rw 2 (q95 c4) ∷
   rw⁻ 3 (q96 c4) ∷
   rw⁻ 6 (q36 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw⁻ 5 (q97 c4) ∷
   rw⁻ 8 (q36 c4) ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q34 c4) ∷
   rw⁻ 8 (q98 c4) ∷
   rw 9 (q34 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw 8 (q95 c4) ∷
   rw⁻ 9 (q99 c4) ∷
   rw 10 (q36 c4) ∷
   rw 1 (q100 c4) ∷
   rw⁻ 2 (q101 c4) ∷
   rw⁻ 5 (q32 c4) ∷
   re 3 3 (CX03 ∷ []) ∷
   rw⁻ 4 (q102 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   re 5 3 (CX03 ∷ []) ∷
   re 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 6 (q33 c4) ∷
   rw⁻ 8 (q34 c4) ∷
   rw⁻ 9 (q103 c4) ∷
   rw⁻ 10 (q34 c4) ∷
   rw⁻ 11 (q33 c4) ∷
   re 6 7 (CS04 ∷ []) ∷
   rw 7 (q100 c4) ∷
   rw⁻ 8 (q90 c4) ∷
   rw 9 (q32 c4) ∷
   rw⁻ 8 (q113 c4) ∷
   rw⁻ 7 (q114 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q39 c4) ∷
   rw 7 (q115 c4) ∷
   rw⁻ 6 (q39 c4) ∷
   re 7 3 (CS14 ∷ []) ∷
   rw 5 (q116 c4) ∷
   rw⁻ 4 (q117 c4) ∷
   rw 3 (q116 c4) ∷
   rw⁻ 2 (q118 c4) ∷
   rw⁻ 1 (q114 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 3 (q100 c4) ∷
   rw⁻ 4 (q107 c4) ∷
   re 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 5 (q32 c4) ∷
   rw⁻ 6 (q108 c4) ∷
   re 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 7 (q32 c4) ∷
   rw⁻ 8 (q119 c4) ∷
   rw 9 (q100 c4) ∷
   rw⁻ 10 (q90 c4) ∷
   rw⁻ 3 (q92 c4) ∷
   rw⁻ 4 (q111 c4) ∷
   re 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 5 (q92 c4) ∷
   rw⁻ 6 (q120 c4) ∷
   re 8 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 7 (q92 c4) ∷
   rw⁻ 8 (q120 c4) ∷
   re 10 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 9 (q92 c4) ∷
   rw⁻ 10 (q111 c4) ∷
   rw⁻ 11 (q94 c4) ∷
   rw 4 (q121 c4) ∷
   re 4 8 (Toff312 ∷ []) ∷
   re 3 3 (Toff412 ∷ []) ∷
   re 2 3 (Toff413 ∷ []) ∷ []) Eq.refl

-- nat 1 CK20: 2 steps
lem-nat-1-CK20 : WsL → ⟪ (Sw12 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CK20 c4 = derive (Sw12 ∷ CK20 ∷ []) (CK10 ∷ Sw12 ∷ [])
  (re 1 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 0 (q36 c4) ∷ []) Eq.refl

-- nat 1 CK10: 2 steps
lem-nat-1-CK10 : WsL → ⟪ (Sw12 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CK10 c4 = derive (Sw12 ∷ CK10 ∷ []) (CK20 ∷ Sw12 ∷ [])
  (rw⁻ 2 (q36 c4) ∷
   re 0 3 (CK20 ∷ []) ∷ []) Eq.refl

-- nat 2 CK30: 2 steps
lem-nat-2-CK30 : WsL → ⟪ (Sw23 ∷ CK30 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CK30 c4 = derive (Sw23 ∷ CK30 ∷ []) (CK20 ∷ Sw23 ∷ [])
  (re 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 0 (q32 c4) ∷ []) Eq.refl

-- nat 2 CK20: 2 steps
lem-nat-2-CK20 : WsL → ⟪ (Sw23 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (CK30 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CK20 c4 = derive (Sw23 ∷ CK20 ∷ []) (CK30 ∷ Sw23 ∷ [])
  (rw⁻ 2 (q32 c4) ∷
   re 0 3 (CK30 ∷ []) ∷ []) Eq.refl

-- nat 3 CK40: 2 steps
lem-nat-3-CK40 : WsL → ⟪ (Sw34 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK30 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CK40 c4 = derive (Sw34 ∷ CK40 ∷ []) (CK30 ∷ Sw34 ∷ [])
  (re 1 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 0 (q92 c4) ∷ []) Eq.refl

-- nat 3 CK30: 2 steps
lem-nat-3-CK30 : WsL → ⟪ (Sw34 ∷ CK30 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CK30 c4 = derive (Sw34 ∷ CK30 ∷ []) (CK40 ∷ Sw34 ∷ [])
  (rw⁻ 2 (q92 c4) ∷
   re 0 3 (CK40 ∷ []) ∷ []) Eq.refl

private
  q122 : WsL → Eqn
  q122 c4 = eqn (CK10 ∷ Sw34 ∷ []) (Sw34 ∷ CK10 ∷ []) (c₂ (CK₁₀) (Swap ↑))

-- nat 2 CK40: 7 steps
lem-nat-2-CK40 : WsL → ⟪ (Sw23 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CK40 c4 = derive (Sw23 ∷ CK40 ∷ []) (CK40 ∷ Sw23 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 0 (q33 c4) ∷
   rw⁻ 2 (q34 c4) ∷
   rw⁻ 3 (q122 c4) ∷
   rw⁻ 4 (q34 c4) ∷
   rw⁻ 5 (q33 c4) ∷
   re 0 7 (CK40 ∷ []) ∷ []) Eq.refl

private
  q123 : WsL → Eqn
  q123 c4 = eqn (CK30 ∷ Sw12 ∷ []) (Sw12 ∷ CK30 ∷ []) (wl0159 c4)

-- nat 1 CK40: 5 steps
lem-nat-1-CK40 : WsL → ⟪ (Sw12 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CK40 c4 = derive (Sw12 ∷ CK40 ∷ []) (CK40 ∷ Sw12 ∷ [])
  (re 1 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 0 (q34 c4) ∷
   rw⁻ 1 (q123 c4) ∷
   rw 2 (q34 c4) ∷
   re 0 3 (CK40 ∷ []) ∷ []) Eq.refl

private
  q124 : WsL → Eqn
  q124 c4 = eqn (CK30 ∷ Sw01 ∷ []) (Sw01 ∷ CK31 ∷ []) (wl0117 c4)

-- nat 0 CK41: 5 steps
lem-nat-0-CK41 : WsL → ⟪ (Sw01 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CK41 c4 = derive (Sw01 ∷ CK41 ∷ []) (CK40 ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ CK31 ∷ Sw34 ∷ []) ∷
   rw 0 (q39 c4) ∷
   rw⁻ 1 (q124 c4) ∷
   rw 2 (q39 c4) ∷
   re 0 3 (CK40 ∷ []) ∷ []) Eq.refl

private
  q125 : WsL → Eqn
  q125 c4 = eqn (CK31 ∷ Sw01 ∷ []) (Sw01 ∷ CK30 ∷ []) (wl0161 c4)

-- nat 0 CK40: 5 steps
lem-nat-0-CK40 : WsL → ⟪ (Sw01 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CK40 c4 = derive (Sw01 ∷ CK40 ∷ []) (CK41 ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw 0 (q39 c4) ∷
   rw⁻ 1 (q125 c4) ∷
   rw 2 (q39 c4) ∷
   re 0 3 (CK41 ∷ []) ∷ []) Eq.refl

private
  q126 : WsL → Eqn
  q126 c4 = eqn (Sw23 ∷ CZ13 ∷ []) (CZ12 ∷ Sw23 ∷ []) (lem-nat-2-CZ13 c4)

-- nat 2 BOX(0;31): 3 steps
lem-nat-2-BOX⟨0·31⟩ : WsL → ⟪ (Sw23 ∷ Bx0-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-21 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·31⟩ c4 = derive (Sw23 ∷ Bx0-31 ∷ []) (Bx0-21 ∷ Sw23 ∷ [])
  (re 1 1 (CZ13 ∷ []) ∷
   rw 0 (q126 c4) ∷
   re 0 1 (Bx0-21 ∷ []) ∷ []) Eq.refl

private
  q127 : WsL → Eqn
  q127 c4 = eqn (Sw23 ∷ Toff304 ∷ []) (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4)
  q128 : WsL → Eqn
  q128 c4 = eqn (Sw23 ∷ Bx0-31 ∷ []) (Bx0-21 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·31⟩ c4)

-- nat 2 BOX(3;041): 8 steps
lem-nat-2-BOX⟨3·041⟩ : WsL → ⟪ (Sw23 ∷ Bx3-041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-041 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·041⟩ c4 = derive (Sw23 ∷ Bx3-041 ∷ []) (Bx2-041 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) ∷
   rw 0 (q24 c4) ∷
   rw 1 (q127 c4) ∷
   rw 2 (q128 c4) ∷
   rw 3 (q127 c4) ∷
   rw 4 (q24 c4) ∷
   rw 5 (q128 c4) ∷
   re 0 6 (Bx2-041 ∷ []) ∷ []) Eq.refl

private
  q129 : WsL → Eqn
  q129 c4 = eqn (CCZ023 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ023 ∷ []) (wl0065 c4)
  q130 : WsL → Eqn
  q130 c4 = eqn (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) (wl0093 c4)
  q131 : WsL → Eqn
  q131 c4 = eqn (Sw23 ∷ Bx3-041 ∷ []) (Bx2-041 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·041⟩ c4)

-- nat 2 BOX(0;3241): 8 steps
lem-nat-2-BOX⟨0·3241⟩ : WsL → ⟪ (Sw23 ∷ Bx0-3241 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·3241⟩ c4 = derive (Sw23 ∷ Bx0-3241 ∷ []) (Bx0-2341 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-041 ∷ Toff023 ∷ CCZ023 ∷ Bx3-041 ∷ []) ∷
   rw⁻ 0 (q129 c4) ∷
   rw 1 (q130 c4) ∷
   rw 2 (q131 c4) ∷
   rw 3 (q130 c4) ∷
   rw⁻ 4 (q129 c4) ∷
   rw 5 (q131 c4) ∷
   re 0 6 (Bx0-2341 ∷ []) ∷ []) Eq.refl

private
  q132 : WsL → Eqn
  q132 c4 = eqn (Sw23 ∷ CS13 ∷ []) (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 c4)

-- nat 2 SBOX(0;3;1;4): 3 steps
lem-nat-2-SBOX⟨0·3·1·4⟩ : WsL → ⟪ (Sw23 ∷ Sb0-3-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·3·1·4⟩ c4 = derive (Sw23 ∷ Sb0-3-1-4 ∷ []) (Sb0-2-1-4 ∷ Sw23 ∷ [])
  (re 1 1 (CS13 ∷ []) ∷
   rw 0 (q132 c4) ∷
   re 0 1 (Sb0-2-1-4 ∷ []) ∷ []) Eq.refl

private
  q133 : WsL → Eqn
  q133 c4 = eqn (Sw23 ∷ CS13⁻ ∷ []) (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 c4)

-- nat 2 SBOXd(0;3;1;4): 3 steps
lem-nat-2-SBOXd⟨0·3·1·4⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻0-3-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·3·1·4⟩ c4 = derive (Sw23 ∷ Sb⁻0-3-1-4 ∷ []) (Sb⁻0-2-1-4 ∷ Sw23 ∷ [])
  (re 1 1 (CS13⁻ ∷ []) ∷
   rw 0 (q133 c4) ∷
   re 0 1 (Sb⁻0-2-1-4 ∷ []) ∷ []) Eq.refl

private
  q134 : WsL → Eqn
  q134 c4 = eqn (Sw23 ∷ Bx0-3241 ∷ []) (Bx0-2341 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·3241⟩ c4)
  q135 : WsL → Eqn
  q135 c4 = eqn (Sw23 ∷ Toff124 ∷ []) (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4)
  q136 : WsL → Eqn
  q136 c4 = eqn (Sw23 ∷ Sb0-3-1-4 ∷ []) (Sb0-2-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·3·1·4⟩ c4)
  q137 : WsL → Eqn
  q137 c4 = eqn (Sw23 ∷ Sb⁻0-3-1-4 ∷ []) (Sb⁻0-2-1-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·3·1·4⟩ c4)

-- nat 2 SBOX(0;3;24;1): 7 steps
lem-nat-2-SBOX⟨0·3·24·1⟩ : WsL → ⟪ (Sw23 ∷ Sb0-3-24-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-34-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·3·24·1⟩ c4 = derive (Sw23 ∷ Sb0-3-24-1 ∷ []) (Sb0-2-34-1 ∷ Sw23 ∷ [])
  (re 1 1 (Bx0-3241 ∷ Toff124 ∷ Sb0-3-1-4 ∷ Toff124 ∷ Sb⁻0-3-1-4 ∷ []) ∷
   rw 0 (q134 c4) ∷
   rw 1 (q135 c4) ∷
   rw 2 (q136 c4) ∷
   rw 3 (q135 c4) ∷
   rw 4 (q137 c4) ∷
   re 0 5 (Sb0-2-34-1 ∷ []) ∷ []) Eq.refl

private
  q138 : WsL → Eqn
  q138 c4 = eqn (CS13 ∷ Sw01 ∷ []) (Sw01 ∷ CS03 ∷ []) (wl0061 c4)

-- nat 0 SBOX(1;3;0;4): 3 steps
lem-nat-0-SBOX⟨1·3·0·4⟩ : WsL → ⟪ (Sw01 ∷ Sb1-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-1-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·3·0·4⟩ c4 = derive (Sw01 ∷ Sb1-3-0-4 ∷ []) (Sb0-3-1-4 ∷ Sw01 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   rw⁻ 0 (q138 c4) ∷
   re 0 1 (Sb0-3-1-4 ∷ []) ∷ []) Eq.refl

private
  q139 : WsL → Eqn
  q139 c4 = eqn (CS13⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS03⁻ ∷ []) (wl0121 c4)

-- nat 0 SBOXd(1;3;0;4): 3 steps
lem-nat-0-SBOXd⟨1·3·0·4⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻1-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-1-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·3·0·4⟩ c4 = derive (Sw01 ∷ Sb⁻1-3-0-4 ∷ []) (Sb⁻0-3-1-4 ∷ Sw01 ∷ [])
  (re 1 1 (CS03⁻ ∷ []) ∷
   rw⁻ 0 (q139 c4) ∷
   re 0 1 (Sb⁻0-3-1-4 ∷ []) ∷ []) Eq.refl

private
  q140 : WsL → Eqn
  q140 c4 = eqn (Sw01 ∷ Bx1-3240 ∷ []) (Bx0-3241 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·3240⟩ c4)
  q141 : WsL → Eqn
  q141 c4 = eqn (Sw01 ∷ Toff024 ∷ []) (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4)
  q142 : WsL → Eqn
  q142 c4 = eqn (Sw01 ∷ Sb1-3-0-4 ∷ []) (Sb0-3-1-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·3·0·4⟩ c4)
  q143 : WsL → Eqn
  q143 c4 = eqn (Sw01 ∷ Sb⁻1-3-0-4 ∷ []) (Sb⁻0-3-1-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·3·0·4⟩ c4)

-- nat 0 SBOX(1;3;24;0): 7 steps
lem-nat-0-SBOX⟨1·3·24·0⟩ : WsL → ⟪ (Sw01 ∷ Sb1-3-24-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-24-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·3·24·0⟩ c4 = derive (Sw01 ∷ Sb1-3-24-0 ∷ []) (Sb0-3-24-1 ∷ Sw01 ∷ [])
  (re 1 1 (Bx1-3240 ∷ Toff024 ∷ Sb1-3-0-4 ∷ Toff024 ∷ Sb⁻1-3-0-4 ∷ []) ∷
   rw 0 (q140 c4) ∷
   rw 1 (q141 c4) ∷
   rw 2 (q142 c4) ∷
   rw 3 (q141 c4) ∷
   rw 4 (q143 c4) ∷
   re 0 5 (Sb0-3-24-1 ∷ []) ∷ []) Eq.refl

private
  q144 : WsL → Eqn
  q144 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl0025 c4)

-- nat 1 SBOX(0;3;1;4): 3 steps
lem-nat-1-SBOX⟨0·3·1·4⟩ : WsL → ⟪ (Sw12 ∷ Sb0-3-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-2-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·3·1·4⟩ c4 = derive (Sw12 ∷ Sb0-3-1-4 ∷ []) (Sb0-3-2-4 ∷ Sw12 ∷ [])
  (re 1 1 (CS13 ∷ []) ∷
   rw⁻ 0 (q144 c4) ∷
   re 0 1 (Sb0-3-2-4 ∷ []) ∷ []) Eq.refl

private
  q145 : WsL → Eqn
  q145 c4 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wl0046 c4)

-- nat 1 SBOXd(0;3;1;4): 3 steps
lem-nat-1-SBOXd⟨0·3·1·4⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻0-3-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-2-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·3·1·4⟩ c4 = derive (Sw12 ∷ Sb⁻0-3-1-4 ∷ []) (Sb⁻0-3-2-4 ∷ Sw12 ∷ [])
  (re 1 1 (CS13⁻ ∷ []) ∷
   rw⁻ 0 (q145 c4) ∷
   re 0 1 (Sb⁻0-3-2-4 ∷ []) ∷ []) Eq.refl

private
  q146 : WsL → Eqn
  q146 c4 = eqn (Sw12 ∷ Bx0-3241 ∷ []) (Bx0-3142 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·3241⟩ c4)
  q147 : WsL → Eqn
  q147 c4 = eqn (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) (wl0095 c4)
  q148 : WsL → Eqn
  q148 c4 = eqn (Sw12 ∷ Sb0-3-1-4 ∷ []) (Sb0-3-2-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·3·1·4⟩ c4)
  q149 : WsL → Eqn
  q149 c4 = eqn (Sw12 ∷ Sb⁻0-3-1-4 ∷ []) (Sb⁻0-3-2-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·3·1·4⟩ c4)

-- nat 1 SBOX(0;3;24;1): 7 steps
lem-nat-1-SBOX⟨0·3·24·1⟩ : WsL → ⟪ (Sw12 ∷ Sb0-3-24-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-14-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·3·24·1⟩ c4 = derive (Sw12 ∷ Sb0-3-24-1 ∷ []) (Sb0-3-14-2 ∷ Sw12 ∷ [])
  (re 1 1 (Bx0-3241 ∷ Toff124 ∷ Sb0-3-1-4 ∷ Toff124 ∷ Sb⁻0-3-1-4 ∷ []) ∷
   rw 0 (q146 c4) ∷
   rw 1 (q147 c4) ∷
   rw 2 (q148 c4) ∷
   rw 3 (q147 c4) ∷
   rw 4 (q149 c4) ∷
   re 0 5 (Sb0-3-14-2 ∷ []) ∷ []) Eq.refl

private
  q150 : WsL → Eqn
  q150 c4 = eqn (Sw01 ∷ Sb0-3-2-4 ∷ []) (Sb0-3-2-4 ∷ Sw01 ∷ []) (c₂ (Swap) (CS))

-- nat 0 SBOX(0;3;2;4): 2 steps
lem-nat-0-SBOX⟨0·3·2·4⟩ : WsL → ⟪ (Sw01 ∷ Sb0-3-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-2-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·3·2·4⟩ c4 = derive (Sw01 ∷ Sb0-3-2-4 ∷ []) (Sb1-3-2-4 ∷ Sw01 ∷ [])
  (rw 0 (q150 c4) ∷
   re 0 1 (Sb1-3-2-4 ∷ []) ∷ []) Eq.refl

private
  q151 : WsL → Eqn
  q151 c4 = eqn (Sw01 ∷ Sb⁻0-3-2-4 ∷ []) (Sb⁻0-3-2-4 ∷ Sw01 ∷ []) (c₂ (Swap) (CS • CS • CS))

-- nat 0 SBOXd(0;3;2;4): 2 steps
lem-nat-0-SBOXd⟨0·3·2·4⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻0-3-2-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-2-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·3·2·4⟩ c4 = derive (Sw01 ∷ Sb⁻0-3-2-4 ∷ []) (Sb⁻1-3-2-4 ∷ Sw01 ∷ [])
  (rw 0 (q151 c4) ∷
   re 0 1 (Sb⁻1-3-2-4 ∷ []) ∷ []) Eq.refl

private
  q152 : WsL → Eqn
  q152 c4 = eqn (Sw01 ∷ Bx0-3142 ∷ []) (Bx1-3042 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·3142⟩ c4)
  q153 : WsL → Eqn
  q153 c4 = eqn (Sw01 ∷ Toff214 ∷ []) (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4)
  q154 : WsL → Eqn
  q154 c4 = eqn (Sw01 ∷ Sb0-3-2-4 ∷ []) (Sb1-3-2-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·3·2·4⟩ c4)
  q155 : WsL → Eqn
  q155 c4 = eqn (Sw01 ∷ Sb⁻0-3-2-4 ∷ []) (Sb⁻1-3-2-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·3·2·4⟩ c4)

-- nat 0 SBOX(0;3;14;2): 7 steps
lem-nat-0-SBOX⟨0·3·14·2⟩ : WsL → ⟪ (Sw01 ∷ Sb0-3-14-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-04-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·3·14·2⟩ c4 = derive (Sw01 ∷ Sb0-3-14-2 ∷ []) (Sb1-3-04-2 ∷ Sw01 ∷ [])
  (re 1 1 (Bx0-3142 ∷ Toff214 ∷ Sb0-3-2-4 ∷ Toff214 ∷ Sb⁻0-3-2-4 ∷ []) ∷
   rw 0 (q152 c4) ∷
   rw 1 (q153 c4) ∷
   rw 2 (q154 c4) ∷
   rw 3 (q153 c4) ∷
   rw 4 (q155 c4) ∷
   re 0 5 (Sb1-3-04-2 ∷ []) ∷ []) Eq.refl

private
  q156 : WsL → Eqn
  q156 c4 = eqn (Sw34 ∷ CCZ124 ∷ []) (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4)
  q157 : WsL → Eqn
  q157 c4 = eqn (Sw34 ∷ Toff214 ∷ []) (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 c4)
  q158 : WsL → Eqn
  q158 c4 = eqn (Sw34 ∷ Bx1-23 ∷ []) (Bx1-24 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·23⟩ c4)

-- nat 3 BOX(2;143): 8 steps
lem-nat-3-BOX⟨2·143⟩ : WsL → ⟪ (Sw34 ∷ Bx2-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-134 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·143⟩ c4 = derive (Sw34 ∷ Bx2-143 ∷ []) (Bx2-134 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-23 ∷ Toff214 ∷ CCZ124 ∷ Bx1-23 ∷ []) ∷
   rw 0 (q156 c4) ∷
   rw 1 (q157 c4) ∷
   rw 2 (q158 c4) ∷
   rw 3 (q157 c4) ∷
   rw 4 (q156 c4) ∷
   rw 5 (q158 c4) ∷
   re 0 6 (Bx2-134 ∷ []) ∷ []) Eq.refl

private
  q159 : WsL → Eqn
  q159 c4 = eqn (CCZ012 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (Swap))
  q160 : WsL → Eqn
  q160 c4 = eqn (Toff102 ∷ Sw34 ∷ []) (Sw34 ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (Swap))
  q161 : WsL → Eqn
  q161 c4 = eqn (Sw34 ∷ Bx2-143 ∷ []) (Bx2-134 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·143⟩ c4)

-- nat 3 BOX(1;2043): 8 steps
lem-nat-3-BOX⟨1·2043⟩ : WsL → ⟪ (Sw34 ∷ Bx1-2043 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2034 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·2043⟩ c4 = derive (Sw34 ∷ Bx1-2043 ∷ []) (Bx1-2034 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-143 ∷ Toff102 ∷ CCZ012 ∷ Bx2-143 ∷ []) ∷
   rw⁻ 0 (q159 c4) ∷
   rw⁻ 1 (q160 c4) ∷
   rw 2 (q161 c4) ∷
   rw⁻ 3 (q160 c4) ∷
   rw⁻ 4 (q159 c4) ∷
   rw 5 (q161 c4) ∷
   re 0 6 (Bx1-2034 ∷ []) ∷ []) Eq.refl

private
  q162 : WsL → Eqn
  q162 c4 = eqn (Sw34 ∷ CCZ123 ∷ []) (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4)
  q163 : WsL → Eqn
  q163 c4 = eqn (Sw34 ∷ Toff213 ∷ []) (Toff214 ∷ Sw34 ∷ []) (lem-nat-3-TOFF213 c4)
  q164 : WsL → Eqn
  q164 c4 = eqn (Sw34 ∷ Bx1-24 ∷ []) (Bx1-23 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·24⟩ c4)

-- nat 3 BOX(2;134): 8 steps
lem-nat-3-BOX⟨2·134⟩ : WsL → ⟪ (Sw34 ∷ Bx2-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-143 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·134⟩ c4 = derive (Sw34 ∷ Bx2-134 ∷ []) (Bx2-143 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-24 ∷ Toff213 ∷ CCZ123 ∷ Bx1-24 ∷ []) ∷
   rw 0 (q162 c4) ∷
   rw 1 (q163 c4) ∷
   rw 2 (q164 c4) ∷
   rw 3 (q163 c4) ∷
   rw 4 (q162 c4) ∷
   rw 5 (q164 c4) ∷
   re 0 6 (Bx2-143 ∷ []) ∷ []) Eq.refl

private
  q165 : WsL → Eqn
  q165 c4 = eqn (Sw34 ∷ Bx2-134 ∷ []) (Bx2-143 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·134⟩ c4)

-- nat 3 BOX(1;2034): 8 steps
lem-nat-3-BOX⟨1·2034⟩ : WsL → ⟪ (Sw34 ∷ Bx1-2034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2043 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·2034⟩ c4 = derive (Sw34 ∷ Bx1-2034 ∷ []) (Bx1-2043 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-134 ∷ Toff102 ∷ CCZ012 ∷ Bx2-134 ∷ []) ∷
   rw⁻ 0 (q159 c4) ∷
   rw⁻ 1 (q160 c4) ∷
   rw 2 (q165 c4) ∷
   rw⁻ 3 (q160 c4) ∷
   rw⁻ 4 (q159 c4) ∷
   rw 5 (q165 c4) ∷
   re 0 6 (Bx1-2043 ∷ []) ∷ []) Eq.refl

private
  q166 : WsL → Eqn
  q166 c4 = eqn (Sw23 ∷ CCZ134 ∷ []) (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4)
  q167 : WsL → Eqn
  q167 c4 = eqn (Sw23 ∷ Toff314 ∷ []) (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4)
  q168 : WsL → Eqn
  q168 c4 = eqn (Sw23 ∷ Bx1-32 ∷ []) (Bx1-23 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·32⟩ c4)

-- nat 2 BOX(3;142): 8 steps
lem-nat-2-BOX⟨3·142⟩ : WsL → ⟪ (Sw23 ∷ Bx3-142 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-143 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·142⟩ c4 = derive (Sw23 ∷ Bx3-142 ∷ []) (Bx2-143 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-32 ∷ Toff314 ∷ CCZ134 ∷ Bx1-32 ∷ []) ∷
   rw 0 (q166 c4) ∷
   rw 1 (q167 c4) ∷
   rw 2 (q168 c4) ∷
   rw 3 (q167 c4) ∷
   rw 4 (q166 c4) ∷
   rw 5 (q168 c4) ∷
   re 0 6 (Bx2-143 ∷ []) ∷ []) Eq.refl

private
  q169 : WsL → Eqn
  q169 c4 = eqn (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4)
  q170 : WsL → Eqn
  q170 c4 = eqn (Sw23 ∷ Toff103 ∷ []) (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4)
  q171 : WsL → Eqn
  q171 c4 = eqn (Sw23 ∷ Bx3-142 ∷ []) (Bx2-143 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·142⟩ c4)

-- nat 2 BOX(1;3042): 8 steps
lem-nat-2-BOX⟨1·3042⟩ : WsL → ⟪ (Sw23 ∷ Bx1-3042 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2043 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·3042⟩ c4 = derive (Sw23 ∷ Bx1-3042 ∷ []) (Bx1-2043 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-142 ∷ Toff103 ∷ CCZ013 ∷ Bx3-142 ∷ []) ∷
   rw 0 (q169 c4) ∷
   rw 1 (q170 c4) ∷
   rw 2 (q171 c4) ∷
   rw 3 (q170 c4) ∷
   rw 4 (q169 c4) ∷
   rw 5 (q171 c4) ∷
   re 0 6 (Bx1-2043 ∷ []) ∷ []) Eq.refl

private
  q172 : WsL → Eqn
  q172 c4 = eqn (Sw23 ∷ CCZ124 ∷ []) (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4)
  q173 : WsL → Eqn
  q173 c4 = eqn (Sw23 ∷ Toff214 ∷ []) (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4)
  q174 : WsL → Eqn
  q174 c4 = eqn (Sw23 ∷ Bx1-23 ∷ []) (Bx1-32 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·23⟩ c4)

-- nat 2 BOX(2;143): 8 steps
lem-nat-2-BOX⟨2·143⟩ : WsL → ⟪ (Sw23 ∷ Bx2-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-142 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·143⟩ c4 = derive (Sw23 ∷ Bx2-143 ∷ []) (Bx3-142 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-23 ∷ Toff214 ∷ CCZ124 ∷ Bx1-23 ∷ []) ∷
   rw 0 (q172 c4) ∷
   rw 1 (q173 c4) ∷
   rw 2 (q174 c4) ∷
   rw 3 (q173 c4) ∷
   rw 4 (q172 c4) ∷
   rw 5 (q174 c4) ∷
   re 0 6 (Bx3-142 ∷ []) ∷ []) Eq.refl

private
  q175 : WsL → Eqn
  q175 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4)
  q176 : WsL → Eqn
  q176 c4 = eqn (Sw23 ∷ Toff102 ∷ []) (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4)
  q177 : WsL → Eqn
  q177 c4 = eqn (Sw23 ∷ Bx2-143 ∷ []) (Bx3-142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·143⟩ c4)

-- nat 2 BOX(1;2043): 8 steps
lem-nat-2-BOX⟨1·2043⟩ : WsL → ⟪ (Sw23 ∷ Bx1-2043 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3042 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·2043⟩ c4 = derive (Sw23 ∷ Bx1-2043 ∷ []) (Bx1-3042 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-143 ∷ Toff102 ∷ CCZ012 ∷ Bx2-143 ∷ []) ∷
   rw 0 (q175 c4) ∷
   rw 1 (q176 c4) ∷
   rw 2 (q177 c4) ∷
   rw 3 (q176 c4) ∷
   rw 4 (q175 c4) ∷
   rw 5 (q177 c4) ∷
   re 0 6 (Bx1-3042 ∷ []) ∷ []) Eq.refl

private
  q178 : WsL → Eqn
  q178 c4 = eqn (Sw23 ∷ CZ12 ∷ []) (CZ13 ∷ Sw23 ∷ []) (lem-nat-2-CZ12 c4)

-- nat 2 BOX(0;21): 3 steps
lem-nat-2-BOX⟨0·21⟩ : WsL → ⟪ (Sw23 ∷ Bx0-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-31 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·21⟩ c4 = derive (Sw23 ∷ Bx0-21 ∷ []) (Bx0-31 ∷ Sw23 ∷ [])
  (re 1 1 (CZ12 ∷ []) ∷
   rw 0 (q178 c4) ∷
   re 0 1 (Bx0-31 ∷ []) ∷ []) Eq.refl

private
  q179 : WsL → Eqn
  q179 c4 = eqn (Sw23 ∷ Toff203 ∷ []) (Toff302 ∷ Sw23 ∷ []) (wl0090 c4)
  q180 : WsL → Eqn
  q180 c4 = eqn (Sw23 ∷ Bx0-21 ∷ []) (Bx0-31 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·21⟩ c4)

-- nat 2 BOX(2;031): 8 steps
lem-nat-2-BOX⟨2·031⟩ : WsL → ⟪ (Sw23 ∷ Bx2-031 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-021 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·031⟩ c4 = derive (Sw23 ∷ Bx2-031 ∷ []) (Bx3-021 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) ∷
   rw⁻ 0 (q129 c4) ∷
   rw 1 (q179 c4) ∷
   rw 2 (q180 c4) ∷
   rw 3 (q179 c4) ∷
   rw⁻ 4 (q129 c4) ∷
   rw 5 (q180 c4) ∷
   re 0 6 (Bx3-021 ∷ []) ∷ []) Eq.refl

private
  q181 : WsL → Eqn
  q181 c4 = eqn (Sw23 ∷ Bx2-031 ∷ []) (Bx3-021 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·031⟩ c4)

-- nat 2 BOX(0;2431): 8 steps
lem-nat-2-BOX⟨0·2431⟩ : WsL → ⟪ (Sw23 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·2431⟩ c4 = derive (Sw23 ∷ Bx0-2431 ∷ []) (Bx0-3421 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) ∷
   rw 0 (q16 c4) ∷
   rw 1 (q17 c4) ∷
   rw 2 (q181 c4) ∷
   rw 3 (q17 c4) ∷
   rw 4 (q16 c4) ∷
   rw 5 (q181 c4) ∷
   re 0 6 (Bx0-3421 ∷ []) ∷ []) Eq.refl

-- resp CCZ023 at 1: 2 steps
lem-resp-CCZ023-at-1 : WsL → ⟪ (CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CCZ023-at-1 c4 = derive (CCZ023 ∷ []) (Sw01 ∷ CCZ123 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q38 c4) ∷
   rw 0 (q50 c4) ∷ []) Eq.refl

private
  q182 : WsL → Eqn
  q182 c4 = eqn (Sw01 ∷ Toff123 ∷ []) (Toff023 ∷ Sw01 ∷ []) (wl0053 c4)
  q183 : WsL → Eqn
  q183 c4 = eqn (Sw01 ∷ Bx2-10 ∷ []) (Bx2-01 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·10⟩ c4)

-- nat 0 BOX(1;230): 8 steps
lem-nat-0-BOX⟨1·230⟩ : WsL → ⟪ (Sw01 ∷ Bx1-230 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-231 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·230⟩ c4 = derive (Sw01 ∷ Bx1-230 ∷ []) (Bx0-231 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) ∷
   rw⁻ 0 (q50 c4) ∷
   rw 1 (q182 c4) ∷
   rw 2 (q183 c4) ∷
   rw 3 (q182 c4) ∷
   rw⁻ 4 (q50 c4) ∷
   rw 5 (q183 c4) ∷
   re 0 6 (Bx0-231 ∷ []) ∷ []) Eq.refl

private
  q184 : WsL → Eqn
  q184 c4 = eqn (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4)
  q185 : WsL → Eqn
  q185 c4 = eqn (Sw01 ∷ Bx1-230 ∷ []) (Bx0-231 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·230⟩ c4)

-- nat 0 BOX(2;1430): 8 steps
lem-nat-0-BOX⟨2·1430⟩ : WsL → ⟪ (Sw01 ∷ Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·1430⟩ c4 = derive (Sw01 ∷ Bx2-1430 ∷ []) (Bx2-0431 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-230 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ []) ∷
   rw 0 (q184 c4) ∷
   rw 1 (q153 c4) ∷
   rw 2 (q185 c4) ∷
   rw 3 (q153 c4) ∷
   rw 4 (q184 c4) ∷
   rw 5 (q185 c4) ∷
   re 0 6 (Bx2-0431 ∷ []) ∷ []) Eq.refl

private
  q186 : WsL → Eqn
  q186 c4 = eqn (Sw01 ∷ Toff023 ∷ []) (Toff123 ∷ Sw01 ∷ []) (wl0108 c4)
  q187 : WsL → Eqn
  q187 c4 = eqn (Sw01 ∷ Bx2-01 ∷ []) (Bx2-10 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·01⟩ c4)

-- nat 0 BOX(0;231): 8 steps
lem-nat-0-BOX⟨0·231⟩ : WsL → ⟪ (Sw01 ∷ Bx0-231 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-230 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·231⟩ c4 = derive (Sw01 ∷ Bx0-231 ∷ []) (Bx1-230 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) ∷
   rw⁻ 0 (q47 c4) ∷
   rw 1 (q186 c4) ∷
   rw 2 (q187 c4) ∷
   rw 3 (q186 c4) ∷
   rw⁻ 4 (q47 c4) ∷
   rw 5 (q187 c4) ∷
   re 0 6 (Bx1-230 ∷ []) ∷ []) Eq.refl

private
  q188 : WsL → Eqn
  q188 c4 = eqn (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4)
  q189 : WsL → Eqn
  q189 c4 = eqn (Sw01 ∷ Toff204 ∷ []) (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4)
  q190 : WsL → Eqn
  q190 c4 = eqn (Sw01 ∷ Bx0-231 ∷ []) (Bx1-230 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·231⟩ c4)

-- nat 0 BOX(2;0431): 8 steps
lem-nat-0-BOX⟨2·0431⟩ : WsL → ⟪ (Sw01 ∷ Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·0431⟩ c4 = derive (Sw01 ∷ Bx2-0431 ∷ []) (Bx2-1430 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-231 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ []) ∷
   rw 0 (q188 c4) ∷
   rw 1 (q189 c4) ∷
   rw 2 (q190 c4) ∷
   rw 3 (q189 c4) ∷
   rw 4 (q188 c4) ∷
   rw 5 (q190 c4) ∷
   re 0 6 (Bx2-1430 ∷ []) ∷ []) Eq.refl

private
  q191 : WsL → Eqn
  q191 c4 = eqn (Sw12 ∷ CZ02 ∷ []) (CZ01 ∷ Sw12 ∷ []) (lem-nat-1-CZ02 c4)

-- nat 1 BOX(1;20): 3 steps
lem-nat-1-BOX⟨1·20⟩ : WsL → ⟪ (Sw12 ∷ Bx1-20 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-10 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·20⟩ c4 = derive (Sw12 ∷ Bx1-20 ∷ []) (Bx2-10 ∷ Sw12 ∷ [])
  (re 1 1 (CZ02 ∷ []) ∷
   rw 0 (q191 c4) ∷
   re 0 1 (Bx2-10 ∷ []) ∷ []) Eq.refl

private
  q192 : WsL → Eqn
  q192 c4 = eqn (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) (wl0112 c4)
  q193 : WsL → Eqn
  q193 c4 = eqn (Sw12 ∷ Bx1-20 ∷ []) (Bx2-10 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·20⟩ c4)

-- nat 1 BOX(2;130): 8 steps
lem-nat-1-BOX⟨2·130⟩ : WsL → ⟪ (Sw12 ∷ Bx2-130 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-230 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·130⟩ c4 = derive (Sw12 ∷ Bx2-130 ∷ []) (Bx1-230 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-20 ∷ Toff213 ∷ CCZ123 ∷ Bx1-20 ∷ []) ∷
   rw⁻ 0 (q44 c4) ∷
   rw 1 (q192 c4) ∷
   rw 2 (q193 c4) ∷
   rw 3 (q192 c4) ∷
   rw⁻ 4 (q44 c4) ∷
   rw 5 (q193 c4) ∷
   re 0 6 (Bx1-230 ∷ []) ∷ []) Eq.refl

private
  q194 : WsL → Eqn
  q194 c4 = eqn (CCZ124 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ124 ∷ []) (wl0078 c4)
  q195 : WsL → Eqn
  q195 c4 = eqn (Sw12 ∷ Bx2-130 ∷ []) (Bx1-230 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·130⟩ c4)

-- nat 1 BOX(1;2430): 8 steps
lem-nat-1-BOX⟨1·2430⟩ : WsL → ⟪ (Sw12 ∷ Bx1-2430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·2430⟩ c4 = derive (Sw12 ∷ Bx1-2430 ∷ []) (Bx2-1430 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-130 ∷ Toff124 ∷ CCZ124 ∷ Bx2-130 ∷ []) ∷
   rw⁻ 0 (q194 c4) ∷
   rw 1 (q147 c4) ∷
   rw 2 (q195 c4) ∷
   rw 3 (q147 c4) ∷
   rw⁻ 4 (q194 c4) ∷
   rw 5 (q195 c4) ∷
   re 0 6 (Bx2-1430 ∷ []) ∷ []) Eq.refl

private
  q196 : WsL → Eqn
  q196 c4 = eqn (Sw12 ∷ Toff123 ∷ []) (Toff213 ∷ Sw12 ∷ []) (wl0146 c4)
  q197 : WsL → Eqn
  q197 c4 = eqn (Sw12 ∷ Bx2-10 ∷ []) (Bx1-20 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·10⟩ c4)

-- nat 1 BOX(1;230): 8 steps
lem-nat-1-BOX⟨1·230⟩ : WsL → ⟪ (Sw12 ∷ Bx1-230 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-130 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·230⟩ c4 = derive (Sw12 ∷ Bx1-230 ∷ []) (Bx2-130 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) ∷
   rw⁻ 0 (q44 c4) ∷
   rw 1 (q196 c4) ∷
   rw 2 (q197 c4) ∷
   rw 3 (q196 c4) ∷
   rw⁻ 4 (q44 c4) ∷
   rw 5 (q197 c4) ∷
   re 0 6 (Bx2-130 ∷ []) ∷ []) Eq.refl

private
  q198 : WsL → Eqn
  q198 c4 = eqn (Sw12 ∷ Toff214 ∷ []) (Toff124 ∷ Sw12 ∷ []) (wl0126 c4)
  q199 : WsL → Eqn
  q199 c4 = eqn (Sw12 ∷ Bx1-230 ∷ []) (Bx2-130 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·230⟩ c4)

-- nat 1 BOX(2;1430): 8 steps
lem-nat-1-BOX⟨2·1430⟩ : WsL → ⟪ (Sw12 ∷ Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2430 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·1430⟩ c4 = derive (Sw12 ∷ Bx2-1430 ∷ []) (Bx1-2430 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-230 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ []) ∷
   rw⁻ 0 (q194 c4) ∷
   rw 1 (q198 c4) ∷
   rw 2 (q199 c4) ∷
   rw 3 (q198 c4) ∷
   rw⁻ 4 (q194 c4) ∷
   rw 5 (q199 c4) ∷
   re 0 6 (Bx1-2430 ∷ []) ∷ []) Eq.refl

private
  q200 : WsL → Eqn
  q200 c4 = eqn (CS01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ))

-- comm CCZ123 CS04: 13 steps
lem-comm-CCZ123-CS04 : WsL → ⟪ (CCZ123 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ CCZ123 ∷ []) ⟫ʷ
lem-comm-CCZ123-CS04 c4 = derive (CCZ123 ∷ CS04 ∷ []) (CS04 ∷ CCZ123 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q92 c4) ∷
   re 1 3 (CCZ124 ∷ []) ∷
   rw⁻ 1 (q32 c4) ∷
   re 2 3 (CCZ134 ∷ []) ∷
   rw 2 (q68 c4) ∷
   rw⁻ 3 (q200 c4) ∷
   rw 4 (q64 c4) ∷
   re 5 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 7 (q32 c4) ∷
   re 6 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   rw 8 (q92 c4) ∷
   re 0 7 (CS04 ∷ []) ∷ []) Eq.refl

private
  q201 : WsL → Eqn
  q201 c4 = eqn (CCZ012 ∷ CS34 ∷ []) (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS))

-- comm CCZ013 CS24: 15 steps
lem-comm-CCZ013-CS24 : WsL → ⟪ (CCZ013 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CS24 c4 = derive (CCZ013 ∷ CS24 ∷ []) (CS24 ∷ CCZ013 ∷ [])
  (re 1 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q92 c4) ∷
   re 1 3 (CCZ014 ∷ []) ∷
   re 1 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 7 (q92 c4) ∷
   re 5 3 (CS24 ∷ []) ∷
   rw⁻ 4 (q101 c4) ∷
   rw 3 (q201 c4) ∷
   rw⁻ 2 (q107 c4) ∷
   re 2 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 1 (q92 c4) ∷
   re 2 5 (CCZ014 ∷ []) ∷
   re 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   rw 4 (q92 c4) ∷
   re 0 3 (CS24 ∷ []) ∷ []) Eq.refl

private
  q202 : WsL → Eqn
  q202 c4 = eqn (CK10 ∷ CCZ234 ∷ []) (CCZ234 ∷ CK10 ∷ []) (c₂ (CK₁₀) (CCZ))

-- comm CK40 CCZ123: 13 steps
lem-comm-CK40-CCZ123 : WsL → ⟪ (CK40 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK40 ∷ []) ⟫ʷ
lem-comm-CK40-CCZ123 c4 = derive (CK40 ∷ CCZ123 ∷ []) (CCZ123 ∷ CK40 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q92 c4) ∷
   re 6 3 (CCZ124 ∷ []) ∷
   rw⁻ 7 (q32 c4) ∷
   re 5 3 (CCZ134 ∷ []) ∷
   rw⁻ 4 (q64 c4) ∷
   rw 3 (q202 c4) ∷
   rw⁻ 2 (q68 c4) ∷
   re 2 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 1 (q32 c4) ∷
   re 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   rw 0 (q92 c4) ∷
   re 1 7 (CK40 ∷ []) ∷ []) Eq.refl

-- comm CCZ123 CK40: 13 steps
lem-comm-CCZ123-CK40 : WsL → ⟪ (CCZ123 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CCZ123 ∷ []) ⟫ʷ
lem-comm-CCZ123-CK40 c4 = derive (CCZ123 ∷ CK40 ∷ []) (CK40 ∷ CCZ123 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q92 c4) ∷
   re 1 3 (CCZ124 ∷ []) ∷
   rw⁻ 1 (q32 c4) ∷
   re 2 3 (CCZ134 ∷ []) ∷
   rw 2 (q68 c4) ∷
   rw⁻ 3 (q202 c4) ∷
   rw 4 (q64 c4) ∷
   re 5 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 7 (q32 c4) ∷
   re 6 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   rw 8 (q92 c4) ∷
   re 0 7 (CK40 ∷ []) ∷ []) Eq.refl

-- resp CK40 at 3: 20 steps
lem-resp-CK40-at-3 : WsL → ⟪ (CK40 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CK40-at-3 c4 = derive (CK40 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q32 c4) ∷
   re 0 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q33 c4) ∷
   rw 4 (q34 c4) ∷
   rw 3 (q122 c4) ∷
   rw 2 (q34 c4) ∷
   rw⁻ 0 (q33 c4) ∷
   re 1 7 (CK40 ∷ []) ∷
   rw⁻ 2 (q36 c4) ∷
   re 1 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw⁻ 3 (q34 c4) ∷
   rw 2 (q123 c4) ∷
   rw⁻ 1 (q34 c4) ∷
   re 2 3 (CK40 ∷ []) ∷
   rw⁻ 3 (q38 c4) ∷
   re 2 1 (Sw34 ∷ CK30 ∷ Sw34 ∷ []) ∷
   rw⁻ 4 (q39 c4) ∷
   rw 3 (q124 c4) ∷
   rw⁻ 2 (q39 c4) ∷
   re 3 3 (CK41 ∷ []) ∷ []) Eq.refl

private
  q203 : WsL → Eqn
  q203 c4 = eqn (CK41 ∷ Sw12 ∷ []) (Sw12 ∷ CK42 ∷ []) (wl0160 c4)
  q204 : WsL → Eqn
  q204 c4 = eqn (CK42 ∷ Sw23 ∷ []) (Sw23 ∷ CK43 ∷ []) (wl0162 c4)
  q205 : WsL → Eqn
  q205 c4 = eqn (Toff102 ∷ CK43 ∷ []) (CK43 ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (CK₁₀))
  q206 : WsL → Eqn
  q206 c4 = eqn (CK43 ∷ Sw23 ∷ []) (Sw23 ∷ CK42 ∷ []) (wl0163 c4)
  q207 : WsL → Eqn
  q207 c4 = eqn (CK42 ∷ Sw12 ∷ []) (Sw12 ∷ CK41 ∷ []) (wl0164 c4)

-- comm CK41 TOFF203: 7 steps
lem-comm-CK41-TOFF203 : WsL → ⟪ (CK41 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CK41 ∷ []) ⟫ʷ
lem-comm-CK41-TOFF203 c4 = derive (CK41 ∷ Toff203 ∷ []) (Toff203 ∷ CK41 ∷ [])
  (re 1 1 (Sw12 ∷ Sw23 ∷ Toff102 ∷ Sw23 ∷ Sw12 ∷ []) ∷
   rw 0 (q203 c4) ∷
   rw 1 (q204 c4) ∷
   rw⁻ 2 (q205 c4) ∷
   rw 3 (q206 c4) ∷
   rw 4 (q207 c4) ∷
   re 0 5 (Toff203 ∷ []) ∷ []) Eq.refl

private
  q208 : WsL → Eqn
  q208 c4 = eqn (CK41 ∷ Sw23 ∷ []) (Sw23 ∷ CK41 ∷ []) (wl0165 c4)
  q209 : WsL → Eqn
  q209 c4 = eqn (Sw01 ∷ CK42 ∷ []) (CK42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CK₁₀ • Swap ↑))

-- resp CK41 at 3: 6 steps
lem-resp-CK41-at-3 : WsL → ⟪ (CK41 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK42 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CK41-at-3 c4 = derive (CK41 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK42 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q32 c4) ∷
   rw 0 (q208 c4) ∷
   rw⁻ 2 (q36 c4) ∷
   rw 1 (q203 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   rw⁻ 2 (q209 c4) ∷ []) Eq.refl

private
  q210 : WsL → Eqn
  q210 c4 = eqn (CCZ012 ∷ CK43 ∷ []) (CK43 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CK₁₀))

-- comm CK41 CCZ023: 7 steps
lem-comm-CK41-CCZ023 : WsL → ⟪ (CK41 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CK41 ∷ []) ⟫ʷ
lem-comm-CK41-CCZ023 c4 = derive (CK41 ∷ CCZ023 ∷ []) (CCZ023 ∷ CK41 ∷ [])
  (re 1 1 (Sw12 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw12 ∷ []) ∷
   rw 0 (q203 c4) ∷
   rw 1 (q204 c4) ∷
   rw⁻ 2 (q210 c4) ∷
   rw 3 (q206 c4) ∷
   rw 4 (q207 c4) ∷
   re 0 5 (CCZ023 ∷ []) ∷ []) Eq.refl

private
  q211 : WsL → Eqn
  q211 c4 = eqn (Toff012 ∷ CK43 ∷ []) (CK43 ∷ Toff012 ∷ []) (c₃ (Toff) (CK₁₀))

-- comm CK41 TOFF023: 7 steps
lem-comm-CK41-TOFF023 : WsL → ⟪ (CK41 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CK41 ∷ []) ⟫ʷ
lem-comm-CK41-TOFF023 c4 = derive (CK41 ∷ Toff023 ∷ []) (Toff023 ∷ CK41 ∷ [])
  (re 1 1 (Sw12 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw12 ∷ []) ∷
   rw 0 (q203 c4) ∷
   rw 1 (q204 c4) ∷
   rw⁻ 2 (q211 c4) ∷
   rw 3 (q206 c4) ∷
   rw 4 (q207 c4) ∷
   re 0 5 (Toff023 ∷ []) ∷ []) Eq.refl

-- comm CCZ013 CK42: 15 steps
lem-comm-CCZ013-CK42 : WsL → ⟪ (CCZ013 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CK42 c4 = derive (CCZ013 ∷ CK42 ∷ []) (CK42 ∷ CCZ013 ∷ [])
  (re 1 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q92 c4) ∷
   re 1 3 (CCZ014 ∷ []) ∷
   re 1 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 7 (q92 c4) ∷
   re 5 3 (CK42 ∷ []) ∷
   rw⁻ 4 (q206 c4) ∷
   rw 3 (q210 c4) ∷
   rw⁻ 2 (q204 c4) ∷
   re 2 1 (Sw34 ∷ CK32 ∷ Sw34 ∷ []) ∷
   rw 1 (q92 c4) ∷
   re 2 5 (CCZ014 ∷ []) ∷
   re 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   rw 4 (q92 c4) ∷
   re 0 3 (CK42 ∷ []) ∷ []) Eq.refl

-- comm CK42 TOFF013: 5 steps
lem-comm-CK42-TOFF013 : WsL → ⟪ (CK42 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CK42 ∷ []) ⟫ʷ
lem-comm-CK42-TOFF013 c4 = derive (CK42 ∷ Toff013 ∷ []) (Toff013 ∷ CK42 ∷ [])
  (re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   rw 0 (q204 c4) ∷
   rw⁻ 1 (q211 c4) ∷
   rw 2 (q206 c4) ∷
   re 0 3 (Toff013 ∷ []) ∷ []) Eq.refl

-- comm CK42 CCZ013: 5 steps
lem-comm-CK42-CCZ013 : WsL → ⟪ (CK42 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CK42 ∷ []) ⟫ʷ
lem-comm-CK42-CCZ013 c4 = derive (CK42 ∷ CCZ013 ∷ []) (CCZ013 ∷ CK42 ∷ [])
  (re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   rw 0 (q204 c4) ∷
   rw⁻ 1 (q210 c4) ∷
   rw 2 (q206 c4) ∷
   re 0 3 (CCZ013 ∷ []) ∷ []) Eq.refl

private
  q212 : WsL → Eqn
  q212 c4 = eqn (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) (wl0091 c4)
  q213 : WsL → Eqn
  q213 c4 = eqn (Sw01 ∷ Toff423 ∷ []) (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ))

-- resp TOFF413 at 2: 4 steps
lem-resp-TOFF413-at-2 : WsL → ⟪ (Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff423 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF413-at-2 c4 = derive (Toff413 ∷ []) (Sw12 ∷ Sw01 ∷ Toff423 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q36 c4) ∷
   rw⁻ 0 (q212 c4) ∷
   rw⁻ 2 (q38 c4) ∷
   rw⁻ 1 (q213 c4) ∷ []) Eq.refl

private
  q214 : WsL → Eqn
  q214 c4 = eqn (CS01 ∷ Sw01 ∷ []) (Sw01 ∷ CS01 ∷ []) (wl0132 c4)

-- nat 0 SBOX(2;0;1;3): 3 steps
lem-nat-0-SBOX⟨2·0·1·3⟩ : WsL → ⟪ (Sw01 ∷ Sb2-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-0-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·0·1·3⟩ c4 = derive (Sw01 ∷ Sb2-0-1-3 ∷ []) (Sb2-1-0-3 ∷ Sw01 ∷ [])
  (re 1 1 (CS01 ∷ []) ∷
   rw⁻ 0 (q214 c4) ∷
   re 0 1 (Sb2-1-0-3 ∷ []) ∷ []) Eq.refl

private
  q215 : WsL → Eqn
  q215 c4 = eqn (CS01⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS01⁻ ∷ []) (wl0133 c4)

-- nat 0 SBOXd(2;0;1;3): 3 steps
lem-nat-0-SBOXd⟨2·0·1·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-0-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-0-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·0·1·3⟩ c4 = derive (Sw01 ∷ Sb⁻2-0-1-3 ∷ []) (Sb⁻2-1-0-3 ∷ Sw01 ∷ [])
  (re 1 1 (CS01⁻ ∷ []) ∷
   rw⁻ 0 (q215 c4) ∷
   re 0 1 (Sb⁻2-1-0-3 ∷ []) ∷ []) Eq.refl

private
  q216 : WsL → Eqn
  q216 c4 = eqn (Sw34 ∷ CCZ023 ∷ []) (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4)
  q217 : WsL → Eqn
  q217 c4 = eqn (Sw34 ∷ Toff203 ∷ []) (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4)
  q218 : WsL → Eqn
  q218 c4 = eqn (Bx0-21 ∷ Sw34 ∷ []) (Sw34 ∷ Bx0-21 ∷ []) (c₃ (CZ ↑) (Swap))

-- nat 3 BOX(2;031): 8 steps
lem-nat-3-BOX⟨2·031⟩ : WsL → ⟪ (Sw34 ∷ Bx2-031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-041 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·031⟩ c4 = derive (Sw34 ∷ Bx2-031 ∷ []) (Bx2-041 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) ∷
   rw 0 (q216 c4) ∷
   rw 1 (q217 c4) ∷
   rw⁻ 2 (q218 c4) ∷
   rw 3 (q217 c4) ∷
   rw 4 (q216 c4) ∷
   rw⁻ 5 (q218 c4) ∷
   re 0 6 (Bx2-041 ∷ []) ∷ []) Eq.refl

private
  q219 : WsL → Eqn
  q219 c4 = eqn (Sw34 ∷ CCZ024 ∷ []) (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4)
  q220 : WsL → Eqn
  q220 c4 = eqn (Sw34 ∷ Toff024 ∷ []) (Toff023 ∷ Sw34 ∷ []) (lem-nat-3-TOFF024 c4)
  q221 : WsL → Eqn
  q221 c4 = eqn (Sw34 ∷ Bx2-031 ∷ []) (Bx2-041 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·031⟩ c4)

-- nat 3 BOX(0;2431): 8 steps
lem-nat-3-BOX⟨0·2431⟩ : WsL → ⟪ (Sw34 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·2431⟩ c4 = derive (Sw34 ∷ Bx0-2431 ∷ []) (Bx0-2341 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) ∷
   rw 0 (q219 c4) ∷
   rw 1 (q220 c4) ∷
   rw 2 (q221 c4) ∷
   rw 3 (q220 c4) ∷
   rw 4 (q219 c4) ∷
   rw 5 (q221 c4) ∷
   re 0 6 (Bx0-2341 ∷ []) ∷ []) Eq.refl

private
  q222 : WsL → Eqn
  q222 c4 = eqn (Sw34 ∷ Toff204 ∷ []) (Toff203 ∷ Sw34 ∷ []) (lem-nat-3-TOFF204 c4)

-- nat 3 BOX(2;041): 8 steps
lem-nat-3-BOX⟨2·041⟩ : WsL → ⟪ (Sw34 ∷ Bx2-041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-031 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·041⟩ c4 = derive (Sw34 ∷ Bx2-041 ∷ []) (Bx2-031 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) ∷
   rw 0 (q219 c4) ∷
   rw 1 (q222 c4) ∷
   rw⁻ 2 (q218 c4) ∷
   rw 3 (q222 c4) ∷
   rw 4 (q219 c4) ∷
   rw⁻ 5 (q218 c4) ∷
   re 0 6 (Bx2-031 ∷ []) ∷ []) Eq.refl

private
  q223 : WsL → Eqn
  q223 c4 = eqn (Sw34 ∷ Toff023 ∷ []) (Toff024 ∷ Sw34 ∷ []) (lem-nat-3-TOFF023 c4)
  q224 : WsL → Eqn
  q224 c4 = eqn (Sw34 ∷ Bx2-041 ∷ []) (Bx2-031 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·041⟩ c4)

-- nat 3 BOX(0;2341): 8 steps
lem-nat-3-BOX⟨0·2341⟩ : WsL → ⟪ (Sw34 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·2341⟩ c4 = derive (Sw34 ∷ Bx0-2341 ∷ []) (Bx0-2431 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) ∷
   rw 0 (q216 c4) ∷
   rw 1 (q223 c4) ∷
   rw 2 (q224 c4) ∷
   rw 3 (q223 c4) ∷
   rw 4 (q216 c4) ∷
   rw 5 (q224 c4) ∷
   re 0 6 (Bx0-2431 ∷ []) ∷ []) Eq.refl
