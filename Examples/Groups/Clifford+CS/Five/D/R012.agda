{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R012 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0003 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0011 ; wl0012 ; wl0016 ; wl0017 ; wl0018 ; wl0019 ; wl0021 ; wl0022 ; wl0023 ; wl0024 ; wl0027 ; wl0028 ; wl0029 ; wl0033 ; wl0034 ; wl0037 ; wl0038 ; wl0039 ; wl0040 ; wl0042 ; wl0043 ; wl0044 ; wl0045 ; wl0047 ; wl0050 ; wl0051 ; wl0064 ; wl0065 ; wl0078 ; wl0084 ; wl0085 ; wl0086 ; wl0090 ; wl0091 ; wl0095 ; wl0099 ; wl0100 ; wl0101 ; wl0103 ; wl0109 ; wl0110 ; wl0113 ; wl0114 ; wl0115 ; wl0116 ; wl0126 ; wl0128 ; wl0129 ; wl0130 ; wl0134 ; wl0135 ; wl0136 ; wl0137 ; wl0138 ; wl0139 ; wl0140 ; wl0143 ; wl0144 ; wl0152 ; wl0153 ; wl0154 ; wl0155)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-BOX⟨0·2134⟩ ; lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-TOFF024 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF102 ; lem-nat-2-TOFF301 ; lem-nat-3-CCZ014 ; lem-nat-3-CZ13 ; lem-nat-3-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ124 ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF103 ; lem-nat-1-TOFF301 ; lem-nat-1-TOFF302 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF201 ; lem-nat-2-TOFF204 ; lem-nat-3-CCZ023 ; lem-nat-3-TOFF203)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-BOX⟨1·43⟩ ; lem-nat-0-CCZ014 ; lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF304 ; lem-nat-0-TOFF403 ; lem-nat-1-TOFF204 ; lem-nat-3-CZ23)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-BOX⟨3·40⟩ ; lem-nat-0-TOFF214 ; lem-nat-0-TOFF413 ; lem-nat-1-BOX⟨0·1234⟩ ; lem-nat-1-TOFF304 ; lem-nat-2-TOFF104 ; lem-nat-3-TOFF302)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-TOFF401 ; lem-nat-1-CZ04 ; lem-nat-1-TOFF023 ; lem-nat-1-TOFF401 ; lem-nat-2-CCZ014 ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124 ; lem-nat-3-CZ03 ; lem-nat-3-CZ04)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-0-BOX⟨0·2134⟩ ; lem-nat-0-BOX⟨1·2034⟩ ; lem-nat-2-CS12 ; lem-nat-2-CSd12 ; lem-nat-2-CZ12 ; lem-nat-3-CS13 ; lem-nat-3-CSd13 ; lem-nat-3-CZ24)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-BOX⟨2·1403⟩ ; lem-nat-0-CS04 ; lem-nat-0-TOFF134 ; lem-nat-1-BOX⟨2·41⟩ ; lem-nat-1-CS04 ; lem-nat-2-TOFF403 ; lem-nat-3-CS24)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨0·32⟩ ; lem-nat-0-BOX⟨1·32⟩ ; lem-nat-0-TOFF034 ; lem-nat-1-BOX⟨1·32⟩ ; lem-nat-1-BOX⟨2·31⟩ ; lem-nat-1-CSd04 ; lem-nat-3-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-0-CSd04 ; lem-nat-1-TOFF402 ; lem-nat-2-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-0-BOX⟨2·30⟩ ; lem-nat-0-BOX⟨2·31⟩ ; lem-nat-0-TOFF124 ; lem-nat-3-TOFF123 ; lem-nat-3-TOFF124)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-1-BOX⟨1·23⟩ ; lem-nat-2-TOFF134)

private
  q1 : WsL → Eqn
  q1 c4 = eqn (CZ34 ∷ Sw23 ∷ []) (Sw23 ∷ CZ24 ∷ []) (wl0028 c4)

-- nat 2 BOX(1;24): 3 steps
lem-nat-2-BOX⟨1·24⟩ : WsL → ⟪ (Sw23 ∷ Bx1-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-34 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·24⟩ c4 = derive (Sw23 ∷ Bx1-24 ∷ []) (Bx1-34 ∷ Sw23 ∷ [])
  (re 1 1 (CZ24 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 0 1 (Bx1-34 ∷ []) ∷ []) Eq.refl

private
  q2 : WsL → Eqn
  q2 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4)
  q3 : WsL → Eqn
  q3 c4 = eqn (Sw23 ∷ Toff201 ∷ []) (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4)
  q4 : WsL → Eqn
  q4 c4 = eqn (Sw23 ∷ Bx1-24 ∷ []) (Bx1-34 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·24⟩ c4)

-- nat 2 BOX(2;104): 8 steps
lem-nat-2-BOX⟨2·104⟩ : WsL → ⟪ (Sw23 ∷ Bx2-104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-104 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·104⟩ c4 = derive (Sw23 ∷ Bx2-104 ∷ []) (Bx3-104 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-24 ∷ Toff201 ∷ CCZ012 ∷ Bx1-24 ∷ []) ∷
   rw 0 (q2 c4) ∷
   rw 1 (q3 c4) ∷
   rw 2 (q4 c4) ∷
   rw 3 (q3 c4) ∷
   rw 4 (q2 c4) ∷
   rw 5 (q4 c4) ∷
   re 0 6 (Bx3-104 ∷ []) ∷ []) Eq.refl

private
  q5 : WsL → Eqn
  q5 c4 = eqn (CCZ123 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ123 ∷ []) (wl0113 c4)
  q6 : WsL → Eqn
  q6 c4 = eqn (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ []) (wl0114 c4)
  q7 : WsL → Eqn
  q7 c4 = eqn (Sw23 ∷ Bx2-104 ∷ []) (Bx3-104 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·104⟩ c4)

-- nat 2 BOX(1;2304): 8 steps
lem-nat-2-BOX⟨1·2304⟩ : WsL → ⟪ (Sw23 ∷ Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3204 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·2304⟩ c4 = derive (Sw23 ∷ Bx1-2304 ∷ []) (Bx1-3204 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-104 ∷ Toff123 ∷ CCZ123 ∷ Bx2-104 ∷ []) ∷
   rw⁻ 0 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw 2 (q7 c4) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q5 c4) ∷
   rw 5 (q7 c4) ∷
   re 0 6 (Bx1-3204 ∷ []) ∷ []) Eq.refl

private
  q8 : WsL → Eqn
  q8 c4 = eqn (CZ24 ∷ Sw23 ∷ []) (Sw23 ∷ CZ34 ∷ []) (wl0027 c4)

-- nat 2 BOX(1;34): 3 steps
lem-nat-2-BOX⟨1·34⟩ : WsL → ⟪ (Sw23 ∷ Bx1-34 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-24 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·34⟩ c4 = derive (Sw23 ∷ Bx1-34 ∷ []) (Bx1-24 ∷ Sw23 ∷ [])
  (re 1 1 (CZ34 ∷ []) ∷
   rw⁻ 0 (q8 c4) ∷
   re 0 1 (Bx1-24 ∷ []) ∷ []) Eq.refl

private
  q9 : WsL → Eqn
  q9 c4 = eqn (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4)
  q10 : WsL → Eqn
  q10 c4 = eqn (Sw23 ∷ Toff301 ∷ []) (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4)
  q11 : WsL → Eqn
  q11 c4 = eqn (Sw23 ∷ Bx1-34 ∷ []) (Bx1-24 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·34⟩ c4)

-- nat 2 BOX(3;104): 8 steps
lem-nat-2-BOX⟨3·104⟩ : WsL → ⟪ (Sw23 ∷ Bx3-104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-104 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·104⟩ c4 = derive (Sw23 ∷ Bx3-104 ∷ []) (Bx2-104 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-34 ∷ Toff301 ∷ CCZ013 ∷ Bx1-34 ∷ []) ∷
   rw 0 (q9 c4) ∷
   rw 1 (q10 c4) ∷
   rw 2 (q11 c4) ∷
   rw 3 (q10 c4) ∷
   rw 4 (q9 c4) ∷
   rw 5 (q11 c4) ∷
   re 0 6 (Bx2-104 ∷ []) ∷ []) Eq.refl

private
  q12 : WsL → Eqn
  q12 c4 = eqn (Sw23 ∷ Bx3-104 ∷ []) (Bx2-104 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·104⟩ c4)

-- nat 2 BOX(1;3204): 8 steps
lem-nat-2-BOX⟨1·3204⟩ : WsL → ⟪ (Sw23 ∷ Bx1-3204 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·3204⟩ c4 = derive (Sw23 ∷ Bx1-3204 ∷ []) (Bx1-2304 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-104 ∷ Toff123 ∷ CCZ123 ∷ Bx3-104 ∷ []) ∷
   rw⁻ 0 (q5 c4) ∷
   rw 1 (q6 c4) ∷
   rw 2 (q12 c4) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q5 c4) ∷
   rw 5 (q12 c4) ∷
   re 0 6 (Bx1-2304 ∷ []) ∷ []) Eq.refl

private
  q13 : WsL → Eqn
  q13 c4 = eqn (Sw34 ∷ CZ23 ∷ []) (CZ24 ∷ Sw34 ∷ []) (lem-nat-3-CZ23 c4)

-- nat 3 BOX(1;23): 3 steps
lem-nat-3-BOX⟨1·23⟩ : WsL → ⟪ (Sw34 ∷ Bx1-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-24 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·23⟩ c4 = derive (Sw34 ∷ Bx1-23 ∷ []) (Bx1-24 ∷ Sw34 ∷ [])
  (re 1 1 (CZ23 ∷ []) ∷
   rw 0 (q13 c4) ∷
   re 0 1 (Bx1-24 ∷ []) ∷ []) Eq.refl

private
  q14 : WsL → Eqn
  q14 c4 = eqn (CCZ012 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (Swap))
  q15 : WsL → Eqn
  q15 c4 = eqn (Toff201 ∷ Sw34 ∷ []) (Sw34 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (Swap))
  q16 : WsL → Eqn
  q16 c4 = eqn (Sw34 ∷ Bx1-23 ∷ []) (Bx1-24 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·23⟩ c4)

-- nat 3 BOX(2;103): 8 steps
lem-nat-3-BOX⟨2·103⟩ : WsL → ⟪ (Sw34 ∷ Bx2-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-104 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·103⟩ c4 = derive (Sw34 ∷ Bx2-103 ∷ []) (Bx2-104 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-23 ∷ Toff201 ∷ CCZ012 ∷ Bx1-23 ∷ []) ∷
   rw⁻ 0 (q14 c4) ∷
   rw⁻ 1 (q15 c4) ∷
   rw 2 (q16 c4) ∷
   rw⁻ 3 (q15 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   rw 5 (q16 c4) ∷
   re 0 6 (Bx2-104 ∷ []) ∷ []) Eq.refl

private
  q17 : WsL → Eqn
  q17 c4 = eqn (Sw34 ∷ CCZ124 ∷ []) (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4)
  q18 : WsL → Eqn
  q18 c4 = eqn (Sw34 ∷ Toff124 ∷ []) (Toff123 ∷ Sw34 ∷ []) (lem-nat-3-TOFF124 c4)
  q19 : WsL → Eqn
  q19 c4 = eqn (Sw34 ∷ Bx2-103 ∷ []) (Bx2-104 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·103⟩ c4)

-- nat 3 BOX(1;2403): 8 steps
lem-nat-3-BOX⟨1·2403⟩ : WsL → ⟪ (Sw34 ∷ Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2304 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·2403⟩ c4 = derive (Sw34 ∷ Bx1-2403 ∷ []) (Bx1-2304 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-103 ∷ Toff124 ∷ CCZ124 ∷ Bx2-103 ∷ []) ∷
   rw 0 (q17 c4) ∷
   rw 1 (q18 c4) ∷
   rw 2 (q19 c4) ∷
   rw 3 (q18 c4) ∷
   rw 4 (q17 c4) ∷
   rw 5 (q19 c4) ∷
   re 0 6 (Bx1-2304 ∷ []) ∷ []) Eq.refl

private
  q20 : WsL → Eqn
  q20 c4 = eqn (Sw34 ∷ CZ24 ∷ []) (CZ23 ∷ Sw34 ∷ []) (lem-nat-3-CZ24 c4)

-- nat 3 BOX(1;24): 3 steps
lem-nat-3-BOX⟨1·24⟩ : WsL → ⟪ (Sw34 ∷ Bx1-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-23 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·24⟩ c4 = derive (Sw34 ∷ Bx1-24 ∷ []) (Bx1-23 ∷ Sw34 ∷ [])
  (re 1 1 (CZ24 ∷ []) ∷
   rw 0 (q20 c4) ∷
   re 0 1 (Bx1-23 ∷ []) ∷ []) Eq.refl

private
  q21 : WsL → Eqn
  q21 c4 = eqn (Sw34 ∷ Bx1-24 ∷ []) (Bx1-23 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·24⟩ c4)

-- nat 3 BOX(2;104): 8 steps
lem-nat-3-BOX⟨2·104⟩ : WsL → ⟪ (Sw34 ∷ Bx2-104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-103 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·104⟩ c4 = derive (Sw34 ∷ Bx2-104 ∷ []) (Bx2-103 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-24 ∷ Toff201 ∷ CCZ012 ∷ Bx1-24 ∷ []) ∷
   rw⁻ 0 (q14 c4) ∷
   rw⁻ 1 (q15 c4) ∷
   rw 2 (q21 c4) ∷
   rw⁻ 3 (q15 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   rw 5 (q21 c4) ∷
   re 0 6 (Bx2-103 ∷ []) ∷ []) Eq.refl

private
  q22 : WsL → Eqn
  q22 c4 = eqn (Sw34 ∷ CCZ123 ∷ []) (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4)
  q23 : WsL → Eqn
  q23 c4 = eqn (Sw34 ∷ Toff123 ∷ []) (Toff124 ∷ Sw34 ∷ []) (lem-nat-3-TOFF123 c4)
  q24 : WsL → Eqn
  q24 c4 = eqn (Sw34 ∷ Bx2-104 ∷ []) (Bx2-103 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·104⟩ c4)

-- nat 3 BOX(1;2304): 8 steps
lem-nat-3-BOX⟨1·2304⟩ : WsL → ⟪ (Sw34 ∷ Bx1-2304 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·2304⟩ c4 = derive (Sw34 ∷ Bx1-2304 ∷ []) (Bx1-2403 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-104 ∷ Toff123 ∷ CCZ123 ∷ Bx2-104 ∷ []) ∷
   rw 0 (q22 c4) ∷
   rw 1 (q23 c4) ∷
   rw 2 (q24 c4) ∷
   rw 3 (q23 c4) ∷
   rw 4 (q22 c4) ∷
   rw 5 (q24 c4) ∷
   re 0 6 (Bx1-2403 ∷ []) ∷ []) Eq.refl

private
  q25 : WsL → Eqn
  q25 c4 = eqn (CZ23 ∷ Sw12 ∷ []) (Sw12 ∷ CZ13 ∷ []) (wl0029 c4)

-- nat 1 BOX(2;13): 3 steps
lem-nat-1-BOX⟨2·13⟩ : WsL → ⟪ (Sw12 ∷ Bx2-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-23 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·13⟩ c4 = derive (Sw12 ∷ Bx2-13 ∷ []) (Bx1-23 ∷ Sw12 ∷ [])
  (re 1 1 (CZ13 ∷ []) ∷
   rw⁻ 0 (q25 c4) ∷
   re 0 1 (Bx1-23 ∷ []) ∷ []) Eq.refl

private
  q26 : WsL → Eqn
  q26 c4 = eqn (CCZ012 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ012 ∷ []) (wl0037 c4)
  q27 : WsL → Eqn
  q27 c4 = eqn (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) (wl0047 c4)
  q28 : WsL → Eqn
  q28 c4 = eqn (Sw12 ∷ Bx2-13 ∷ []) (Bx1-23 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·13⟩ c4)

-- nat 1 BOX(1;203): 8 steps
lem-nat-1-BOX⟨1·203⟩ : WsL → ⟪ (Sw12 ∷ Bx1-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-103 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·203⟩ c4 = derive (Sw12 ∷ Bx1-203 ∷ []) (Bx2-103 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-13 ∷ Toff102 ∷ CCZ012 ∷ Bx2-13 ∷ []) ∷
   rw⁻ 0 (q26 c4) ∷
   rw 1 (q27 c4) ∷
   rw 2 (q28 c4) ∷
   rw 3 (q27 c4) ∷
   rw⁻ 4 (q26 c4) ∷
   rw 5 (q28 c4) ∷
   re 0 6 (Bx2-103 ∷ []) ∷ []) Eq.refl

private
  q29 : WsL → Eqn
  q29 c4 = eqn (CCZ124 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ124 ∷ []) (wl0078 c4)
  q30 : WsL → Eqn
  q30 c4 = eqn (Sw12 ∷ Toff214 ∷ []) (Toff124 ∷ Sw12 ∷ []) (wl0126 c4)
  q31 : WsL → Eqn
  q31 c4 = eqn (Sw12 ∷ Bx1-203 ∷ []) (Bx2-103 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·203⟩ c4)

-- nat 1 BOX(2;1403): 8 steps
lem-nat-1-BOX⟨2·1403⟩ : WsL → ⟪ (Sw12 ∷ Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·1403⟩ c4 = derive (Sw12 ∷ Bx2-1403 ∷ []) (Bx1-2403 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-203 ∷ Toff214 ∷ CCZ124 ∷ Bx1-203 ∷ []) ∷
   rw⁻ 0 (q29 c4) ∷
   rw 1 (q30 c4) ∷
   rw 2 (q31 c4) ∷
   rw 3 (q30 c4) ∷
   rw⁻ 4 (q29 c4) ∷
   rw 5 (q31 c4) ∷
   re 0 6 (Bx1-2403 ∷ []) ∷ []) Eq.refl

private
  q32 : WsL → Eqn
  q32 c4 = eqn (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) (wl0044 c4)
  q33 : WsL → Eqn
  q33 c4 = eqn (Sw12 ∷ Bx1-23 ∷ []) (Bx2-13 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·23⟩ c4)

-- nat 1 BOX(2;103): 8 steps
lem-nat-1-BOX⟨2·103⟩ : WsL → ⟪ (Sw12 ∷ Bx2-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-203 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·103⟩ c4 = derive (Sw12 ∷ Bx2-103 ∷ []) (Bx1-203 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-23 ∷ Toff201 ∷ CCZ012 ∷ Bx1-23 ∷ []) ∷
   rw⁻ 0 (q26 c4) ∷
   rw 1 (q32 c4) ∷
   rw 2 (q33 c4) ∷
   rw 3 (q32 c4) ∷
   rw⁻ 4 (q26 c4) ∷
   rw 5 (q33 c4) ∷
   re 0 6 (Bx1-203 ∷ []) ∷ []) Eq.refl

private
  q34 : WsL → Eqn
  q34 c4 = eqn (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) (wl0095 c4)
  q35 : WsL → Eqn
  q35 c4 = eqn (Sw12 ∷ Bx2-103 ∷ []) (Bx1-203 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·103⟩ c4)

-- nat 1 BOX(1;2403): 8 steps
lem-nat-1-BOX⟨1·2403⟩ : WsL → ⟪ (Sw12 ∷ Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·2403⟩ c4 = derive (Sw12 ∷ Bx1-2403 ∷ []) (Bx2-1403 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-103 ∷ Toff124 ∷ CCZ124 ∷ Bx2-103 ∷ []) ∷
   rw⁻ 0 (q29 c4) ∷
   rw 1 (q34 c4) ∷
   rw 2 (q35 c4) ∷
   rw 3 (q34 c4) ∷
   rw⁻ 4 (q29 c4) ∷
   rw 5 (q35 c4) ∷
   re 0 6 (Bx2-1403 ∷ []) ∷ []) Eq.refl

private
  q36 : WsL → Eqn
  q36 c4 = eqn (Sw01 ∷ Sb0-2-4-3 ∷ []) (Sb0-2-4-3 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))

-- nat 0 SBOX(0;2;4;3): 2 steps
lem-nat-0-SBOX⟨0·2·4·3⟩ : WsL → ⟪ (Sw01 ∷ Sb0-2-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-4-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·2·4·3⟩ c4 = derive (Sw01 ∷ Sb0-2-4-3 ∷ []) (Sb1-2-4-3 ∷ Sw01 ∷ [])
  (rw 0 (q36 c4) ∷
   re 0 1 (Sb1-2-4-3 ∷ []) ∷ []) Eq.refl

private
  q37 : WsL → Eqn
  q37 c4 = eqn (Sw01 ∷ Sb⁻0-2-4-3 ∷ []) (Sb⁻0-2-4-3 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))

-- nat 0 SBOXd(0;2;4;3): 2 steps
lem-nat-0-SBOXd⟨0·2·4·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻0-2-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-4-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·2·4·3⟩ c4 = derive (Sw01 ∷ Sb⁻0-2-4-3 ∷ []) (Sb⁻1-2-4-3 ∷ Sw01 ∷ [])
  (rw 0 (q37 c4) ∷
   re 0 1 (Sb⁻1-2-4-3 ∷ []) ∷ []) Eq.refl

private
  q38 : WsL → Eqn
  q38 c4 = eqn (Sw01 ∷ Bx0-2134 ∷ []) (Bx1-2034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2134⟩ c4)
  q39 : WsL → Eqn
  q39 c4 = eqn (Sw01 ∷ Toff413 ∷ []) (Toff403 ∷ Sw01 ∷ []) (lem-nat-0-TOFF413 c4)
  q40 : WsL → Eqn
  q40 c4 = eqn (Sw01 ∷ Sb0-2-4-3 ∷ []) (Sb1-2-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·4·3⟩ c4)
  q41 : WsL → Eqn
  q41 c4 = eqn (Sw01 ∷ Sb⁻0-2-4-3 ∷ []) (Sb⁻1-2-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·2·4·3⟩ c4)

-- nat 0 SBOX(0;2;13;4): 7 steps
lem-nat-0-SBOX⟨0·2·13·4⟩ : WsL → ⟪ (Sw01 ∷ Sb0-2-13-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-03-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·2·13·4⟩ c4 = derive (Sw01 ∷ Sb0-2-13-4 ∷ []) (Sb1-2-03-4 ∷ Sw01 ∷ [])
  (re 1 1 (Bx0-2134 ∷ Toff413 ∷ Sb0-2-4-3 ∷ Toff413 ∷ Sb⁻0-2-4-3 ∷ []) ∷
   rw 0 (q38 c4) ∷
   rw 1 (q39 c4) ∷
   rw 2 (q40 c4) ∷
   rw 3 (q39 c4) ∷
   rw 4 (q41 c4) ∷
   re 0 5 (Sb1-2-03-4 ∷ []) ∷ []) Eq.refl

private
  q42 : WsL → Eqn
  q42 c4 = eqn (Sw01 ∷ Sb1-2-4-3 ∷ []) (Sb1-2-4-3 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))

-- nat 0 SBOX(1;2;4;3): 2 steps
lem-nat-0-SBOX⟨1·2·4·3⟩ : WsL → ⟪ (Sw01 ∷ Sb1-2-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-4-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·2·4·3⟩ c4 = derive (Sw01 ∷ Sb1-2-4-3 ∷ []) (Sb0-2-4-3 ∷ Sw01 ∷ [])
  (rw 0 (q42 c4) ∷
   re 0 1 (Sb0-2-4-3 ∷ []) ∷ []) Eq.refl

private
  q43 : WsL → Eqn
  q43 c4 = eqn (Sw01 ∷ Sb⁻1-2-4-3 ∷ []) (Sb⁻1-2-4-3 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))

-- nat 0 SBOXd(1;2;4;3): 2 steps
lem-nat-0-SBOXd⟨1·2·4·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻1-2-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-4-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·2·4·3⟩ c4 = derive (Sw01 ∷ Sb⁻1-2-4-3 ∷ []) (Sb⁻0-2-4-3 ∷ Sw01 ∷ [])
  (rw 0 (q43 c4) ∷
   re 0 1 (Sb⁻0-2-4-3 ∷ []) ∷ []) Eq.refl

private
  q44 : WsL → Eqn
  q44 c4 = eqn (Sw01 ∷ Bx1-2034 ∷ []) (Bx0-2134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2034⟩ c4)
  q45 : WsL → Eqn
  q45 c4 = eqn (Sw01 ∷ Toff403 ∷ []) (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4)
  q46 : WsL → Eqn
  q46 c4 = eqn (Sw01 ∷ Sb1-2-4-3 ∷ []) (Sb0-2-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·4·3⟩ c4)
  q47 : WsL → Eqn
  q47 c4 = eqn (Sw01 ∷ Sb⁻1-2-4-3 ∷ []) (Sb⁻0-2-4-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·2·4·3⟩ c4)

-- nat 0 SBOX(1;2;03;4): 7 steps
lem-nat-0-SBOX⟨1·2·03·4⟩ : WsL → ⟪ (Sw01 ∷ Sb1-2-03-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-13-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·2·03·4⟩ c4 = derive (Sw01 ∷ Sb1-2-03-4 ∷ []) (Sb0-2-13-4 ∷ Sw01 ∷ [])
  (re 1 1 (Bx1-2034 ∷ Toff403 ∷ Sb1-2-4-3 ∷ Toff403 ∷ Sb⁻1-2-4-3 ∷ []) ∷
   rw 0 (q44 c4) ∷
   rw 1 (q45 c4) ∷
   rw 2 (q46 c4) ∷
   rw 3 (q45 c4) ∷
   rw 4 (q47 c4) ∷
   re 0 5 (Sb0-2-13-4 ∷ []) ∷ []) Eq.refl

private
  q48 : WsL → Eqn
  q48 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0008 c4)

-- nat 1 SBOX(0;1;4;3): 3 steps
lem-nat-1-SBOX⟨0·1·4·3⟩ : WsL → ⟪ (Sw12 ∷ Sb0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-4-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·1·4·3⟩ c4 = derive (Sw12 ∷ Sb0-1-4-3 ∷ []) (Sb0-2-4-3 ∷ Sw12 ∷ [])
  (re 1 1 (CS14 ∷ []) ∷
   rw⁻ 0 (q48 c4) ∷
   re 0 1 (Sb0-2-4-3 ∷ []) ∷ []) Eq.refl

private
  q49 : WsL → Eqn
  q49 c4 = eqn (CS24⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS14⁻ ∷ []) (wl0009 c4)

-- nat 1 SBOXd(0;1;4;3): 3 steps
lem-nat-1-SBOXd⟨0·1·4·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻0-1-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-4-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·1·4·3⟩ c4 = derive (Sw12 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-2-4-3 ∷ Sw12 ∷ [])
  (re 1 1 (CS14⁻ ∷ []) ∷
   rw⁻ 0 (q49 c4) ∷
   re 0 1 (Sb⁻0-2-4-3 ∷ []) ∷ []) Eq.refl

private
  q50 : WsL → Eqn
  q50 c4 = eqn (Sw12 ∷ Bx0-1234 ∷ []) (Bx0-2134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1234⟩ c4)
  q51 : WsL → Eqn
  q51 c4 = eqn (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) (wl0091 c4)
  q52 : WsL → Eqn
  q52 c4 = eqn (Sw12 ∷ Sb0-1-4-3 ∷ []) (Sb0-2-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·4·3⟩ c4)
  q53 : WsL → Eqn
  q53 c4 = eqn (Sw12 ∷ Sb⁻0-1-4-3 ∷ []) (Sb⁻0-2-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·1·4·3⟩ c4)

-- nat 1 SBOX(0;1;23;4): 7 steps
lem-nat-1-SBOX⟨0·1·23·4⟩ : WsL → ⟪ (Sw12 ∷ Sb0-1-23-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-13-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·1·23·4⟩ c4 = derive (Sw12 ∷ Sb0-1-23-4 ∷ []) (Sb0-2-13-4 ∷ Sw12 ∷ [])
  (re 1 1 (Bx0-1234 ∷ Toff423 ∷ Sb0-1-4-3 ∷ Toff423 ∷ Sb⁻0-1-4-3 ∷ []) ∷
   rw 0 (q50 c4) ∷
   rw 1 (q51 c4) ∷
   rw 2 (q52 c4) ∷
   rw 3 (q51 c4) ∷
   rw 4 (q53 c4) ∷
   re 0 5 (Sb0-2-13-4 ∷ []) ∷ []) Eq.refl

private
  q54 : WsL → Eqn
  q54 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl0017 c4)

-- nat 1 SBOX(0;2;4;3): 3 steps
lem-nat-1-SBOX⟨0·2·4·3⟩ : WsL → ⟪ (Sw12 ∷ Sb0-2-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-4-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·2·4·3⟩ c4 = derive (Sw12 ∷ Sb0-2-4-3 ∷ []) (Sb0-1-4-3 ∷ Sw12 ∷ [])
  (re 1 1 (CS24 ∷ []) ∷
   rw⁻ 0 (q54 c4) ∷
   re 0 1 (Sb0-1-4-3 ∷ []) ∷ []) Eq.refl

private
  q55 : WsL → Eqn
  q55 c4 = eqn (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ []) (wl0018 c4)

-- nat 1 SBOXd(0;2;4;3): 3 steps
lem-nat-1-SBOXd⟨0·2·4·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻0-2-4-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-4-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·2·4·3⟩ c4 = derive (Sw12 ∷ Sb⁻0-2-4-3 ∷ []) (Sb⁻0-1-4-3 ∷ Sw12 ∷ [])
  (re 1 1 (CS24⁻ ∷ []) ∷
   rw⁻ 0 (q55 c4) ∷
   re 0 1 (Sb⁻0-1-4-3 ∷ []) ∷ []) Eq.refl

private
  q56 : WsL → Eqn
  q56 c4 = eqn (Sw12 ∷ Bx0-2134 ∷ []) (Bx0-1234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2134⟩ c4)
  q57 : WsL → Eqn
  q57 c4 = eqn (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) (wl0085 c4)
  q58 : WsL → Eqn
  q58 c4 = eqn (Sw12 ∷ Sb0-2-4-3 ∷ []) (Sb0-1-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·4·3⟩ c4)
  q59 : WsL → Eqn
  q59 c4 = eqn (Sw12 ∷ Sb⁻0-2-4-3 ∷ []) (Sb⁻0-1-4-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·2·4·3⟩ c4)

-- nat 1 SBOX(0;2;13;4): 7 steps
lem-nat-1-SBOX⟨0·2·13·4⟩ : WsL → ⟪ (Sw12 ∷ Sb0-2-13-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-23-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·2·13·4⟩ c4 = derive (Sw12 ∷ Sb0-2-13-4 ∷ []) (Sb0-1-23-4 ∷ Sw12 ∷ [])
  (re 1 1 (Bx0-2134 ∷ Toff413 ∷ Sb0-2-4-3 ∷ Toff413 ∷ Sb⁻0-2-4-3 ∷ []) ∷
   rw 0 (q56 c4) ∷
   rw 1 (q57 c4) ∷
   rw 2 (q58 c4) ∷
   rw 3 (q57 c4) ∷
   rw 4 (q59 c4) ∷
   re 0 5 (Sb0-1-23-4 ∷ []) ∷ []) Eq.refl

private
  q60 : WsL → Eqn
  q60 c4 = eqn (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) (wl0019 c4)

-- nat 0 SBOX(2;1;3;0): 3 steps
lem-nat-0-SBOX⟨2·1·3·0⟩ : WsL → ⟪ (Sw01 ∷ Sb2-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·1·3·0⟩ c4 = derive (Sw01 ∷ Sb2-1-3-0 ∷ []) (Sb2-0-3-1 ∷ Sw01 ∷ [])
  (re 1 1 (CS13 ∷ []) ∷
   rw⁻ 0 (q60 c4) ∷
   re 0 1 (Sb2-0-3-1 ∷ []) ∷ []) Eq.refl

private
  q61 : WsL → Eqn
  q61 c4 = eqn (CS03⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS13⁻ ∷ []) (wl0022 c4)

-- nat 0 SBOXd(2;1;3;0): 3 steps
lem-nat-0-SBOXd⟨2·1·3·0⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·1·3·0⟩ c4 = derive (Sw01 ∷ Sb⁻2-1-3-0 ∷ []) (Sb⁻2-0-3-1 ∷ Sw01 ∷ [])
  (re 1 1 (CS13⁻ ∷ []) ∷
   rw⁻ 0 (q61 c4) ∷
   re 0 1 (Sb⁻2-0-3-1 ∷ []) ∷ []) Eq.refl

private
  q62 : WsL → Eqn
  q62 c4 = eqn (Sw01 ∷ Bx2-1403 ∷ []) (Bx2-0413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·1403⟩ c4)
  q63 : WsL → Eqn
  q63 c4 = eqn (Sw01 ∷ Toff304 ∷ []) (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4)
  q64 : WsL → Eqn
  q64 c4 = eqn (Sw01 ∷ Sb2-1-3-0 ∷ []) (Sb2-0-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·3·0⟩ c4)
  q65 : WsL → Eqn
  q65 c4 = eqn (Sw01 ∷ Sb⁻2-1-3-0 ∷ []) (Sb⁻2-0-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·1·3·0⟩ c4)

-- nat 0 SBOX(2;1;40;3): 7 steps
lem-nat-0-SBOX⟨2·1·40·3⟩ : WsL → ⟪ (Sw01 ∷ Sb2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·1·40·3⟩ c4 = derive (Sw01 ∷ Sb2-1-40-3 ∷ []) (Sb2-0-41-3 ∷ Sw01 ∷ [])
  (re 1 1 (Bx2-1403 ∷ Toff304 ∷ Sb2-1-3-0 ∷ Toff304 ∷ Sb⁻2-1-3-0 ∷ []) ∷
   rw 0 (q62 c4) ∷
   rw 1 (q63 c4) ∷
   rw 2 (q64 c4) ∷
   rw 3 (q63 c4) ∷
   rw 4 (q65 c4) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q66 : WsL → Eqn
  q66 c4 = eqn (CZ12 ∷ Sw01 ∷ []) (Sw01 ∷ CZ02 ∷ []) (wl0137 c4)

-- nat 0 BOX(3;02): 3 steps
lem-nat-0-BOX⟨3·02⟩ : WsL → ⟪ (Sw01 ∷ Bx3-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-12 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·02⟩ c4 = derive (Sw01 ∷ Bx3-02 ∷ []) (Bx3-12 ∷ Sw01 ∷ [])
  (re 1 1 (CZ02 ∷ []) ∷
   rw⁻ 0 (q66 c4) ∷
   re 0 1 (Bx3-12 ∷ []) ∷ []) Eq.refl

private
  q67 : WsL → Eqn
  q67 c4 = eqn (CCZ013 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ013 ∷ []) (wl0100 c4)
  q68 : WsL → Eqn
  q68 c4 = eqn (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) (wl0101 c4)
  q69 : WsL → Eqn
  q69 c4 = eqn (Sw01 ∷ Bx3-02 ∷ []) (Bx3-12 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·02⟩ c4)

-- nat 0 BOX(0;312): 8 steps
lem-nat-0-BOX⟨0·312⟩ : WsL → ⟪ (Sw01 ∷ Bx0-312 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-302 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·312⟩ c4 = derive (Sw01 ∷ Bx0-312 ∷ []) (Bx1-302 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) ∷
   rw⁻ 0 (q67 c4) ∷
   rw 1 (q68 c4) ∷
   rw 2 (q69 c4) ∷
   rw 3 (q68 c4) ∷
   rw⁻ 4 (q67 c4) ∷
   rw 5 (q69 c4) ∷
   re 0 6 (Bx1-302 ∷ []) ∷ []) Eq.refl

private
  q70 : WsL → Eqn
  q70 c4 = eqn (Sw01 ∷ CCZ034 ∷ []) (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4)
  q71 : WsL → Eqn
  q71 c4 = eqn (Sw01 ∷ Bx0-312 ∷ []) (Bx1-302 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·312⟩ c4)

-- nat 0 BOX(3;0412): 8 steps
lem-nat-0-BOX⟨3·0412⟩ : WsL → ⟪ (Sw01 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·0412⟩ c4 = derive (Sw01 ∷ Bx3-0412 ∷ []) (Bx3-1402 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) ∷
   rw 0 (q70 c4) ∷
   rw 1 (q63 c4) ∷
   rw 2 (q71 c4) ∷
   rw 3 (q63 c4) ∷
   rw 4 (q70 c4) ∷
   rw 5 (q71 c4) ∷
   re 0 6 (Bx3-1402 ∷ []) ∷ []) Eq.refl

private
  q72 : WsL → Eqn
  q72 c4 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wl0138 c4)

-- nat 0 SBOX(3;0;2;1): 3 steps
lem-nat-0-SBOX⟨3·0·2·1⟩ : WsL → ⟪ (Sw01 ∷ Sb3-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-2-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·0·2·1⟩ c4 = derive (Sw01 ∷ Sb3-0-2-1 ∷ []) (Sb3-1-2-0 ∷ Sw01 ∷ [])
  (re 1 1 (CS02 ∷ []) ∷
   rw⁻ 0 (q72 c4) ∷
   re 0 1 (Sb3-1-2-0 ∷ []) ∷ []) Eq.refl

private
  q73 : WsL → Eqn
  q73 c4 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wl0139 c4)

-- nat 0 SBOXd(3;0;2;1): 3 steps
lem-nat-0-SBOXd⟨3·0·2·1⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻3-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-1-2-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨3·0·2·1⟩ c4 = derive (Sw01 ∷ Sb⁻3-0-2-1 ∷ []) (Sb⁻3-1-2-0 ∷ Sw01 ∷ [])
  (re 1 1 (CS02⁻ ∷ []) ∷
   rw⁻ 0 (q73 c4) ∷
   re 0 1 (Sb⁻3-1-2-0 ∷ []) ∷ []) Eq.refl

private
  q74 : WsL → Eqn
  q74 c4 = eqn (Sw01 ∷ Bx3-0412 ∷ []) (Bx3-1402 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·0412⟩ c4)
  q75 : WsL → Eqn
  q75 c4 = eqn (Sw01 ∷ Toff214 ∷ []) (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4)
  q76 : WsL → Eqn
  q76 c4 = eqn (Sw01 ∷ Sb3-0-2-1 ∷ []) (Sb3-1-2-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·0·2·1⟩ c4)
  q77 : WsL → Eqn
  q77 c4 = eqn (Sw01 ∷ Sb⁻3-0-2-1 ∷ []) (Sb⁻3-1-2-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨3·0·2·1⟩ c4)

-- nat 0 SBOX(3;0;41;2): 7 steps
lem-nat-0-SBOX⟨3·0·41·2⟩ : WsL → ⟪ (Sw01 ∷ Sb3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-40-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·0·41·2⟩ c4 = derive (Sw01 ∷ Sb3-0-41-2 ∷ []) (Sb3-1-40-2 ∷ Sw01 ∷ [])
  (re 1 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   rw 0 (q74 c4) ∷
   rw 1 (q75 c4) ∷
   rw 2 (q76 c4) ∷
   rw 3 (q75 c4) ∷
   rw 4 (q77 c4) ∷
   re 0 5 (Sb3-1-40-2 ∷ []) ∷ []) Eq.refl

private
  q78 : WsL → Eqn
  q78 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl0024 c4)

-- nat 1 SBOX(1;2;3;0): 3 steps
lem-nat-1-SBOX⟨1·2·3·0⟩ : WsL → ⟪ (Sw12 ∷ Sb1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·2·3·0⟩ c4 = derive (Sw12 ∷ Sb1-2-3-0 ∷ []) (Sb2-1-3-0 ∷ Sw12 ∷ [])
  (re 1 1 (CS23 ∷ []) ∷
   rw⁻ 0 (q78 c4) ∷
   re 0 1 (Sb2-1-3-0 ∷ []) ∷ []) Eq.refl

private
  q79 : WsL → Eqn
  q79 c4 = eqn (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) (wl0043 c4)

-- nat 1 SBOXd(1;2;3;0): 3 steps
lem-nat-1-SBOXd⟨1·2·3·0⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·2·3·0⟩ c4 = derive (Sw12 ∷ Sb⁻1-2-3-0 ∷ []) (Sb⁻2-1-3-0 ∷ Sw12 ∷ [])
  (re 1 1 (CS23⁻ ∷ []) ∷
   rw⁻ 0 (q79 c4) ∷
   re 0 1 (Sb⁻2-1-3-0 ∷ []) ∷ []) Eq.refl

private
  q80 : WsL → Eqn
  q80 c4 = eqn (Sw12 ∷ Bx1-2403 ∷ []) (Bx2-1403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·2403⟩ c4)
  q81 : WsL → Eqn
  q81 c4 = eqn (Sw12 ∷ Toff304 ∷ []) (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4)
  q82 : WsL → Eqn
  q82 c4 = eqn (Sw12 ∷ Sb1-2-3-0 ∷ []) (Sb2-1-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·2·3·0⟩ c4)
  q83 : WsL → Eqn
  q83 c4 = eqn (Sw12 ∷ Sb⁻1-2-3-0 ∷ []) (Sb⁻2-1-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·2·3·0⟩ c4)

-- nat 1 SBOX(1;2;40;3): 7 steps
lem-nat-1-SBOX⟨1·2·40·3⟩ : WsL → ⟪ (Sw12 ∷ Sb1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-40-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·2·40·3⟩ c4 = derive (Sw12 ∷ Sb1-2-40-3 ∷ []) (Sb2-1-40-3 ∷ Sw12 ∷ [])
  (re 1 1 (Bx1-2403 ∷ Toff304 ∷ Sb1-2-3-0 ∷ Toff304 ∷ Sb⁻1-2-3-0 ∷ []) ∷
   rw 0 (q80 c4) ∷
   rw 1 (q81 c4) ∷
   rw 2 (q82 c4) ∷
   rw 3 (q81 c4) ∷
   rw 4 (q83 c4) ∷
   re 0 5 (Sb2-1-40-3 ∷ []) ∷ []) Eq.refl

private
  q84 : WsL → Eqn
  q84 c4 = eqn (CZ12 ∷ Sw12 ∷ []) (Sw12 ∷ CZ12 ∷ []) (wl0109 c4)

-- nat 1 BOX(3;12): 3 steps
lem-nat-1-BOX⟨3·12⟩ : WsL → ⟪ (Sw12 ∷ Bx3-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-21 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·12⟩ c4 = derive (Sw12 ∷ Bx3-12 ∷ []) (Bx3-21 ∷ Sw12 ∷ [])
  (re 1 1 (CZ12 ∷ []) ∷
   rw⁻ 0 (q84 c4) ∷
   re 0 1 (Bx3-21 ∷ []) ∷ []) Eq.refl

private
  q85 : WsL → Eqn
  q85 c4 = eqn (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4)
  q86 : WsL → Eqn
  q86 c4 = eqn (Sw12 ∷ Toff103 ∷ []) (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4)
  q87 : WsL → Eqn
  q87 c4 = eqn (Sw12 ∷ Bx3-12 ∷ []) (Bx3-21 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·12⟩ c4)

-- nat 1 BOX(1;302): 8 steps
lem-nat-1-BOX⟨1·302⟩ : WsL → ⟪ (Sw12 ∷ Bx1-302 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-301 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·302⟩ c4 = derive (Sw12 ∷ Bx1-302 ∷ []) (Bx2-301 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) ∷
   rw 0 (q85 c4) ∷
   rw 1 (q86 c4) ∷
   rw 2 (q87 c4) ∷
   rw 3 (q86 c4) ∷
   rw 4 (q85 c4) ∷
   rw 5 (q87 c4) ∷
   re 0 6 (Bx2-301 ∷ []) ∷ []) Eq.refl

private
  q88 : WsL → Eqn
  q88 c4 = eqn (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) (wl0084 c4)
  q89 : WsL → Eqn
  q89 c4 = eqn (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) (wl0064 c4)
  q90 : WsL → Eqn
  q90 c4 = eqn (Sw12 ∷ Bx1-302 ∷ []) (Bx2-301 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·302⟩ c4)

-- nat 1 BOX(3;1402): 8 steps
lem-nat-1-BOX⟨3·1402⟩ : WsL → ⟪ (Sw12 ∷ Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·1402⟩ c4 = derive (Sw12 ∷ Bx3-1402 ∷ []) (Bx3-2401 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-302 ∷ Toff314 ∷ CCZ134 ∷ Bx1-302 ∷ []) ∷
   rw⁻ 0 (q88 c4) ∷
   rw 1 (q89 c4) ∷
   rw 2 (q90 c4) ∷
   rw 3 (q89 c4) ∷
   rw⁻ 4 (q88 c4) ∷
   rw 5 (q90 c4) ∷
   re 0 6 (Bx3-2401 ∷ []) ∷ []) Eq.refl

private
  q91 : WsL → Eqn
  q91 c4 = eqn (CS12 ∷ Sw12 ∷ []) (Sw12 ∷ CS12 ∷ []) (wl0134 c4)

-- nat 1 SBOX(3;1;2;0): 3 steps
lem-nat-1-SBOX⟨3·1·2·0⟩ : WsL → ⟪ (Sw12 ∷ Sb3-1-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-2-1-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·1·2·0⟩ c4 = derive (Sw12 ∷ Sb3-1-2-0 ∷ []) (Sb3-2-1-0 ∷ Sw12 ∷ [])
  (re 1 1 (CS12 ∷ []) ∷
   rw⁻ 0 (q91 c4) ∷
   re 0 1 (Sb3-2-1-0 ∷ []) ∷ []) Eq.refl

private
  q92 : WsL → Eqn
  q92 c4 = eqn (CS12⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS12⁻ ∷ []) (wl0135 c4)

-- nat 1 SBOXd(3;1;2;0): 3 steps
lem-nat-1-SBOXd⟨3·1·2·0⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻3-1-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-2-1-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·1·2·0⟩ c4 = derive (Sw12 ∷ Sb⁻3-1-2-0 ∷ []) (Sb⁻3-2-1-0 ∷ Sw12 ∷ [])
  (re 1 1 (CS12⁻ ∷ []) ∷
   rw⁻ 0 (q92 c4) ∷
   re 0 1 (Sb⁻3-2-1-0 ∷ []) ∷ []) Eq.refl

private
  q93 : WsL → Eqn
  q93 c4 = eqn (Sw12 ∷ Bx3-1402 ∷ []) (Bx3-2401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·1402⟩ c4)
  q94 : WsL → Eqn
  q94 c4 = eqn (Sw12 ∷ Toff204 ∷ []) (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4)
  q95 : WsL → Eqn
  q95 c4 = eqn (Sw12 ∷ Sb3-1-2-0 ∷ []) (Sb3-2-1-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·1·2·0⟩ c4)
  q96 : WsL → Eqn
  q96 c4 = eqn (Sw12 ∷ Sb⁻3-1-2-0 ∷ []) (Sb⁻3-2-1-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·1·2·0⟩ c4)

-- nat 1 SBOX(3;1;40;2): 7 steps
lem-nat-1-SBOX⟨3·1·40·2⟩ : WsL → ⟪ (Sw12 ∷ Sb3-1-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-2-40-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·1·40·2⟩ c4 = derive (Sw12 ∷ Sb3-1-40-2 ∷ []) (Sb3-2-40-1 ∷ Sw12 ∷ [])
  (re 1 1 (Bx3-1402 ∷ Toff204 ∷ Sb3-1-2-0 ∷ Toff204 ∷ Sb⁻3-1-2-0 ∷ []) ∷
   rw 0 (q93 c4) ∷
   rw 1 (q94 c4) ∷
   rw 2 (q95 c4) ∷
   rw 3 (q94 c4) ∷
   rw 4 (q96 c4) ∷
   re 0 5 (Sb3-2-40-1 ∷ []) ∷ []) Eq.refl

private
  q97 : WsL → Eqn
  q97 c4 = eqn (CZ23 ∷ Sw23 ∷ []) (Sw23 ∷ CZ23 ∷ []) (wl0045 c4)

-- nat 2 BOX(1;32): 3 steps
lem-nat-2-BOX⟨1·32⟩ : WsL → ⟪ (Sw23 ∷ Bx1-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-23 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·32⟩ c4 = derive (Sw23 ∷ Bx1-32 ∷ []) (Bx1-23 ∷ Sw23 ∷ [])
  (re 1 1 (CZ23 ∷ []) ∷
   rw⁻ 0 (q97 c4) ∷
   re 0 1 (Bx1-23 ∷ []) ∷ []) Eq.refl

private
  q98 : WsL → Eqn
  q98 c4 = eqn (Sw23 ∷ Bx1-32 ∷ []) (Bx1-23 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·32⟩ c4)

-- nat 2 BOX(3;102): 8 steps
lem-nat-2-BOX⟨3·102⟩ : WsL → ⟪ (Sw23 ∷ Bx3-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-103 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·102⟩ c4 = derive (Sw23 ∷ Bx3-102 ∷ []) (Bx2-103 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-32 ∷ Toff301 ∷ CCZ013 ∷ Bx1-32 ∷ []) ∷
   rw 0 (q9 c4) ∷
   rw 1 (q10 c4) ∷
   rw 2 (q98 c4) ∷
   rw 3 (q10 c4) ∷
   rw 4 (q9 c4) ∷
   rw 5 (q98 c4) ∷
   re 0 6 (Bx2-103 ∷ []) ∷ []) Eq.refl

private
  q99 : WsL → Eqn
  q99 c4 = eqn (Sw23 ∷ CCZ134 ∷ []) (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4)
  q100 : WsL → Eqn
  q100 c4 = eqn (Sw23 ∷ Toff134 ∷ []) (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4)
  q101 : WsL → Eqn
  q101 c4 = eqn (Sw23 ∷ Bx3-102 ∷ []) (Bx2-103 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·102⟩ c4)

-- nat 2 BOX(1;3402): 8 steps
lem-nat-2-BOX⟨1·3402⟩ : WsL → ⟪ (Sw23 ∷ Bx1-3402 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2403 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·3402⟩ c4 = derive (Sw23 ∷ Bx1-3402 ∷ []) (Bx1-2403 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff134 ∷ Bx3-102 ∷ Toff134 ∷ CCZ134 ∷ Bx3-102 ∷ []) ∷
   rw 0 (q99 c4) ∷
   rw 1 (q100 c4) ∷
   rw 2 (q101 c4) ∷
   rw 3 (q100 c4) ∷
   rw 4 (q99 c4) ∷
   rw 5 (q101 c4) ∷
   re 0 6 (Bx1-2403 ∷ []) ∷ []) Eq.refl

private
  q102 : WsL → Eqn
  q102 c4 = eqn (CS23 ∷ Sw23 ∷ []) (Sw23 ∷ CS23 ∷ []) (wl0152 c4)

-- nat 2 SBOX(1;3;2;0): 3 steps
lem-nat-2-SBOX⟨1·3·2·0⟩ : WsL → ⟪ (Sw23 ∷ Sb1-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-3-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·3·2·0⟩ c4 = derive (Sw23 ∷ Sb1-3-2-0 ∷ []) (Sb1-2-3-0 ∷ Sw23 ∷ [])
  (re 1 1 (CS23 ∷ []) ∷
   rw⁻ 0 (q102 c4) ∷
   re 0 1 (Sb1-2-3-0 ∷ []) ∷ []) Eq.refl

private
  q103 : WsL → Eqn
  q103 c4 = eqn (CS23⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS23⁻ ∷ []) (wl0153 c4)

-- nat 2 SBOXd(1;3;2;0): 3 steps
lem-nat-2-SBOXd⟨1·3·2·0⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-3-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·3·2·0⟩ c4 = derive (Sw23 ∷ Sb⁻1-3-2-0 ∷ []) (Sb⁻1-2-3-0 ∷ Sw23 ∷ [])
  (re 1 1 (CS23⁻ ∷ []) ∷
   rw⁻ 0 (q103 c4) ∷
   re 0 1 (Sb⁻1-2-3-0 ∷ []) ∷ []) Eq.refl

private
  q104 : WsL → Eqn
  q104 c4 = eqn (Sw23 ∷ Bx1-3402 ∷ []) (Bx1-2403 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·3402⟩ c4)
  q105 : WsL → Eqn
  q105 c4 = eqn (Sw23 ∷ Toff204 ∷ []) (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4)
  q106 : WsL → Eqn
  q106 c4 = eqn (Sw23 ∷ Sb1-3-2-0 ∷ []) (Sb1-2-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·2·0⟩ c4)
  q107 : WsL → Eqn
  q107 c4 = eqn (Sw23 ∷ Sb⁻1-3-2-0 ∷ []) (Sb⁻1-2-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·3·2·0⟩ c4)

-- nat 2 SBOX(1;3;40;2): 7 steps
lem-nat-2-SBOX⟨1·3·40·2⟩ : WsL → ⟪ (Sw23 ∷ Sb1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-40-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·3·40·2⟩ c4 = derive (Sw23 ∷ Sb1-3-40-2 ∷ []) (Sb1-2-40-3 ∷ Sw23 ∷ [])
  (re 1 1 (Bx1-3402 ∷ Toff204 ∷ Sb1-3-2-0 ∷ Toff204 ∷ Sb⁻1-3-2-0 ∷ []) ∷
   rw 0 (q104 c4) ∷
   rw 1 (q105 c4) ∷
   rw 2 (q106 c4) ∷
   rw 3 (q105 c4) ∷
   rw 4 (q107 c4) ∷
   re 0 5 (Sb1-2-40-3 ∷ []) ∷ []) Eq.refl

private
  q108 : WsL → Eqn
  q108 c4 = eqn (Sw23 ∷ CZ12 ∷ []) (CZ13 ∷ Sw23 ∷ []) (lem-nat-2-CZ12 c4)

-- nat 2 BOX(3;21): 3 steps
lem-nat-2-BOX⟨3·21⟩ : WsL → ⟪ (Sw23 ∷ Bx3-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-31 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·21⟩ c4 = derive (Sw23 ∷ Bx3-21 ∷ []) (Bx2-31 ∷ Sw23 ∷ [])
  (re 1 1 (CZ12 ∷ []) ∷
   rw 0 (q108 c4) ∷
   re 0 1 (Bx2-31 ∷ []) ∷ []) Eq.refl

private
  q109 : WsL → Eqn
  q109 c4 = eqn (CCZ023 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ023 ∷ []) (wl0065 c4)
  q110 : WsL → Eqn
  q110 c4 = eqn (Sw23 ∷ Toff203 ∷ []) (Toff302 ∷ Sw23 ∷ []) (wl0090 c4)
  q111 : WsL → Eqn
  q111 c4 = eqn (Sw23 ∷ Bx3-21 ∷ []) (Bx2-31 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·21⟩ c4)

-- nat 2 BOX(2;301): 8 steps
lem-nat-2-BOX⟨2·301⟩ : WsL → ⟪ (Sw23 ∷ Bx2-301 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-201 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·301⟩ c4 = derive (Sw23 ∷ Bx2-301 ∷ []) (Bx3-201 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) ∷
   rw⁻ 0 (q109 c4) ∷
   rw 1 (q110 c4) ∷
   rw 2 (q111 c4) ∷
   rw 3 (q110 c4) ∷
   rw⁻ 4 (q109 c4) ∷
   rw 5 (q111 c4) ∷
   re 0 6 (Bx3-201 ∷ []) ∷ []) Eq.refl

private
  q112 : WsL → Eqn
  q112 c4 = eqn (CCZ234 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ234 ∷ []) (wl0086 c4)
  q113 : WsL → Eqn
  q113 c4 = eqn (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) (wl0144 c4)
  q114 : WsL → Eqn
  q114 c4 = eqn (Sw23 ∷ Bx2-301 ∷ []) (Bx3-201 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·301⟩ c4)

-- nat 2 BOX(3;2401): 8 steps
lem-nat-2-BOX⟨3·2401⟩ : WsL → ⟪ (Sw23 ∷ Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·2401⟩ c4 = derive (Sw23 ∷ Bx3-2401 ∷ []) (Bx2-3401 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-301 ∷ Toff324 ∷ CCZ234 ∷ Bx2-301 ∷ []) ∷
   rw⁻ 0 (q112 c4) ∷
   rw 1 (q113 c4) ∷
   rw 2 (q114 c4) ∷
   rw 3 (q113 c4) ∷
   rw⁻ 4 (q112 c4) ∷
   rw 5 (q114 c4) ∷
   re 0 6 (Bx2-3401 ∷ []) ∷ []) Eq.refl

private
  q115 : WsL → Eqn
  q115 c4 = eqn (Sw23 ∷ CS12 ∷ []) (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 c4)

-- nat 2 SBOX(3;2;1;0): 3 steps
lem-nat-2-SBOX⟨3·2·1·0⟩ : WsL → ⟪ (Sw23 ∷ Sb3-2-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-1-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·2·1·0⟩ c4 = derive (Sw23 ∷ Sb3-2-1-0 ∷ []) (Sb2-3-1-0 ∷ Sw23 ∷ [])
  (re 1 1 (CS12 ∷ []) ∷
   rw 0 (q115 c4) ∷
   re 0 1 (Sb2-3-1-0 ∷ []) ∷ []) Eq.refl

private
  q116 : WsL → Eqn
  q116 c4 = eqn (Sw23 ∷ CS12⁻ ∷ []) (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 c4)

-- nat 2 SBOXd(3;2;1;0): 3 steps
lem-nat-2-SBOXd⟨3·2·1·0⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻3-2-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-1-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·2·1·0⟩ c4 = derive (Sw23 ∷ Sb⁻3-2-1-0 ∷ []) (Sb⁻2-3-1-0 ∷ Sw23 ∷ [])
  (re 1 1 (CS12⁻ ∷ []) ∷
   rw 0 (q116 c4) ∷
   re 0 1 (Sb⁻2-3-1-0 ∷ []) ∷ []) Eq.refl

private
  q117 : WsL → Eqn
  q117 c4 = eqn (Sw23 ∷ Bx3-2401 ∷ []) (Bx2-3401 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·2401⟩ c4)
  q118 : WsL → Eqn
  q118 c4 = eqn (Sw23 ∷ Toff104 ∷ []) (Toff104 ∷ Sw23 ∷ []) (lem-nat-2-TOFF104 c4)
  q119 : WsL → Eqn
  q119 c4 = eqn (Sw23 ∷ Sb3-2-1-0 ∷ []) (Sb2-3-1-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·2·1·0⟩ c4)
  q120 : WsL → Eqn
  q120 c4 = eqn (Sw23 ∷ Sb⁻3-2-1-0 ∷ []) (Sb⁻2-3-1-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·2·1·0⟩ c4)

-- nat 2 SBOX(3;2;40;1): 7 steps
lem-nat-2-SBOX⟨3·2·40·1⟩ : WsL → ⟪ (Sw23 ∷ Sb3-2-40-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-40-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·2·40·1⟩ c4 = derive (Sw23 ∷ Sb3-2-40-1 ∷ []) (Sb2-3-40-1 ∷ Sw23 ∷ [])
  (re 1 1 (Bx3-2401 ∷ Toff104 ∷ Sb3-2-1-0 ∷ Toff104 ∷ Sb⁻3-2-1-0 ∷ []) ∷
   rw 0 (q117 c4) ∷
   rw 1 (q118 c4) ∷
   rw 2 (q119 c4) ∷
   rw 3 (q118 c4) ∷
   rw 4 (q120 c4) ∷
   re 0 5 (Sb2-3-40-1 ∷ []) ∷ []) Eq.refl

-- nat 3 BOX(1;42): 3 steps
lem-nat-3-BOX⟨1·42⟩ : WsL → ⟪ (Sw34 ∷ Bx1-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-32 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·42⟩ c4 = derive (Sw34 ∷ Bx1-42 ∷ []) (Bx1-32 ∷ Sw34 ∷ [])
  (re 1 1 (CZ24 ∷ []) ∷
   rw 0 (q20 c4) ∷
   re 0 1 (Bx1-32 ∷ []) ∷ []) Eq.refl

private
  q121 : WsL → Eqn
  q121 c4 = eqn (Sw34 ∷ CCZ014 ∷ []) (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4)
  q122 : WsL → Eqn
  q122 c4 = eqn (Sw34 ∷ Toff401 ∷ []) (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4)
  q123 : WsL → Eqn
  q123 c4 = eqn (Sw34 ∷ Bx1-42 ∷ []) (Bx1-32 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·42⟩ c4)

-- nat 3 BOX(4;102): 8 steps
lem-nat-3-BOX⟨4·102⟩ : WsL → ⟪ (Sw34 ∷ Bx4-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-102 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·102⟩ c4 = derive (Sw34 ∷ Bx4-102 ∷ []) (Bx3-102 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-42 ∷ Toff401 ∷ CCZ014 ∷ Bx1-42 ∷ []) ∷
   rw 0 (q121 c4) ∷
   rw 1 (q122 c4) ∷
   rw 2 (q123 c4) ∷
   rw 3 (q122 c4) ∷
   rw 4 (q121 c4) ∷
   rw 5 (q123 c4) ∷
   re 0 6 (Bx3-102 ∷ []) ∷ []) Eq.refl

private
  q124 : WsL → Eqn
  q124 c4 = eqn (CCZ134 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ134 ∷ []) (wl0154 c4)
  q125 : WsL → Eqn
  q125 c4 = eqn (Sw34 ∷ Toff134 ∷ []) (Toff134 ∷ Sw34 ∷ []) (wl0129 c4)
  q126 : WsL → Eqn
  q126 c4 = eqn (Sw34 ∷ Bx4-102 ∷ []) (Bx3-102 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·102⟩ c4)

-- nat 3 BOX(1;4302): 8 steps
lem-nat-3-BOX⟨1·4302⟩ : WsL → ⟪ (Sw34 ∷ Bx1-4302 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·4302⟩ c4 = derive (Sw34 ∷ Bx1-4302 ∷ []) (Bx1-3402 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-102 ∷ Toff134 ∷ CCZ134 ∷ Bx4-102 ∷ []) ∷
   rw⁻ 0 (q124 c4) ∷
   rw 1 (q125 c4) ∷
   rw 2 (q126 c4) ∷
   rw 3 (q125 c4) ∷
   rw⁻ 4 (q124 c4) ∷
   rw 5 (q126 c4) ∷
   re 0 6 (Bx1-3402 ∷ []) ∷ []) Eq.refl

private
  q127 : WsL → Eqn
  q127 c4 = eqn (Sw34 ∷ CS24 ∷ []) (CS23 ∷ Sw34 ∷ []) (lem-nat-3-CS24 c4)

-- nat 3 SBOX(1;4;2;0): 3 steps
lem-nat-3-SBOX⟨1·4·2·0⟩ : WsL → ⟪ (Sw34 ∷ Sb1-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-2-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·4·2·0⟩ c4 = derive (Sw34 ∷ Sb1-4-2-0 ∷ []) (Sb1-3-2-0 ∷ Sw34 ∷ [])
  (re 1 1 (CS24 ∷ []) ∷
   rw 0 (q127 c4) ∷
   re 0 1 (Sb1-3-2-0 ∷ []) ∷ []) Eq.refl

private
  q128 : WsL → Eqn
  q128 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 c4)

-- nat 3 CSd24: 2 steps
lem-nat-3-CSd24 : WsL → ⟪ (Sw34 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CSd24 c4 = derive (Sw34 ∷ CS24⁻ ∷ []) (CS23⁻ ∷ Sw34 ∷ [])
  (re 1 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 0 (q128 c4) ∷ []) Eq.refl

private
  q129 : WsL → Eqn
  q129 c4 = eqn (Sw34 ∷ CS24⁻ ∷ []) (CS23⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd24 c4)

-- nat 3 SBOXd(1;4;2;0): 3 steps
lem-nat-3-SBOXd⟨1·4·2·0⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻1-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-2-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·4·2·0⟩ c4 = derive (Sw34 ∷ Sb⁻1-4-2-0 ∷ []) (Sb⁻1-3-2-0 ∷ Sw34 ∷ [])
  (re 1 1 (CS24⁻ ∷ []) ∷
   rw 0 (q129 c4) ∷
   re 0 1 (Sb⁻1-3-2-0 ∷ []) ∷ []) Eq.refl

private
  q130 : WsL → Eqn
  q130 c4 = eqn (Sw34 ∷ Bx1-4302 ∷ []) (Bx1-3402 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·4302⟩ c4)
  q131 : WsL → Eqn
  q131 c4 = eqn (Sw34 ∷ Toff203 ∷ []) (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4)
  q132 : WsL → Eqn
  q132 c4 = eqn (Sw34 ∷ Sb1-4-2-0 ∷ []) (Sb1-3-2-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·4·2·0⟩ c4)
  q133 : WsL → Eqn
  q133 c4 = eqn (Sw34 ∷ Sb⁻1-4-2-0 ∷ []) (Sb⁻1-3-2-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·4·2·0⟩ c4)

-- nat 3 SBOX(1;4;30;2): 7 steps
lem-nat-3-SBOX⟨1·4·30·2⟩ : WsL → ⟪ (Sw34 ∷ Sb1-4-30-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-40-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·4·30·2⟩ c4 = derive (Sw34 ∷ Sb1-4-30-2 ∷ []) (Sb1-3-40-2 ∷ Sw34 ∷ [])
  (re 1 1 (Bx1-4302 ∷ Toff203 ∷ Sb1-4-2-0 ∷ Toff203 ∷ Sb⁻1-4-2-0 ∷ []) ∷
   rw 0 (q130 c4) ∷
   rw 1 (q131 c4) ∷
   rw 2 (q132 c4) ∷
   rw 3 (q131 c4) ∷
   rw 4 (q133 c4) ∷
   re 0 5 (Sb1-3-40-2 ∷ []) ∷ []) Eq.refl

private
  q134 : WsL → Eqn
  q134 c4 = eqn (Sw34 ∷ CZ13 ∷ []) (CZ14 ∷ Sw34 ∷ []) (lem-nat-3-CZ13 c4)

-- nat 3 BOX(2;31): 3 steps
lem-nat-3-BOX⟨2·31⟩ : WsL → ⟪ (Sw34 ∷ Bx2-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-41 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·31⟩ c4 = derive (Sw34 ∷ Bx2-31 ∷ []) (Bx2-41 ∷ Sw34 ∷ [])
  (re 1 1 (CZ13 ∷ []) ∷
   rw 0 (q134 c4) ∷
   re 0 1 (Bx2-41 ∷ []) ∷ []) Eq.refl

private
  q135 : WsL → Eqn
  q135 c4 = eqn (Sw34 ∷ CCZ023 ∷ []) (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4)
  q136 : WsL → Eqn
  q136 c4 = eqn (Sw34 ∷ Toff302 ∷ []) (Toff402 ∷ Sw34 ∷ []) (lem-nat-3-TOFF302 c4)
  q137 : WsL → Eqn
  q137 c4 = eqn (Sw34 ∷ Bx2-31 ∷ []) (Bx2-41 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·31⟩ c4)

-- nat 3 BOX(3;201): 8 steps
lem-nat-3-BOX⟨3·201⟩ : WsL → ⟪ (Sw34 ∷ Bx3-201 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-201 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·201⟩ c4 = derive (Sw34 ∷ Bx3-201 ∷ []) (Bx4-201 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) ∷
   rw 0 (q135 c4) ∷
   rw 1 (q136 c4) ∷
   rw 2 (q137 c4) ∷
   rw 3 (q136 c4) ∷
   rw 4 (q135 c4) ∷
   rw 5 (q137 c4) ∷
   re 0 6 (Bx4-201 ∷ []) ∷ []) Eq.refl

private
  q138 : WsL → Eqn
  q138 c4 = eqn (CCZ234 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ234 ∷ []) (wl0155 c4)
  q139 : WsL → Eqn
  q139 c4 = eqn (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) (wl0128 c4)
  q140 : WsL → Eqn
  q140 c4 = eqn (Sw34 ∷ Bx3-201 ∷ []) (Bx4-201 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·201⟩ c4)

-- nat 3 BOX(2;3401): 8 steps
lem-nat-3-BOX⟨2·3401⟩ : WsL → ⟪ (Sw34 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·3401⟩ c4 = derive (Sw34 ∷ Bx2-3401 ∷ []) (Bx2-4301 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-201 ∷ Toff234 ∷ CCZ234 ∷ Bx3-201 ∷ []) ∷
   rw⁻ 0 (q138 c4) ∷
   rw 1 (q139 c4) ∷
   rw 2 (q140 c4) ∷
   rw 3 (q139 c4) ∷
   rw⁻ 4 (q138 c4) ∷
   rw 5 (q140 c4) ∷
   re 0 6 (Bx2-4301 ∷ []) ∷ []) Eq.refl

private
  q141 : WsL → Eqn
  q141 c4 = eqn (Sw34 ∷ CS13 ∷ []) (CS14 ∷ Sw34 ∷ []) (lem-nat-3-CS13 c4)

-- nat 3 SBOX(2;3;1;0): 3 steps
lem-nat-3-SBOX⟨2·3·1·0⟩ : WsL → ⟪ (Sw34 ∷ Sb2-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-1-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·3·1·0⟩ c4 = derive (Sw34 ∷ Sb2-3-1-0 ∷ []) (Sb2-4-1-0 ∷ Sw34 ∷ [])
  (re 1 1 (CS13 ∷ []) ∷
   rw 0 (q141 c4) ∷
   re 0 1 (Sb2-4-1-0 ∷ []) ∷ []) Eq.refl

private
  q142 : WsL → Eqn
  q142 c4 = eqn (Sw34 ∷ CS13⁻ ∷ []) (CS14⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd13 c4)

-- nat 3 SBOXd(2;3;1;0): 3 steps
lem-nat-3-SBOXd⟨2·3·1·0⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻2-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-1-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·3·1·0⟩ c4 = derive (Sw34 ∷ Sb⁻2-3-1-0 ∷ []) (Sb⁻2-4-1-0 ∷ Sw34 ∷ [])
  (re 1 1 (CS13⁻ ∷ []) ∷
   rw 0 (q142 c4) ∷
   re 0 1 (Sb⁻2-4-1-0 ∷ []) ∷ []) Eq.refl

private
  q143 : WsL → Eqn
  q143 c4 = eqn (Sw34 ∷ Bx2-3401 ∷ []) (Bx2-4301 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·3401⟩ c4)
  q144 : WsL → Eqn
  q144 c4 = eqn (Sw34 ∷ Toff104 ∷ []) (Toff103 ∷ Sw34 ∷ []) (lem-nat-3-TOFF104 c4)
  q145 : WsL → Eqn
  q145 c4 = eqn (Sw34 ∷ Sb2-3-1-0 ∷ []) (Sb2-4-1-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·3·1·0⟩ c4)
  q146 : WsL → Eqn
  q146 c4 = eqn (Sw34 ∷ Sb⁻2-3-1-0 ∷ []) (Sb⁻2-4-1-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·3·1·0⟩ c4)

-- nat 3 SBOX(2;3;40;1): 7 steps
lem-nat-3-SBOX⟨2·3·40·1⟩ : WsL → ⟪ (Sw34 ∷ Sb2-3-40-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-30-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·3·40·1⟩ c4 = derive (Sw34 ∷ Sb2-3-40-1 ∷ []) (Sb2-4-30-1 ∷ Sw34 ∷ [])
  (re 1 1 (Bx2-3401 ∷ Toff104 ∷ Sb2-3-1-0 ∷ Toff104 ∷ Sb⁻2-3-1-0 ∷ []) ∷
   rw 0 (q143 c4) ∷
   rw 1 (q144 c4) ∷
   rw 2 (q145 c4) ∷
   rw 3 (q144 c4) ∷
   rw 4 (q146 c4) ∷
   re 0 5 (Sb2-4-30-1 ∷ []) ∷ []) Eq.refl

private
  q147 : WsL → Eqn
  q147 c4 = eqn (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4)
  q148 : WsL → Eqn
  q148 c4 = eqn (Sw12 ∷ Toff402 ∷ []) (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4)
  q149 : WsL → Eqn
  q149 c4 = eqn (Sw12 ∷ Bx2-41 ∷ []) (Bx1-42 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·41⟩ c4)

-- nat 1 BOX(4;201): 8 steps
lem-nat-1-BOX⟨4·201⟩ : WsL → ⟪ (Sw12 ∷ Bx4-201 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-102 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·201⟩ c4 = derive (Sw12 ∷ Bx4-201 ∷ []) (Bx4-102 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) ∷
   rw 0 (q147 c4) ∷
   rw 1 (q148 c4) ∷
   rw 2 (q149 c4) ∷
   rw 3 (q148 c4) ∷
   rw 4 (q147 c4) ∷
   rw 5 (q149 c4) ∷
   re 0 6 (Bx4-102 ∷ []) ∷ []) Eq.refl

private
  q150 : WsL → Eqn
  q150 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl0034 c4)
  q151 : WsL → Eqn
  q151 c4 = eqn (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) (wl0140 c4)
  q152 : WsL → Eqn
  q152 c4 = eqn (Sw12 ∷ Bx4-201 ∷ []) (Bx4-102 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·201⟩ c4)

-- nat 1 BOX(2;4301): 8 steps
lem-nat-1-BOX⟨2·4301⟩ : WsL → ⟪ (Sw12 ∷ Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4302 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·4301⟩ c4 = derive (Sw12 ∷ Bx2-4301 ∷ []) (Bx1-4302 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-201 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ []) ∷
   rw⁻ 0 (q150 c4) ∷
   rw 1 (q151 c4) ∷
   rw 2 (q152 c4) ∷
   rw 3 (q151 c4) ∷
   rw⁻ 4 (q150 c4) ∷
   rw 5 (q152 c4) ∷
   re 0 6 (Bx1-4302 ∷ []) ∷ []) Eq.refl

-- nat 1 SBOX(2;4;1;0): 3 steps
lem-nat-1-SBOX⟨2·4·1·0⟩ : WsL → ⟪ (Sw12 ∷ Sb2-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·4·1·0⟩ c4 = derive (Sw12 ∷ Sb2-4-1-0 ∷ []) (Sb1-4-2-0 ∷ Sw12 ∷ [])
  (re 1 1 (CS14 ∷ []) ∷
   rw⁻ 0 (q48 c4) ∷
   re 0 1 (Sb1-4-2-0 ∷ []) ∷ []) Eq.refl

-- nat 1 SBOXd(2;4;1;0): 3 steps
lem-nat-1-SBOXd⟨2·4·1·0⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·4·1·0⟩ c4 = derive (Sw12 ∷ Sb⁻2-4-1-0 ∷ []) (Sb⁻1-4-2-0 ∷ Sw12 ∷ [])
  (re 1 1 (CS14⁻ ∷ []) ∷
   rw⁻ 0 (q49 c4) ∷
   re 0 1 (Sb⁻1-4-2-0 ∷ []) ∷ []) Eq.refl

private
  q153 : WsL → Eqn
  q153 c4 = eqn (Sw12 ∷ Bx2-4301 ∷ []) (Bx1-4302 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4301⟩ c4)
  q154 : WsL → Eqn
  q154 c4 = eqn (Sw12 ∷ Sb2-4-1-0 ∷ []) (Sb1-4-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·4·1·0⟩ c4)
  q155 : WsL → Eqn
  q155 c4 = eqn (Sw12 ∷ Sb⁻2-4-1-0 ∷ []) (Sb⁻1-4-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·4·1·0⟩ c4)

-- nat 1 SBOX(2;4;30;1): 7 steps
lem-nat-1-SBOX⟨2·4·30·1⟩ : WsL → ⟪ (Sw12 ∷ Sb2-4-30-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-30-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·4·30·1⟩ c4 = derive (Sw12 ∷ Sb2-4-30-1 ∷ []) (Sb1-4-30-2 ∷ Sw12 ∷ [])
  (re 1 1 (Bx2-4301 ∷ Toff103 ∷ Sb2-4-1-0 ∷ Toff103 ∷ Sb⁻2-4-1-0 ∷ []) ∷
   rw 0 (q153 c4) ∷
   rw 1 (q86 c4) ∷
   rw 2 (q154 c4) ∷
   rw 3 (q86 c4) ∷
   rw 4 (q155 c4) ∷
   re 0 5 (Sb1-4-30-2 ∷ []) ∷ []) Eq.refl

private
  q156 : WsL → Eqn
  q156 c4 = eqn (CZ14 ∷ Sw23 ∷ []) (Sw23 ∷ CZ14 ∷ []) (wl0042 c4)

-- nat 2 BOX(3;41): 3 steps
lem-nat-2-BOX⟨3·41⟩ : WsL → ⟪ (Sw23 ∷ Bx3-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-41 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·41⟩ c4 = derive (Sw23 ∷ Bx3-41 ∷ []) (Bx2-41 ∷ Sw23 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   rw⁻ 0 (q156 c4) ∷
   re 0 1 (Bx2-41 ∷ []) ∷ []) Eq.refl

private
  q157 : WsL → Eqn
  q157 c4 = eqn (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4)
  q158 : WsL → Eqn
  q158 c4 = eqn (Sw23 ∷ Toff403 ∷ []) (Toff402 ∷ Sw23 ∷ []) (lem-nat-2-TOFF403 c4)
  q159 : WsL → Eqn
  q159 c4 = eqn (Sw23 ∷ Bx3-41 ∷ []) (Bx2-41 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·41⟩ c4)

-- nat 2 BOX(4;301): 8 steps
lem-nat-2-BOX⟨4·301⟩ : WsL → ⟪ (Sw23 ∷ Bx4-301 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-201 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·301⟩ c4 = derive (Sw23 ∷ Bx4-301 ∷ []) (Bx4-201 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) ∷
   rw 0 (q157 c4) ∷
   rw 1 (q158 c4) ∷
   rw 2 (q159 c4) ∷
   rw 3 (q158 c4) ∷
   rw 4 (q157 c4) ∷
   rw 5 (q159 c4) ∷
   re 0 6 (Bx4-201 ∷ []) ∷ []) Eq.refl

private
  q160 : WsL → Eqn
  q160 c4 = eqn (Sw23 ∷ Bx4-301 ∷ []) (Bx4-201 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·301⟩ c4)

-- nat 2 BOX(3;4201): 8 steps
lem-nat-2-BOX⟨3·4201⟩ : WsL → ⟪ (Sw23 ∷ Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·4201⟩ c4 = derive (Sw23 ∷ Bx3-4201 ∷ []) (Bx2-4301 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff324 ∷ Bx4-301 ∷ Toff324 ∷ CCZ234 ∷ Bx4-301 ∷ []) ∷
   rw⁻ 0 (q112 c4) ∷
   rw 1 (q113 c4) ∷
   rw 2 (q160 c4) ∷
   rw 3 (q113 c4) ∷
   rw⁻ 4 (q112 c4) ∷
   rw 5 (q160 c4) ∷
   re 0 6 (Bx2-4301 ∷ []) ∷ []) Eq.refl

private
  q161 : WsL → Eqn
  q161 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl0021 c4)

-- nat 2 SBOX(3;4;1;0): 3 steps
lem-nat-2-SBOX⟨3·4·1·0⟩ : WsL → ⟪ (Sw23 ∷ Sb3-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-1-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·4·1·0⟩ c4 = derive (Sw23 ∷ Sb3-4-1-0 ∷ []) (Sb2-4-1-0 ∷ Sw23 ∷ [])
  (re 1 1 (CS14 ∷ []) ∷
   rw⁻ 0 (q161 c4) ∷
   re 0 1 (Sb2-4-1-0 ∷ []) ∷ []) Eq.refl

private
  q162 : WsL → Eqn
  q162 c4 = eqn (CS14⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS14⁻ ∷ []) (wl0033 c4)

-- nat 2 SBOXd(3;4;1;0): 3 steps
lem-nat-2-SBOXd⟨3·4·1·0⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻3-4-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-1-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·4·1·0⟩ c4 = derive (Sw23 ∷ Sb⁻3-4-1-0 ∷ []) (Sb⁻2-4-1-0 ∷ Sw23 ∷ [])
  (re 1 1 (CS14⁻ ∷ []) ∷
   rw⁻ 0 (q162 c4) ∷
   re 0 1 (Sb⁻2-4-1-0 ∷ []) ∷ []) Eq.refl

private
  q163 : WsL → Eqn
  q163 c4 = eqn (Sw23 ∷ Bx3-4201 ∷ []) (Bx2-4301 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·4201⟩ c4)
  q164 : WsL → Eqn
  q164 c4 = eqn (Sw23 ∷ Toff102 ∷ []) (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4)
  q165 : WsL → Eqn
  q165 c4 = eqn (Sw23 ∷ Sb3-4-1-0 ∷ []) (Sb2-4-1-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·4·1·0⟩ c4)
  q166 : WsL → Eqn
  q166 c4 = eqn (Sw23 ∷ Sb⁻3-4-1-0 ∷ []) (Sb⁻2-4-1-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·4·1·0⟩ c4)

-- nat 2 SBOX(3;4;20;1): 7 steps
lem-nat-2-SBOX⟨3·4·20·1⟩ : WsL → ⟪ (Sw23 ∷ Sb3-4-20-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-30-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·4·20·1⟩ c4 = derive (Sw23 ∷ Sb3-4-20-1 ∷ []) (Sb2-4-30-1 ∷ Sw23 ∷ [])
  (re 1 1 (Bx3-4201 ∷ Toff102 ∷ Sb3-4-1-0 ∷ Toff102 ∷ Sb⁻3-4-1-0 ∷ []) ∷
   rw 0 (q163 c4) ∷
   rw 1 (q164 c4) ∷
   rw 2 (q165 c4) ∷
   rw 3 (q164 c4) ∷
   rw 4 (q166 c4) ∷
   re 0 5 (Sb2-4-30-1 ∷ []) ∷ []) Eq.refl

-- nat 2 BOX(1;42): 3 steps
lem-nat-2-BOX⟨1·42⟩ : WsL → ⟪ (Sw23 ∷ Bx1-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-43 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·42⟩ c4 = derive (Sw23 ∷ Bx1-42 ∷ []) (Bx1-43 ∷ Sw23 ∷ [])
  (re 1 1 (CZ24 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   re 0 1 (Bx1-43 ∷ []) ∷ []) Eq.refl

private
  q167 : WsL → Eqn
  q167 c4 = eqn (Sw23 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4)
  q168 : WsL → Eqn
  q168 c4 = eqn (Sw23 ∷ Toff401 ∷ []) (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4)
  q169 : WsL → Eqn
  q169 c4 = eqn (Sw23 ∷ Bx1-42 ∷ []) (Bx1-43 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·42⟩ c4)

-- nat 2 BOX(4;102): 8 steps
lem-nat-2-BOX⟨4·102⟩ : WsL → ⟪ (Sw23 ∷ Bx4-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-103 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·102⟩ c4 = derive (Sw23 ∷ Bx4-102 ∷ []) (Bx4-103 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-42 ∷ Toff401 ∷ CCZ014 ∷ Bx1-42 ∷ []) ∷
   rw 0 (q167 c4) ∷
   rw 1 (q168 c4) ∷
   rw 2 (q169 c4) ∷
   rw 3 (q168 c4) ∷
   rw 4 (q167 c4) ∷
   rw 5 (q169 c4) ∷
   re 0 6 (Bx4-103 ∷ []) ∷ []) Eq.refl

private
  q170 : WsL → Eqn
  q170 c4 = eqn (Sw23 ∷ Bx4-102 ∷ []) (Bx4-103 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·102⟩ c4)

-- nat 2 BOX(1;4302): 8 steps
lem-nat-2-BOX⟨1·4302⟩ : WsL → ⟪ (Sw23 ∷ Bx1-4302 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4203 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·4302⟩ c4 = derive (Sw23 ∷ Bx1-4302 ∷ []) (Bx1-4203 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-102 ∷ Toff134 ∷ CCZ134 ∷ Bx4-102 ∷ []) ∷
   rw 0 (q99 c4) ∷
   rw 1 (q100 c4) ∷
   rw 2 (q170 c4) ∷
   rw 3 (q100 c4) ∷
   rw 4 (q99 c4) ∷
   rw 5 (q170 c4) ∷
   re 0 6 (Bx1-4203 ∷ []) ∷ []) Eq.refl

private
  q171 : WsL → Eqn
  q171 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl0011 c4)

-- nat 2 SBOX(1;4;2;0): 3 steps
lem-nat-2-SBOX⟨1·4·2·0⟩ : WsL → ⟪ (Sw23 ∷ Sb1-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-3-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·4·2·0⟩ c4 = derive (Sw23 ∷ Sb1-4-2-0 ∷ []) (Sb1-4-3-0 ∷ Sw23 ∷ [])
  (re 1 1 (CS24 ∷ []) ∷
   rw⁻ 0 (q171 c4) ∷
   re 0 1 (Sb1-4-3-0 ∷ []) ∷ []) Eq.refl

private
  q172 : WsL → Eqn
  q172 c4 = eqn (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) (wl0012 c4)

-- nat 2 SBOXd(1;4;2;0): 3 steps
lem-nat-2-SBOXd⟨1·4·2·0⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-4-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-3-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·4·2·0⟩ c4 = derive (Sw23 ∷ Sb⁻1-4-2-0 ∷ []) (Sb⁻1-4-3-0 ∷ Sw23 ∷ [])
  (re 1 1 (CS24⁻ ∷ []) ∷
   rw⁻ 0 (q172 c4) ∷
   re 0 1 (Sb⁻1-4-3-0 ∷ []) ∷ []) Eq.refl

private
  q173 : WsL → Eqn
  q173 c4 = eqn (Sw23 ∷ Bx1-4302 ∷ []) (Bx1-4203 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·4302⟩ c4)
  q174 : WsL → Eqn
  q174 c4 = eqn (Sw23 ∷ Sb1-4-2-0 ∷ []) (Sb1-4-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·4·2·0⟩ c4)
  q175 : WsL → Eqn
  q175 c4 = eqn (Sw23 ∷ Sb⁻1-4-2-0 ∷ []) (Sb⁻1-4-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·4·2·0⟩ c4)

-- nat 2 SBOX(1;4;30;2): 7 steps
lem-nat-2-SBOX⟨1·4·30·2⟩ : WsL → ⟪ (Sw23 ∷ Sb1-4-30-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-20-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·4·30·2⟩ c4 = derive (Sw23 ∷ Sb1-4-30-2 ∷ []) (Sb1-4-20-3 ∷ Sw23 ∷ [])
  (re 1 1 (Bx1-4302 ∷ Toff203 ∷ Sb1-4-2-0 ∷ Toff203 ∷ Sb⁻1-4-2-0 ∷ []) ∷
   rw 0 (q173 c4) ∷
   rw 1 (q110 c4) ∷
   rw 2 (q174 c4) ∷
   rw 3 (q110 c4) ∷
   rw 4 (q175 c4) ∷
   re 0 5 (Sb1-4-20-3 ∷ []) ∷ []) Eq.refl

private
  q176 : WsL → Eqn
  q176 c4 = eqn (Sw01 ∷ CCZ134 ∷ []) (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4)
  q177 : WsL → Eqn
  q177 c4 = eqn (Sw01 ∷ Bx3-40 ∷ []) (Bx3-41 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·40⟩ c4)

-- nat 0 BOX(4;310): 8 steps
lem-nat-0-BOX⟨4·310⟩ : WsL → ⟪ (Sw01 ∷ Bx4-310 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-301 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·310⟩ c4 = derive (Sw01 ∷ Bx4-310 ∷ []) (Bx4-301 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ []) ∷
   rw 0 (q176 c4) ∷
   rw 1 (q39 c4) ∷
   rw 2 (q177 c4) ∷
   rw 3 (q39 c4) ∷
   rw 4 (q176 c4) ∷
   rw 5 (q177 c4) ∷
   re 0 6 (Bx4-301 ∷ []) ∷ []) Eq.refl

private
  q178 : WsL → Eqn
  q178 c4 = eqn (Sw01 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ))
  q179 : WsL → Eqn
  q179 c4 = eqn (Sw01 ∷ Toff324 ∷ []) (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))
  q180 : WsL → Eqn
  q180 c4 = eqn (Sw01 ∷ Bx4-310 ∷ []) (Bx4-301 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·310⟩ c4)

-- nat 0 BOX(3;4210): 8 steps
lem-nat-0-BOX⟨3·4210⟩ : WsL → ⟪ (Sw01 ∷ Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·4210⟩ c4 = derive (Sw01 ∷ Bx3-4210 ∷ []) (Bx3-4201 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff324 ∷ Bx4-310 ∷ Toff324 ∷ CCZ234 ∷ Bx4-310 ∷ []) ∷
   rw 0 (q178 c4) ∷
   rw 1 (q179 c4) ∷
   rw 2 (q180 c4) ∷
   rw 3 (q179 c4) ∷
   rw 4 (q178 c4) ∷
   rw 5 (q180 c4) ∷
   re 0 6 (Bx3-4201 ∷ []) ∷ []) Eq.refl

private
  q181 : WsL → Eqn
  q181 c4 = eqn (Sw01 ∷ CS04 ∷ []) (CS14 ∷ Sw01 ∷ []) (lem-nat-0-CS04 c4)

-- nat 0 SBOX(3;4;0;1): 3 steps
lem-nat-0-SBOX⟨3·4·0·1⟩ : WsL → ⟪ (Sw01 ∷ Sb3-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-1-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·4·0·1⟩ c4 = derive (Sw01 ∷ Sb3-4-0-1 ∷ []) (Sb3-4-1-0 ∷ Sw01 ∷ [])
  (re 1 1 (CS04 ∷ []) ∷
   rw 0 (q181 c4) ∷
   re 0 1 (Sb3-4-1-0 ∷ []) ∷ []) Eq.refl

private
  q182 : WsL → Eqn
  q182 c4 = eqn (Sw01 ∷ CS04⁻ ∷ []) (CS14⁻ ∷ Sw01 ∷ []) (lem-nat-0-CSd04 c4)

-- nat 0 SBOXd(3;4;0;1): 3 steps
lem-nat-0-SBOXd⟨3·4·0·1⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻3-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-1-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨3·4·0·1⟩ c4 = derive (Sw01 ∷ Sb⁻3-4-0-1 ∷ []) (Sb⁻3-4-1-0 ∷ Sw01 ∷ [])
  (re 1 1 (CS04⁻ ∷ []) ∷
   rw 0 (q182 c4) ∷
   re 0 1 (Sb⁻3-4-1-0 ∷ []) ∷ []) Eq.refl

private
  q183 : WsL → Eqn
  q183 c4 = eqn (Sw01 ∷ Bx3-4210 ∷ []) (Bx3-4201 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·4210⟩ c4)
  q184 : WsL → Eqn
  q184 c4 = eqn (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) (wl0099 c4)
  q185 : WsL → Eqn
  q185 c4 = eqn (Sw01 ∷ Sb3-4-0-1 ∷ []) (Sb3-4-1-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨3·4·0·1⟩ c4)
  q186 : WsL → Eqn
  q186 c4 = eqn (Sw01 ∷ Sb⁻3-4-0-1 ∷ []) (Sb⁻3-4-1-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨3·4·0·1⟩ c4)

-- nat 0 SBOX(3;4;21;0): 7 steps
lem-nat-0-SBOX⟨3·4·21·0⟩ : WsL → ⟪ (Sw01 ∷ Sb3-4-21-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-20-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·4·21·0⟩ c4 = derive (Sw01 ∷ Sb3-4-21-0 ∷ []) (Sb3-4-20-1 ∷ Sw01 ∷ [])
  (re 1 1 (Bx3-4210 ∷ Toff012 ∷ Sb3-4-0-1 ∷ Toff012 ∷ Sb⁻3-4-0-1 ∷ []) ∷
   rw 0 (q183 c4) ∷
   rw 1 (q184 c4) ∷
   rw 2 (q185 c4) ∷
   rw 3 (q184 c4) ∷
   rw 4 (q186 c4) ∷
   re 0 5 (Sb3-4-20-1 ∷ []) ∷ []) Eq.refl

private
  q187 : WsL → Eqn
  q187 c4 = eqn (Sw01 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4)
  q188 : WsL → Eqn
  q188 c4 = eqn (Sw01 ∷ Toff401 ∷ []) (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4)
  q189 : WsL → Eqn
  q189 c4 = eqn (Sw01 ∷ Bx1-43 ∷ []) (Bx0-43 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·43⟩ c4)

-- nat 0 BOX(4;103): 8 steps
lem-nat-0-BOX⟨4·103⟩ : WsL → ⟪ (Sw01 ∷ Bx4-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-013 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·103⟩ c4 = derive (Sw01 ∷ Bx4-103 ∷ []) (Bx4-013 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-43 ∷ Toff401 ∷ CCZ014 ∷ Bx1-43 ∷ []) ∷
   rw 0 (q187 c4) ∷
   rw 1 (q188 c4) ∷
   rw 2 (q189 c4) ∷
   rw 3 (q188 c4) ∷
   rw 4 (q187 c4) ∷
   rw 5 (q189 c4) ∷
   re 0 6 (Bx4-013 ∷ []) ∷ []) Eq.refl

private
  q190 : WsL → Eqn
  q190 c4 = eqn (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4)
  q191 : WsL → Eqn
  q191 c4 = eqn (Sw01 ∷ Toff124 ∷ []) (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4)
  q192 : WsL → Eqn
  q192 c4 = eqn (Sw01 ∷ Bx4-103 ∷ []) (Bx4-013 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·103⟩ c4)

-- nat 0 BOX(1;4203): 8 steps
lem-nat-0-BOX⟨1·4203⟩ : WsL → ⟪ (Sw01 ∷ Bx1-4203 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·4203⟩ c4 = derive (Sw01 ∷ Bx1-4203 ∷ []) (Bx0-4213 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-103 ∷ Toff124 ∷ CCZ124 ∷ Bx4-103 ∷ []) ∷
   rw 0 (q190 c4) ∷
   rw 1 (q191 c4) ∷
   rw 2 (q192 c4) ∷
   rw 3 (q191 c4) ∷
   rw 4 (q190 c4) ∷
   rw 5 (q192 c4) ∷
   re 0 6 (Bx0-4213 ∷ []) ∷ []) Eq.refl

private
  q193 : WsL → Eqn
  q193 c4 = eqn (Sw01 ∷ Sb1-4-3-0 ∷ []) (Sb1-4-3-0 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))

-- nat 0 SBOX(1;4;3;0): 2 steps
lem-nat-0-SBOX⟨1·4·3·0⟩ : WsL → ⟪ (Sw01 ∷ Sb1-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·4·3·0⟩ c4 = derive (Sw01 ∷ Sb1-4-3-0 ∷ []) (Sb0-4-3-1 ∷ Sw01 ∷ [])
  (rw 0 (q193 c4) ∷
   re 0 1 (Sb0-4-3-1 ∷ []) ∷ []) Eq.refl

private
  q194 : WsL → Eqn
  q194 c4 = eqn (Sw01 ∷ Sb⁻1-4-3-0 ∷ []) (Sb⁻1-4-3-0 ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑))

-- nat 0 SBOXd(1;4;3;0): 2 steps
lem-nat-0-SBOXd⟨1·4·3·0⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻1-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·4·3·0⟩ c4 = derive (Sw01 ∷ Sb⁻1-4-3-0 ∷ []) (Sb⁻0-4-3-1 ∷ Sw01 ∷ [])
  (rw 0 (q194 c4) ∷
   re 0 1 (Sb⁻0-4-3-1 ∷ []) ∷ []) Eq.refl

private
  q195 : WsL → Eqn
  q195 c4 = eqn (Sw01 ∷ Bx1-4203 ∷ []) (Bx0-4213 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·4203⟩ c4)
  q196 : WsL → Eqn
  q196 c4 = eqn (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) (wl0116 c4)
  q197 : WsL → Eqn
  q197 c4 = eqn (Sw01 ∷ Sb1-4-3-0 ∷ []) (Sb0-4-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·4·3·0⟩ c4)
  q198 : WsL → Eqn
  q198 c4 = eqn (Sw01 ∷ Sb⁻1-4-3-0 ∷ []) (Sb⁻0-4-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·4·3·0⟩ c4)

-- nat 0 SBOX(1;4;20;3): 7 steps
lem-nat-0-SBOX⟨1·4·20·3⟩ : WsL → ⟪ (Sw01 ∷ Sb1-4-20-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-21-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·4·20·3⟩ c4 = derive (Sw01 ∷ Sb1-4-20-3 ∷ []) (Sb0-4-21-3 ∷ Sw01 ∷ [])
  (re 1 1 (Bx1-4203 ∷ Toff302 ∷ Sb1-4-3-0 ∷ Toff302 ∷ Sb⁻1-4-3-0 ∷ []) ∷
   rw 0 (q195 c4) ∷
   rw 1 (q196 c4) ∷
   rw 2 (q197 c4) ∷
   rw 3 (q196 c4) ∷
   rw 4 (q198 c4) ∷
   re 0 5 (Sb0-4-21-3 ∷ []) ∷ []) Eq.refl

private
  q199 : WsL → Eqn
  q199 c4 = eqn (Sw12 ∷ CZ04 ∷ []) (CZ04 ∷ Sw12 ∷ []) (lem-nat-1-CZ04 c4)

-- nat 1 BOX(3;40): 3 steps
lem-nat-1-BOX⟨3·40⟩ : WsL → ⟪ (Sw12 ∷ Bx3-40 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-40 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·40⟩ c4 = derive (Sw12 ∷ Bx3-40 ∷ []) (Bx3-40 ∷ Sw12 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   rw 0 (q199 c4) ∷
   re 0 1 (Bx3-40 ∷ []) ∷ []) Eq.refl

private
  q200 : WsL → Eqn
  q200 c4 = eqn (Sw12 ∷ Bx3-40 ∷ []) (Bx3-40 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·40⟩ c4)

-- nat 1 BOX(4;320): 8 steps
lem-nat-1-BOX⟨4·320⟩ : WsL → ⟪ (Sw12 ∷ Bx4-320 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-310 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·320⟩ c4 = derive (Sw12 ∷ Bx4-320 ∷ []) (Bx4-310 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) ∷
   rw⁻ 0 (q150 c4) ∷
   rw 1 (q51 c4) ∷
   rw 2 (q200 c4) ∷
   rw 3 (q51 c4) ∷
   rw⁻ 4 (q150 c4) ∷
   rw 5 (q200 c4) ∷
   re 0 6 (Bx4-310 ∷ []) ∷ []) Eq.refl

private
  q201 : WsL → Eqn
  q201 c4 = eqn (Sw12 ∷ Bx4-320 ∷ []) (Bx4-310 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·320⟩ c4)

-- nat 1 BOX(3;4120): 8 steps
lem-nat-1-BOX⟨3·4120⟩ : WsL → ⟪ (Sw12 ∷ Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·4120⟩ c4 = derive (Sw12 ∷ Bx3-4120 ∷ []) (Bx3-4210 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff314 ∷ Bx4-320 ∷ Toff314 ∷ CCZ134 ∷ Bx4-320 ∷ []) ∷
   rw⁻ 0 (q88 c4) ∷
   rw 1 (q89 c4) ∷
   rw 2 (q201 c4) ∷
   rw 3 (q89 c4) ∷
   rw⁻ 4 (q88 c4) ∷
   rw 5 (q201 c4) ∷
   re 0 6 (Bx3-4210 ∷ []) ∷ []) Eq.refl

private
  q202 : WsL → Eqn
  q202 c4 = eqn (Sw12 ∷ CS04 ∷ []) (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 c4)

-- nat 1 SBOX(3;4;0;2): 3 steps
lem-nat-1-SBOX⟨3·4·0·2⟩ : WsL → ⟪ (Sw12 ∷ Sb3-4-0-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-0-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·4·0·2⟩ c4 = derive (Sw12 ∷ Sb3-4-0-2 ∷ []) (Sb3-4-0-1 ∷ Sw12 ∷ [])
  (re 1 1 (CS04 ∷ []) ∷
   rw 0 (q202 c4) ∷
   re 0 1 (Sb3-4-0-1 ∷ []) ∷ []) Eq.refl

private
  q203 : WsL → Eqn
  q203 c4 = eqn (Sw12 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd04 c4)

-- nat 1 SBOXd(3;4;0;2): 3 steps
lem-nat-1-SBOXd⟨3·4·0·2⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻3-4-0-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-0-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·4·0·2⟩ c4 = derive (Sw12 ∷ Sb⁻3-4-0-2 ∷ []) (Sb⁻3-4-0-1 ∷ Sw12 ∷ [])
  (re 1 1 (CS04⁻ ∷ []) ∷
   rw 0 (q203 c4) ∷
   re 0 1 (Sb⁻3-4-0-1 ∷ []) ∷ []) Eq.refl

private
  q204 : WsL → Eqn
  q204 c4 = eqn (Sw12 ∷ Bx3-4120 ∷ []) (Bx3-4210 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4120⟩ c4)
  q205 : WsL → Eqn
  q205 c4 = eqn (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) (wl0038 c4)
  q206 : WsL → Eqn
  q206 c4 = eqn (Sw12 ∷ Sb3-4-0-2 ∷ []) (Sb3-4-0-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·4·0·2⟩ c4)
  q207 : WsL → Eqn
  q207 c4 = eqn (Sw12 ∷ Sb⁻3-4-0-2 ∷ []) (Sb⁻3-4-0-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·4·0·2⟩ c4)

-- nat 1 SBOX(3;4;12;0): 7 steps
lem-nat-1-SBOX⟨3·4·12·0⟩ : WsL → ⟪ (Sw12 ∷ Sb3-4-12-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-21-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·4·12·0⟩ c4 = derive (Sw12 ∷ Sb3-4-12-0 ∷ []) (Sb3-4-21-0 ∷ Sw12 ∷ [])
  (re 1 1 (Bx3-4120 ∷ Toff012 ∷ Sb3-4-0-2 ∷ Toff012 ∷ Sb⁻3-4-0-2 ∷ []) ∷
   rw 0 (q204 c4) ∷
   rw 1 (q205 c4) ∷
   rw 2 (q206 c4) ∷
   rw 3 (q205 c4) ∷
   rw 4 (q207 c4) ∷
   re 0 5 (Sb3-4-21-0 ∷ []) ∷ []) Eq.refl

private
  q208 : WsL → Eqn
  q208 c4 = eqn (Sw12 ∷ CCZ014 ∷ []) (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4)
  q209 : WsL → Eqn
  q209 c4 = eqn (Sw12 ∷ Toff401 ∷ []) (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4)
  q210 : WsL → Eqn
  q210 c4 = eqn (Sw12 ∷ Bx0-43 ∷ []) (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ))

-- nat 1 BOX(4;013): 8 steps
lem-nat-1-BOX⟨4·013⟩ : WsL → ⟪ (Sw12 ∷ Bx4-013 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-023 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·013⟩ c4 = derive (Sw12 ∷ Bx4-013 ∷ []) (Bx4-023 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) ∷
   rw 0 (q208 c4) ∷
   rw 1 (q209 c4) ∷
   rw 2 (q210 c4) ∷
   rw 3 (q209 c4) ∷
   rw 4 (q208 c4) ∷
   rw 5 (q210 c4) ∷
   re 0 6 (Bx4-023 ∷ []) ∷ []) Eq.refl

private
  q211 : WsL → Eqn
  q211 c4 = eqn (Sw12 ∷ Toff024 ∷ []) (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4)
  q212 : WsL → Eqn
  q212 c4 = eqn (Sw12 ∷ Bx4-013 ∷ []) (Bx4-023 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·013⟩ c4)

-- nat 1 BOX(0;4213): 8 steps
lem-nat-1-BOX⟨0·4213⟩ : WsL → ⟪ (Sw12 ∷ Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·4213⟩ c4 = derive (Sw12 ∷ Bx0-4213 ∷ []) (Bx0-4123 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ Bx4-013 ∷ []) ∷
   rw 0 (q147 c4) ∷
   rw 1 (q211 c4) ∷
   rw 2 (q212 c4) ∷
   rw 3 (q211 c4) ∷
   rw 4 (q147 c4) ∷
   rw 5 (q212 c4) ∷
   re 0 6 (Bx0-4123 ∷ []) ∷ []) Eq.refl

private
  q213 : WsL → Eqn
  q213 c4 = eqn (Sw12 ∷ Sb0-4-3-1 ∷ []) (Sb0-4-3-1 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))

-- nat 1 SBOX(0;4;3;1): 2 steps
lem-nat-1-SBOX⟨0·4·3·1⟩ : WsL → ⟪ (Sw12 ∷ Sb0-4-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-3-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·4·3·1⟩ c4 = derive (Sw12 ∷ Sb0-4-3-1 ∷ []) (Sb0-4-3-2 ∷ Sw12 ∷ [])
  (rw 0 (q213 c4) ∷
   re 0 1 (Sb0-4-3-2 ∷ []) ∷ []) Eq.refl

private
  q214 : WsL → Eqn
  q214 c4 = eqn (Sw12 ∷ Sb⁻0-4-3-1 ∷ []) (Sb⁻0-4-3-1 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS))

-- nat 1 SBOXd(0;4;3;1): 2 steps
lem-nat-1-SBOXd⟨0·4·3·1⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻0-4-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-3-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·4·3·1⟩ c4 = derive (Sw12 ∷ Sb⁻0-4-3-1 ∷ []) (Sb⁻0-4-3-2 ∷ Sw12 ∷ [])
  (rw 0 (q214 c4) ∷
   re 0 1 (Sb⁻0-4-3-2 ∷ []) ∷ []) Eq.refl

private
  q215 : WsL → Eqn
  q215 c4 = eqn (Sw12 ∷ Bx0-4213 ∷ []) (Bx0-4123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·4213⟩ c4)
  q216 : WsL → Eqn
  q216 c4 = eqn (Sw12 ∷ Toff312 ∷ []) (Toff312 ∷ Sw12 ∷ []) (wl0143 c4)
  q217 : WsL → Eqn
  q217 c4 = eqn (Sw12 ∷ Sb0-4-3-1 ∷ []) (Sb0-4-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·4·3·1⟩ c4)
  q218 : WsL → Eqn
  q218 c4 = eqn (Sw12 ∷ Sb⁻0-4-3-1 ∷ []) (Sb⁻0-4-3-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·4·3·1⟩ c4)

-- nat 1 SBOX(0;4;21;3): 7 steps
lem-nat-1-SBOX⟨0·4·21·3⟩ : WsL → ⟪ (Sw12 ∷ Sb0-4-21-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-12-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·4·21·3⟩ c4 = derive (Sw12 ∷ Sb0-4-21-3 ∷ []) (Sb0-4-12-3 ∷ Sw12 ∷ [])
  (re 1 1 (Bx0-4213 ∷ Toff312 ∷ Sb0-4-3-1 ∷ Toff312 ∷ Sb⁻0-4-3-1 ∷ []) ∷
   rw 0 (q215 c4) ∷
   rw 1 (q216 c4) ∷
   rw 2 (q217 c4) ∷
   rw 3 (q216 c4) ∷
   rw 4 (q218 c4) ∷
   re 0 5 (Sb0-4-12-3 ∷ []) ∷ []) Eq.refl

private
  q219 : WsL → Eqn
  q219 c4 = eqn (CS34 ∷ Sw34 ∷ []) (Sw34 ∷ CS34 ∷ []) (wl0039 c4)

-- nat 3 SBOX(0;4;3;2): 3 steps
lem-nat-3-SBOX⟨0·4·3·2⟩ : WsL → ⟪ (Sw34 ∷ Sb0-4-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-4-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·4·3·2⟩ c4 = derive (Sw34 ∷ Sb0-4-3-2 ∷ []) (Sb0-3-4-2 ∷ Sw34 ∷ [])
  (re 1 1 (CS34 ∷ []) ∷
   rw⁻ 0 (q219 c4) ∷
   re 0 1 (Sb0-3-4-2 ∷ []) ∷ []) Eq.refl

-- nat 3 SBOX(0;3;4;2): 3 steps
lem-nat-3-SBOX⟨0·3·4·2⟩ : WsL → ⟪ (Sw34 ∷ Sb0-3-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-4-3-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·3·4·2⟩ c4 = derive (Sw34 ∷ Sb0-3-4-2 ∷ []) (Sb0-4-3-2 ∷ Sw34 ∷ [])
  (re 1 1 (CS34 ∷ []) ∷
   rw⁻ 0 (q219 c4) ∷
   re 0 1 (Sb0-4-3-2 ∷ []) ∷ []) Eq.refl

private
  q220 : WsL → Eqn
  q220 c4 = eqn (CS34⁻ ∷ Sw34 ∷ []) (Sw34 ∷ CS34⁻ ∷ []) (wl0040 c4)

-- nat 3 SBOXd(0;4;3;2): 3 steps
lem-nat-3-SBOXd⟨0·4·3·2⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻0-4-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-4-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·4·3·2⟩ c4 = derive (Sw34 ∷ Sb⁻0-4-3-2 ∷ []) (Sb⁻0-3-4-2 ∷ Sw34 ∷ [])
  (re 1 1 (CS34⁻ ∷ []) ∷
   rw⁻ 0 (q220 c4) ∷
   re 0 1 (Sb⁻0-3-4-2 ∷ []) ∷ []) Eq.refl

-- nat 3 SBOXd(0;3;4;2): 3 steps
lem-nat-3-SBOXd⟨0·3·4·2⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻0-3-4-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-4-3-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·3·4·2⟩ c4 = derive (Sw34 ∷ Sb⁻0-3-4-2 ∷ []) (Sb⁻0-4-3-2 ∷ Sw34 ∷ [])
  (re 1 1 (CS34⁻ ∷ []) ∷
   rw⁻ 0 (q220 c4) ∷
   re 0 1 (Sb⁻0-4-3-2 ∷ []) ∷ []) Eq.refl

private
  q221 : WsL → Eqn
  q221 c4 = eqn (Toff012 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS))
  q222 : WsL → Eqn
  q222 c4 = eqn (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) (wl0016 c4)

-- comm TOFF013 CSd24: 15 steps
lem-comm-TOFF013-CSd24 : WsL → ⟪ (Toff013 ∷ CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Toff013 ∷ []) ⟫ʷ
lem-comm-TOFF013-CSd24 c4 = derive (Toff013 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff013 ∷ [])
  (re 1 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q128 c4) ∷
   re 1 3 (Toff014 ∷ []) ∷
   re 1 1 (Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 7 (q128 c4) ∷
   re 5 3 (CS24⁻ ∷ []) ∷
   rw⁻ 4 (q172 c4) ∷
   rw 3 (q221 c4) ∷
   rw⁻ 2 (q222 c4) ∷
   re 2 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 1 (q128 c4) ∷
   re 2 5 (Toff014 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   rw 4 (q128 c4) ∷
   re 0 3 (CS24⁻ ∷ []) ∷ []) Eq.refl

private
  q223 : WsL → Eqn
  q223 c4 = eqn (Sw12 ∷ Toff301 ∷ []) (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4)
  q224 : WsL → Eqn
  q224 c4 = eqn (Sw12 ∷ Bx0-34 ∷ []) (Bx0-34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ))

-- nat 1 BOX(3;014): 8 steps
lem-nat-1-BOX⟨3·014⟩ : WsL → ⟪ (Sw12 ∷ Bx3-014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-024 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·014⟩ c4 = derive (Sw12 ∷ Bx3-014 ∷ []) (Bx3-024 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) ∷
   rw 0 (q85 c4) ∷
   rw 1 (q223 c4) ∷
   rw 2 (q224 c4) ∷
   rw 3 (q223 c4) ∷
   rw 4 (q85 c4) ∷
   rw 5 (q224 c4) ∷
   re 0 6 (Bx3-024 ∷ []) ∷ []) Eq.refl

private
  q225 : WsL → Eqn
  q225 c4 = eqn (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4)
  q226 : WsL → Eqn
  q226 c4 = eqn (Sw12 ∷ Toff023 ∷ []) (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4)
  q227 : WsL → Eqn
  q227 c4 = eqn (Sw12 ∷ Bx3-014 ∷ []) (Bx3-024 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·014⟩ c4)

-- nat 1 BOX(0;3214): 8 steps
lem-nat-1-BOX⟨0·3214⟩ : WsL → ⟪ (Sw12 ∷ Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·3214⟩ c4 = derive (Sw12 ∷ Bx0-3214 ∷ []) (Bx0-3124 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ []) ∷
   rw 0 (q225 c4) ∷
   rw 1 (q226 c4) ∷
   rw 2 (q227 c4) ∷
   rw 3 (q226 c4) ∷
   rw 4 (q225 c4) ∷
   rw 5 (q227 c4) ∷
   re 0 6 (Bx0-3124 ∷ []) ∷ []) Eq.refl

private
  q228 : WsL → Eqn
  q228 c4 = eqn (CX34 ∷ Sw23 ∷ []) (Sw23 ∷ CX24 ∷ []) (wl0051 c4)
  q229 : WsL → Eqn
  q229 c4 = eqn (CCZ012 ∷ CX34 ∷ []) (CX34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CX₀₁))
  q230 : WsL → Eqn
  q230 c4 = eqn (CX24 ∷ Sw23 ∷ []) (Sw23 ∷ CX34 ∷ []) (wl0050 c4)

-- comm CCZ014 CX23: 9 steps
lem-comm-CCZ014-CX23 : WsL → ⟪ (CCZ014 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ CCZ014 ∷ []) ⟫ʷ
lem-comm-CCZ014-CX23 c4 = derive (CCZ014 ∷ CX23 ∷ []) (CX23 ∷ CCZ014 ∷ [])
  (re 0 1 (Sw34 ∷ Sw23 ∷ CCZ012 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 6 (q128 c4) ∷
   re 4 3 (CX24 ∷ []) ∷
   rw⁻ 3 (q228 c4) ∷
   rw 2 (q229 c4) ∷
   rw⁻ 1 (q230 c4) ∷
   re 1 1 (Sw34 ∷ CX23 ∷ Sw34 ∷ []) ∷
   rw 0 (q128 c4) ∷
   re 1 5 (CCZ014 ∷ []) ∷ []) Eq.refl

private
  q231 : WsL → Eqn
  q231 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 c4)
  q232 : WsL → Eqn
  q232 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 c4)
  q233 : WsL → Eqn
  q233 c4 = eqn (Sw12 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS))
  q234 : WsL → Eqn
  q234 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 c4)
  q235 : WsL → Eqn
  q235 c4 = eqn (Sw01 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑))

-- resp CSd24 at 3: 6 steps
lem-resp-CSd24-at-3 : WsL → ⟪ (CS24⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS34⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CSd24-at-3 c4 = derive (CS24⁻ ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS34⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q231 c4) ∷
   rw 0 (q222 c4) ∷
   rw⁻ 2 (q232 c4) ∷
   rw⁻ 1 (q233 c4) ∷
   rw⁻ 3 (q234 c4) ∷
   rw⁻ 2 (q235 c4) ∷ []) Eq.refl

private
  q236 : WsL → Eqn
  q236 c4 = eqn (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) (wl0115 c4)
  q237 : WsL → Eqn
  q237 c4 = eqn (Sw01 ∷ Bx1-32 ∷ []) (Bx0-32 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·32⟩ c4)

-- nat 0 BOX(3;102): 8 steps
lem-nat-0-BOX⟨3·102⟩ : WsL → ⟪ (Sw01 ∷ Bx3-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-012 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·102⟩ c4 = derive (Sw01 ∷ Bx3-102 ∷ []) (Bx3-012 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-32 ∷ Toff301 ∷ CCZ013 ∷ Bx1-32 ∷ []) ∷
   rw⁻ 0 (q67 c4) ∷
   rw 1 (q236 c4) ∷
   rw 2 (q237 c4) ∷
   rw 3 (q236 c4) ∷
   rw⁻ 4 (q67 c4) ∷
   rw 5 (q237 c4) ∷
   re 0 6 (Bx3-012 ∷ []) ∷ []) Eq.refl

private
  q238 : WsL → Eqn
  q238 c4 = eqn (Sw01 ∷ Toff134 ∷ []) (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4)
  q239 : WsL → Eqn
  q239 c4 = eqn (Sw01 ∷ Bx3-102 ∷ []) (Bx3-012 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·102⟩ c4)

-- nat 0 BOX(1;3402): 8 steps
lem-nat-0-BOX⟨1·3402⟩ : WsL → ⟪ (Sw01 ∷ Bx1-3402 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·3402⟩ c4 = derive (Sw01 ∷ Bx1-3402 ∷ []) (Bx0-3412 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff134 ∷ Bx3-102 ∷ Toff134 ∷ CCZ134 ∷ Bx3-102 ∷ []) ∷
   rw 0 (q176 c4) ∷
   rw 1 (q238 c4) ∷
   rw 2 (q239 c4) ∷
   rw 3 (q238 c4) ∷
   rw 4 (q176 c4) ∷
   rw 5 (q239 c4) ∷
   re 0 6 (Bx0-3412 ∷ []) ∷ []) Eq.refl

private
  q240 : WsL → Eqn
  q240 c4 = eqn (Sw12 ∷ Toff302 ∷ []) (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4)
  q241 : WsL → Eqn
  q241 c4 = eqn (Sw12 ∷ Bx2-31 ∷ []) (Bx1-32 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·31⟩ c4)

-- nat 1 BOX(3;201): 8 steps
lem-nat-1-BOX⟨3·201⟩ : WsL → ⟪ (Sw12 ∷ Bx3-201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-102 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·201⟩ c4 = derive (Sw12 ∷ Bx3-201 ∷ []) (Bx3-102 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) ∷
   rw 0 (q225 c4) ∷
   rw 1 (q240 c4) ∷
   rw 2 (q241 c4) ∷
   rw 3 (q240 c4) ∷
   rw 4 (q225 c4) ∷
   rw 5 (q241 c4) ∷
   re 0 6 (Bx3-102 ∷ []) ∷ []) Eq.refl

private
  q242 : WsL → Eqn
  q242 c4 = eqn (Sw12 ∷ Bx3-201 ∷ []) (Bx3-102 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·201⟩ c4)

-- nat 1 BOX(2;3401): 8 steps
lem-nat-1-BOX⟨2·3401⟩ : WsL → ⟪ (Sw12 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·3401⟩ c4 = derive (Sw12 ∷ Bx2-3401 ∷ []) (Bx1-3402 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-201 ∷ Toff234 ∷ CCZ234 ∷ Bx3-201 ∷ []) ∷
   rw⁻ 0 (q150 c4) ∷
   rw 1 (q151 c4) ∷
   rw 2 (q242 c4) ∷
   rw 3 (q151 c4) ∷
   rw⁻ 4 (q150 c4) ∷
   rw 5 (q242 c4) ∷
   re 0 6 (Bx1-3402 ∷ []) ∷ []) Eq.refl

private
  q243 : WsL → Eqn
  q243 c4 = eqn (CCZ023 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ123 ∷ []) (wl0003 c4)
  q244 : WsL → Eqn
  q244 c4 = eqn (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) (wl0110 c4)
  q245 : WsL → Eqn
  q245 c4 = eqn (Sw01 ∷ Bx2-30 ∷ []) (Bx2-31 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·30⟩ c4)

-- nat 0 BOX(3;210): 8 steps
lem-nat-0-BOX⟨3·210⟩ : WsL → ⟪ (Sw01 ∷ Bx3-210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-201 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·210⟩ c4 = derive (Sw01 ∷ Bx3-210 ∷ []) (Bx3-201 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) ∷
   rw⁻ 0 (q243 c4) ∷
   rw 1 (q244 c4) ∷
   rw 2 (q245 c4) ∷
   rw 3 (q244 c4) ∷
   rw⁻ 4 (q243 c4) ∷
   rw 5 (q245 c4) ∷
   re 0 6 (Bx3-201 ∷ []) ∷ []) Eq.refl

private
  q246 : WsL → Eqn
  q246 c4 = eqn (Sw01 ∷ Toff234 ∷ []) (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff))
  q247 : WsL → Eqn
  q247 c4 = eqn (Sw01 ∷ Bx3-210 ∷ []) (Bx3-201 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·210⟩ c4)

-- nat 0 BOX(2;3410): 8 steps
lem-nat-0-BOX⟨2·3410⟩ : WsL → ⟪ (Sw01 ∷ Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·3410⟩ c4 = derive (Sw01 ∷ Bx2-3410 ∷ []) (Bx2-3401 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-210 ∷ Toff234 ∷ CCZ234 ∷ Bx3-210 ∷ []) ∷
   rw 0 (q178 c4) ∷
   rw 1 (q246 c4) ∷
   rw 2 (q247 c4) ∷
   rw 3 (q246 c4) ∷
   rw 4 (q178 c4) ∷
   rw 5 (q247 c4) ∷
   re 0 6 (Bx2-3401 ∷ []) ∷ []) Eq.refl

private
  q248 : WsL → Eqn
  q248 c4 = eqn (CZ01 ∷ Sw01 ∷ []) (Sw01 ∷ CZ01 ∷ []) (wl0130 c4)

-- nat 0 BOX(2;10): 3 steps
lem-nat-0-BOX⟨2·10⟩ : WsL → ⟪ (Sw01 ∷ Bx2-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-01 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·10⟩ c4 = derive (Sw01 ∷ Bx2-10 ∷ []) (Bx2-01 ∷ Sw01 ∷ [])
  (re 1 1 (CZ01 ∷ []) ∷
   rw⁻ 0 (q248 c4) ∷
   re 0 1 (Bx2-01 ∷ []) ∷ []) Eq.refl

private
  q249 : WsL → Eqn
  q249 c4 = eqn (Sw01 ∷ Bx0-32 ∷ []) (Bx1-32 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·32⟩ c4)

-- nat 0 BOX(3;012): 8 steps
lem-nat-0-BOX⟨3·012⟩ : WsL → ⟪ (Sw01 ∷ Bx3-012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-102 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·012⟩ c4 = derive (Sw01 ∷ Bx3-012 ∷ []) (Bx3-102 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) ∷
   rw⁻ 0 (q67 c4) ∷
   rw 1 (q236 c4) ∷
   rw 2 (q249 c4) ∷
   rw 3 (q236 c4) ∷
   rw⁻ 4 (q67 c4) ∷
   rw 5 (q249 c4) ∷
   re 0 6 (Bx3-102 ∷ []) ∷ []) Eq.refl

private
  q250 : WsL → Eqn
  q250 c4 = eqn (Sw01 ∷ Toff034 ∷ []) (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4)
  q251 : WsL → Eqn
  q251 c4 = eqn (Sw01 ∷ Bx3-012 ∷ []) (Bx3-102 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·012⟩ c4)

-- nat 0 BOX(0;3412): 8 steps
lem-nat-0-BOX⟨0·3412⟩ : WsL → ⟪ (Sw01 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·3412⟩ c4 = derive (Sw01 ∷ Bx0-3412 ∷ []) (Bx1-3402 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) ∷
   rw 0 (q70 c4) ∷
   rw 1 (q250 c4) ∷
   rw 2 (q251 c4) ∷
   rw 3 (q250 c4) ∷
   rw 4 (q70 c4) ∷
   rw 5 (q251 c4) ∷
   re 0 6 (Bx1-3402 ∷ []) ∷ []) Eq.refl

private
  q252 : WsL → Eqn
  q252 c4 = eqn (Sw12 ∷ Bx1-32 ∷ []) (Bx2-31 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·32⟩ c4)

-- nat 1 BOX(3;102): 8 steps
lem-nat-1-BOX⟨3·102⟩ : WsL → ⟪ (Sw12 ∷ Bx3-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-201 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·102⟩ c4 = derive (Sw12 ∷ Bx3-102 ∷ []) (Bx3-201 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx1-32 ∷ Toff301 ∷ CCZ013 ∷ Bx1-32 ∷ []) ∷
   rw 0 (q85 c4) ∷
   rw 1 (q223 c4) ∷
   rw 2 (q252 c4) ∷
   rw 3 (q223 c4) ∷
   rw 4 (q85 c4) ∷
   rw 5 (q252 c4) ∷
   re 0 6 (Bx3-201 ∷ []) ∷ []) Eq.refl

private
  q253 : WsL → Eqn
  q253 c4 = eqn (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) (wl0136 c4)
  q254 : WsL → Eqn
  q254 c4 = eqn (Sw12 ∷ Bx3-102 ∷ []) (Bx3-201 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·102⟩ c4)

-- nat 1 BOX(1;3402): 8 steps
lem-nat-1-BOX⟨1·3402⟩ : WsL → ⟪ (Sw12 ∷ Bx1-3402 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·3402⟩ c4 = derive (Sw12 ∷ Bx1-3402 ∷ []) (Bx2-3401 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff134 ∷ Bx3-102 ∷ Toff134 ∷ CCZ134 ∷ Bx3-102 ∷ []) ∷
   rw⁻ 0 (q88 c4) ∷
   rw 1 (q253 c4) ∷
   rw 2 (q254 c4) ∷
   rw 3 (q253 c4) ∷
   rw⁻ 4 (q88 c4) ∷
   rw 5 (q254 c4) ∷
   re 0 6 (Bx2-3401 ∷ []) ∷ []) Eq.refl

private
  q255 : WsL → Eqn
  q255 c4 = eqn (CCZ123 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ023 ∷ []) (wl0103 c4)
  q256 : WsL → Eqn
  q256 c4 = eqn (Sw01 ∷ Bx2-31 ∷ []) (Bx2-30 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·31⟩ c4)

-- nat 0 BOX(3;201): 8 steps
lem-nat-0-BOX⟨3·201⟩ : WsL → ⟪ (Sw01 ∷ Bx3-201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-210 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·201⟩ c4 = derive (Sw01 ∷ Bx3-201 ∷ []) (Bx3-210 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) ∷
   rw⁻ 0 (q255 c4) ∷
   rw 1 (q196 c4) ∷
   rw 2 (q256 c4) ∷
   rw 3 (q196 c4) ∷
   rw⁻ 4 (q255 c4) ∷
   rw 5 (q256 c4) ∷
   re 0 6 (Bx3-210 ∷ []) ∷ []) Eq.refl

private
  q257 : WsL → Eqn
  q257 c4 = eqn (Sw01 ∷ Bx3-201 ∷ []) (Bx3-210 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·201⟩ c4)

-- nat 0 BOX(2;3401): 8 steps
lem-nat-0-BOX⟨2·3401⟩ : WsL → ⟪ (Sw01 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·3401⟩ c4 = derive (Sw01 ∷ Bx2-3401 ∷ []) (Bx2-3410 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-201 ∷ Toff234 ∷ CCZ234 ∷ Bx3-201 ∷ []) ∷
   rw 0 (q178 c4) ∷
   rw 1 (q246 c4) ∷
   rw 2 (q257 c4) ∷
   rw 3 (q246 c4) ∷
   rw 4 (q178 c4) ∷
   rw 5 (q257 c4) ∷
   re 0 6 (Bx2-3410 ∷ []) ∷ []) Eq.refl

private
  q258 : WsL → Eqn
  q258 c4 = eqn (Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap))
  q259 : WsL → Eqn
  q259 c4 = eqn (CS03⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS03⁻ ∷ []) (wl0023 c4)
  q260 : WsL → Eqn
  q260 c4 = eqn (Sw01 ∷ Sw34 ∷ []) (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑))

-- resp CSd04 at 2: 12 steps
lem-resp-CSd04-at-2 : WsL → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS14⁻ ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CSd04-at-2 c4 = derive (CS04⁻ ∷ []) (Sw12 ∷ Sw01 ∷ CS14⁻ ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q232 c4) ∷
   re 0 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw⁻ 2 (q258 c4) ∷
   rw 1 (q259 c4) ∷
   rw⁻ 0 (q258 c4) ∷
   re 1 3 (CS04⁻ ∷ []) ∷
   rw⁻ 2 (q234 c4) ∷
   re 1 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw⁻ 3 (q260 c4) ∷
   rw 2 (q61 c4) ∷
   rw⁻ 1 (q260 c4) ∷
   re 2 3 (CS14⁻ ∷ []) ∷ []) Eq.refl

private
  q261 : WsL → Eqn
  q261 c4 = eqn (Sw34 ∷ CZ03 ∷ []) (CZ04 ∷ Sw34 ∷ []) (lem-nat-3-CZ03 c4)

-- nat 3 BOX(1;03): 3 steps
lem-nat-3-BOX⟨1·03⟩ : WsL → ⟪ (Sw34 ∷ Bx1-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-04 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·03⟩ c4 = derive (Sw34 ∷ Bx1-03 ∷ []) (Bx1-04 ∷ Sw34 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw 0 (q261 c4) ∷
   re 0 1 (Bx1-04 ∷ []) ∷ []) Eq.refl

private
  q262 : WsL → Eqn
  q262 c4 = eqn (Sw34 ∷ CZ04 ∷ []) (CZ03 ∷ Sw34 ∷ []) (lem-nat-3-CZ04 c4)

-- nat 3 BOX(1;04): 3 steps
lem-nat-3-BOX⟨1·04⟩ : WsL → ⟪ (Sw34 ∷ Bx1-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-03 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·04⟩ c4 = derive (Sw34 ∷ Bx1-04 ∷ []) (Bx1-03 ∷ Sw34 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   rw 0 (q262 c4) ∷
   re 0 1 (Bx1-03 ∷ []) ∷ []) Eq.refl
