{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R017 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0003 ; wl0004 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0015 ; wl0016 ; wl0017 ; wl0018 ; wl0019 ; wl0020 ; wl0021 ; wl0024 ; wl0025 ; wl0030 ; wl0034 ; wl0039 ; wl0040 ; wl0043 ; wl0046 ; wl0048 ; wl0055 ; wl0056 ; wl0057 ; wl0058 ; wl0059 ; wl0062 ; wl0065 ; wl0066 ; wl0067 ; wl0068 ; wl0086 ; wl0090 ; wl0093 ; wl0095 ; wl0103 ; wl0110 ; wl0113 ; wl0114 ; wl0116 ; wl0122 ; wl0127 ; wl0128 ; wl0132 ; wl0133 ; wl0134 ; wl0135 ; wl0140 ; wl0144 ; wl0151 ; wl0155 ; wl0166)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ024 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF034 ; lem-nat-2-TOFF102 ; lem-nat-2-TOFF103 ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ024 ; lem-nat-3-CCZ034 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF204 ; lem-nat-2-TOFF304 ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023 ; lem-nat-3-TOFF402)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ034 ; lem-nat-0-CCZ134 ; lem-nat-0-TOFF412 ; lem-nat-1-TOFF104 ; lem-nat-3-BOX⟨0·32⟩)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-TOFF204 ; lem-nat-3-TOFF301 ; lem-nat-3-TOFF302)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-2-BOX⟨2·0413⟩ ; lem-nat-2-BOX⟨3·0412⟩ ; lem-nat-2-CCZ014 ; lem-nat-2-TOFF214)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-CS01 ; lem-nat-2-CS12 ; lem-nat-2-CS13 ; lem-nat-2-CSd12 ; lem-nat-2-CSd13 ; lem-nat-2-CZ12 ; lem-nat-2-CZ13 ; lem-nat-2-TOFF314 ; lem-nat-3-CZ24)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-TOFF134 ; lem-nat-2-CS02 ; lem-nat-2-CSd02 ; lem-nat-2-TOFF124 ; lem-nat-3-CS23 ; lem-nat-3-CS24)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-TOFF034 ; lem-nat-1-CSd01 ; lem-nat-1-TOFF034 ; lem-nat-3-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-1-TOFF402 ; lem-nat-2-CS03 ; lem-nat-2-CSd03 ; lem-nat-2-TOFF401)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-nat-3-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-2-TOFF134)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-2-BOX⟨3·21⟩ ; lem-nat-3-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-nat-3-CSd23)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-nat-1-BOX⟨3·0421⟩ ; lem-nat-1-BOX⟨4·21⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-0-BOX⟨3·01⟩ ; lem-nat-0-BOX⟨3·10⟩ ; lem-nat-1-BOX⟨3·2401⟩ ; lem-nat-2-BOX⟨2·13⟩ ; lem-nat-2-BOX⟨2·31⟩)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-nat-0-BOX⟨2·0431⟩ ; lem-nat-0-SBOX⟨2·0·1·3⟩ ; lem-nat-0-SBOXd⟨2·0·1·3⟩ ; lem-nat-1-BOX⟨2·1430⟩ ; lem-nat-2-BOX⟨0·21⟩ ; lem-nat-2-BOX⟨0·31⟩)

private
  q1 : WsL → Eqn
  q1 c4 = eqn (CCZ023 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ023 ∷ []) (wl0065 c4)
  q2 : WsL → Eqn
  q2 c4 = eqn (Sw23 ∷ Toff302 ∷ []) (Toff203 ∷ Sw23 ∷ []) (wl0066 c4)
  q3 : WsL → Eqn
  q3 c4 = eqn (Sw23 ∷ Bx0-31 ∷ []) (Bx0-21 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·31⟩ c4)

-- nat 2 BOX(3;021): 8 steps
lem-nat-2-BOX⟨3·021⟩ : WsL → ⟪ (Sw23 ∷ Bx3-021 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-031 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·021⟩ c4 = derive (Sw23 ∷ Bx3-021 ∷ []) (Bx2-031 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw 5 (q3 c4) ∷
   re 0 6 (Bx2-031 ∷ []) ∷ []) Eq.refl

private
  q4 : WsL → Eqn
  q4 c4 = eqn (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4)
  q5 : WsL → Eqn
  q5 c4 = eqn (Sw23 ∷ Toff034 ∷ []) (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4)
  q6 : WsL → Eqn
  q6 c4 = eqn (Sw23 ∷ Bx3-021 ∷ []) (Bx2-031 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·021⟩ c4)

-- nat 2 BOX(0;3421): 8 steps
lem-nat-2-BOX⟨0·3421⟩ : WsL → ⟪ (Sw23 ∷ Bx0-3421 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·3421⟩ c4 = derive (Sw23 ∷ Bx0-3421 ∷ []) (Bx0-2431 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ Bx3-021 ∷ []) ∷
   rw 0 (q4 c4) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   rw 3 (q5 c4) ∷
   rw 4 (q4 c4) ∷
   rw 5 (q6 c4) ∷
   re 0 6 (Bx0-2431 ∷ []) ∷ []) Eq.refl

private
  q7 : WsL → Eqn
  q7 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl0011 c4)

-- nat 2 SBOX(1;2;4;0): 3 steps
lem-nat-2-SBOX⟨1·2·4·0⟩ : WsL → ⟪ (Sw23 ∷ Sb1-2-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-4-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·2·4·0⟩ c4 = derive (Sw23 ∷ Sb1-2-4-0 ∷ []) (Sb1-3-4-0 ∷ Sw23 ∷ [])
  (re 1 1 (CS24 ∷ []) ∷
   rw⁻ 0 (q7 c4) ∷
   re 0 1 (Sb1-3-4-0 ∷ []) ∷ []) Eq.refl

private
  q8 : WsL → Eqn
  q8 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl0015 c4)

-- nat 2 SBOX(1;3;4;0): 3 steps
lem-nat-2-SBOX⟨1·3·4·0⟩ : WsL → ⟪ (Sw23 ∷ Sb1-3-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-4-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·3·4·0⟩ c4 = derive (Sw23 ∷ Sb1-3-4-0 ∷ []) (Sb1-2-4-0 ∷ Sw23 ∷ [])
  (re 1 1 (CS34 ∷ []) ∷
   rw⁻ 0 (q8 c4) ∷
   re 0 1 (Sb1-2-4-0 ∷ []) ∷ []) Eq.refl

private
  q9 : WsL → Eqn
  q9 c4 = eqn (Sw34 ∷ CS23 ∷ []) (CS24 ∷ Sw34 ∷ []) (lem-nat-3-CS23 c4)

-- nat 3 SBOX(1;2;3;0): 3 steps
lem-nat-3-SBOX⟨1·2·3·0⟩ : WsL → ⟪ (Sw34 ∷ Sb1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-4-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·2·3·0⟩ c4 = derive (Sw34 ∷ Sb1-2-3-0 ∷ []) (Sb1-2-4-0 ∷ Sw34 ∷ [])
  (re 1 1 (CS23 ∷ []) ∷
   rw 0 (q9 c4) ∷
   re 0 1 (Sb1-2-4-0 ∷ []) ∷ []) Eq.refl

private
  q10 : WsL → Eqn
  q10 c4 = eqn (Sw34 ∷ CS24 ∷ []) (CS23 ∷ Sw34 ∷ []) (lem-nat-3-CS24 c4)

-- nat 3 SBOX(1;2;4;0): 3 steps
lem-nat-3-SBOX⟨1·2·4·0⟩ : WsL → ⟪ (Sw34 ∷ Sb1-2-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-3-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·2·4·0⟩ c4 = derive (Sw34 ∷ Sb1-2-4-0 ∷ []) (Sb1-2-3-0 ∷ Sw34 ∷ [])
  (re 1 1 (CS24 ∷ []) ∷
   rw 0 (q10 c4) ∷
   re 0 1 (Sb1-2-3-0 ∷ []) ∷ []) Eq.refl

private
  q11 : WsL → Eqn
  q11 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl0025 c4)

-- nat 1 SBOX(0;1;3;2): 3 steps
lem-nat-1-SBOX⟨0·1·3·2⟩ : WsL → ⟪ (Sw12 ∷ Sb0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-3-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·1·3·2⟩ c4 = derive (Sw12 ∷ Sb0-1-3-2 ∷ []) (Sb0-2-3-1 ∷ Sw12 ∷ [])
  (re 1 1 (CS13 ∷ []) ∷
   rw⁻ 0 (q11 c4) ∷
   re 0 1 (Sb0-2-3-1 ∷ []) ∷ []) Eq.refl

private
  q12 : WsL → Eqn
  q12 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl0024 c4)

-- nat 1 SBOX(0;2;3;1): 3 steps
lem-nat-1-SBOX⟨0·2·3·1⟩ : WsL → ⟪ (Sw12 ∷ Sb0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-3-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·2·3·1⟩ c4 = derive (Sw12 ∷ Sb0-2-3-1 ∷ []) (Sb0-1-3-2 ∷ Sw12 ∷ [])
  (re 1 1 (CS23 ∷ []) ∷
   rw⁻ 0 (q12 c4) ∷
   re 0 1 (Sb0-1-3-2 ∷ []) ∷ []) Eq.refl

private
  q13 : WsL → Eqn
  q13 c4 = eqn (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) (wl0012 c4)

-- nat 2 SBOXd(1;2;4;0): 3 steps
lem-nat-2-SBOXd⟨1·2·4·0⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-2-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-4-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·2·4·0⟩ c4 = derive (Sw23 ∷ Sb⁻1-2-4-0 ∷ []) (Sb⁻1-3-4-0 ∷ Sw23 ∷ [])
  (re 1 1 (CS24⁻ ∷ []) ∷
   rw⁻ 0 (q13 c4) ∷
   re 0 1 (Sb⁻1-3-4-0 ∷ []) ∷ []) Eq.refl

private
  q14 : WsL → Eqn
  q14 c4 = eqn (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) (wl0016 c4)

-- nat 2 SBOXd(1;3;4;0): 3 steps
lem-nat-2-SBOXd⟨1·3·4·0⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-3-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-4-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·3·4·0⟩ c4 = derive (Sw23 ∷ Sb⁻1-3-4-0 ∷ []) (Sb⁻1-2-4-0 ∷ Sw23 ∷ [])
  (re 1 1 (CS34⁻ ∷ []) ∷
   rw⁻ 0 (q14 c4) ∷
   re 0 1 (Sb⁻1-2-4-0 ∷ []) ∷ []) Eq.refl

private
  q15 : WsL → Eqn
  q15 c4 = eqn (Sw34 ∷ CS23⁻ ∷ []) (CS24⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd23 c4)

-- nat 3 SBOXd(1;2;3;0): 3 steps
lem-nat-3-SBOXd⟨1·2·3·0⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-4-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·2·3·0⟩ c4 = derive (Sw34 ∷ Sb⁻1-2-3-0 ∷ []) (Sb⁻1-2-4-0 ∷ Sw34 ∷ [])
  (re 1 1 (CS23⁻ ∷ []) ∷
   rw 0 (q15 c4) ∷
   re 0 1 (Sb⁻1-2-4-0 ∷ []) ∷ []) Eq.refl

private
  q16 : WsL → Eqn
  q16 c4 = eqn (Sw34 ∷ CS24⁻ ∷ []) (CS23⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd24 c4)

-- nat 3 SBOXd(1;2;4;0): 3 steps
lem-nat-3-SBOXd⟨1·2·4·0⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻1-2-4-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-3-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·2·4·0⟩ c4 = derive (Sw34 ∷ Sb⁻1-2-4-0 ∷ []) (Sb⁻1-2-3-0 ∷ Sw34 ∷ [])
  (re 1 1 (CS24⁻ ∷ []) ∷
   rw 0 (q16 c4) ∷
   re 0 1 (Sb⁻1-2-3-0 ∷ []) ∷ []) Eq.refl

private
  q17 : WsL → Eqn
  q17 c4 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wl0046 c4)

-- nat 1 SBOXd(0;1;3;2): 3 steps
lem-nat-1-SBOXd⟨0·1·3·2⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻0-1-3-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-3-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·1·3·2⟩ c4 = derive (Sw12 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-2-3-1 ∷ Sw12 ∷ [])
  (re 1 1 (CS13⁻ ∷ []) ∷
   rw⁻ 0 (q17 c4) ∷
   re 0 1 (Sb⁻0-2-3-1 ∷ []) ∷ []) Eq.refl

private
  q18 : WsL → Eqn
  q18 c4 = eqn (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) (wl0043 c4)

-- nat 1 SBOXd(0;2;3;1): 3 steps
lem-nat-1-SBOXd⟨0·2·3·1⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻0-2-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-3-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·2·3·1⟩ c4 = derive (Sw12 ∷ Sb⁻0-2-3-1 ∷ []) (Sb⁻0-1-3-2 ∷ Sw12 ∷ [])
  (re 1 1 (CS23⁻ ∷ []) ∷
   rw⁻ 0 (q18 c4) ∷
   re 0 1 (Sb⁻0-1-3-2 ∷ []) ∷ []) Eq.refl

private
  q19 : WsL → Eqn
  q19 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 c4)
  q20 : WsL → Eqn
  q20 c4 = eqn (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) (wl0004 c4)

-- resp TOFF203 at 1: 2 steps
lem-resp-TOFF203-at-1 : WsL → ⟪ (Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF203-at-1 c4 = derive (Toff203 ∷ []) (Sw01 ∷ Toff213 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q19 c4) ∷
   rw⁻ 0 (q20 c4) ∷ []) Eq.refl

private
  q21 : WsL → Eqn
  q21 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 c4)
  q22 : WsL → Eqn
  q22 c4 = eqn (CX14 ∷ Sw12 ∷ []) (Sw12 ∷ CX24 ∷ []) (wl0055 c4)
  q23 : WsL → Eqn
  q23 c4 = eqn (Sw01 ∷ CX24 ∷ []) (CX24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CX₀₁ • Swap ↑))

-- resp CX14 at 2: 4 steps
lem-resp-CX14-at-2 : WsL → ⟪ (CX14 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX24 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX14-at-2 c4 = derive (CX14 ∷ []) (Sw12 ∷ Sw01 ∷ CX24 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q21 c4) ∷
   rw 0 (q22 c4) ∷
   rw⁻ 2 (q19 c4) ∷
   rw⁻ 1 (q23 c4) ∷ []) Eq.refl

private
  q24 : WsL → Eqn
  q24 c4 = eqn (Sw12 ∷ CS01 ∷ []) (CS02 ∷ Sw12 ∷ []) (lem-nat-1-CS01 c4)

-- nat 1 SBOX(3;0;1;2): 3 steps
lem-nat-1-SBOX⟨3·0·1·2⟩ : WsL → ⟪ (Sw12 ∷ Sb3-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-2-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·0·1·2⟩ c4 = derive (Sw12 ∷ Sb3-0-1-2 ∷ []) (Sb3-0-2-1 ∷ Sw12 ∷ [])
  (re 1 1 (CS01 ∷ []) ∷
   rw 0 (q24 c4) ∷
   re 0 1 (Sb3-0-2-1 ∷ []) ∷ []) Eq.refl

private
  q25 : WsL → Eqn
  q25 c4 = eqn (Sw12 ∷ CS01⁻ ∷ []) (CS02⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd01 c4)

-- nat 1 SBOXd(3;0;1;2): 3 steps
lem-nat-1-SBOXd⟨3·0·1·2⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻3-0-1-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-2-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·0·1·2⟩ c4 = derive (Sw12 ∷ Sb⁻3-0-1-2 ∷ []) (Sb⁻3-0-2-1 ∷ Sw12 ∷ [])
  (re 1 1 (CS01⁻ ∷ []) ∷
   rw 0 (q25 c4) ∷
   re 0 1 (Sb⁻3-0-2-1 ∷ []) ∷ []) Eq.refl

private
  q26 : WsL → Eqn
  q26 c4 = eqn (Sw12 ∷ Bx3-0421 ∷ []) (Bx3-0412 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·0421⟩ c4)
  q27 : WsL → Eqn
  q27 c4 = eqn (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) (wl0095 c4)
  q28 : WsL → Eqn
  q28 c4 = eqn (Sw12 ∷ Sb3-0-1-2 ∷ []) (Sb3-0-2-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·0·1·2⟩ c4)
  q29 : WsL → Eqn
  q29 c4 = eqn (Sw12 ∷ Sb⁻3-0-1-2 ∷ []) (Sb⁻3-0-2-1 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·0·1·2⟩ c4)

-- nat 1 SBOX(3;0;42;1): 7 steps
lem-nat-1-SBOX⟨3·0·42·1⟩ : WsL → ⟪ (Sw12 ∷ Sb3-0-42-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·0·42·1⟩ c4 = derive (Sw12 ∷ Sb3-0-42-1 ∷ []) (Sb3-0-41-2 ∷ Sw12 ∷ [])
  (re 1 1 (Bx3-0421 ∷ Toff124 ∷ Sb3-0-1-2 ∷ Toff124 ∷ Sb⁻3-0-1-2 ∷ []) ∷
   rw 0 (q26 c4) ∷
   rw 1 (q27 c4) ∷
   rw 2 (q28 c4) ∷
   rw 3 (q27 c4) ∷
   rw 4 (q29 c4) ∷
   re 0 5 (Sb3-0-41-2 ∷ []) ∷ []) Eq.refl

private
  q30 : WsL → Eqn
  q30 c4 = eqn (Sw23 ∷ CS03 ∷ []) (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4)

-- nat 2 SBOX(2;0;3;1): 3 steps
lem-nat-2-SBOX⟨2·0·3·1⟩ : WsL → ⟪ (Sw23 ∷ Sb2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-2-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·0·3·1⟩ c4 = derive (Sw23 ∷ Sb2-0-3-1 ∷ []) (Sb3-0-2-1 ∷ Sw23 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   rw 0 (q30 c4) ∷
   re 0 1 (Sb3-0-2-1 ∷ []) ∷ []) Eq.refl

private
  q31 : WsL → Eqn
  q31 c4 = eqn (Sw23 ∷ CS03⁻ ∷ []) (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 c4)

-- nat 2 SBOXd(2;0;3;1): 3 steps
lem-nat-2-SBOXd⟨2·0·3·1⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-2-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨2·0·3·1⟩ c4 = derive (Sw23 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻3-0-2-1 ∷ Sw23 ∷ [])
  (re 1 1 (CS03⁻ ∷ []) ∷
   rw 0 (q31 c4) ∷
   re 0 1 (Sb⁻3-0-2-1 ∷ []) ∷ []) Eq.refl

private
  q32 : WsL → Eqn
  q32 c4 = eqn (Sw23 ∷ Bx2-0413 ∷ []) (Bx3-0412 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·0413⟩ c4)
  q33 : WsL → Eqn
  q33 c4 = eqn (Sw23 ∷ Toff314 ∷ []) (Toff214 ∷ Sw23 ∷ []) (lem-nat-2-TOFF314 c4)
  q34 : WsL → Eqn
  q34 c4 = eqn (Sw23 ∷ Sb2-0-3-1 ∷ []) (Sb3-0-2-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·0·3·1⟩ c4)
  q35 : WsL → Eqn
  q35 c4 = eqn (Sw23 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻3-0-2-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨2·0·3·1⟩ c4)

-- nat 2 SBOX(2;0;41;3): 7 steps
lem-nat-2-SBOX⟨2·0·41·3⟩ : WsL → ⟪ (Sw23 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·0·41·3⟩ c4 = derive (Sw23 ∷ Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ Sw23 ∷ [])
  (re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 0 (q32 c4) ∷
   rw 1 (q33 c4) ∷
   rw 2 (q34 c4) ∷
   rw 3 (q33 c4) ∷
   rw 4 (q35 c4) ∷
   re 0 5 (Sb3-0-41-2 ∷ []) ∷ []) Eq.refl

private
  q36 : WsL → Eqn
  q36 c4 = eqn (Sw23 ∷ CS02 ∷ []) (CS03 ∷ Sw23 ∷ []) (lem-nat-2-CS02 c4)

-- nat 2 SBOX(3;0;2;1): 3 steps
lem-nat-2-SBOX⟨3·0·2·1⟩ : WsL → ⟪ (Sw23 ∷ Sb3-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·0·2·1⟩ c4 = derive (Sw23 ∷ Sb3-0-2-1 ∷ []) (Sb2-0-3-1 ∷ Sw23 ∷ [])
  (re 1 1 (CS02 ∷ []) ∷
   rw 0 (q36 c4) ∷
   re 0 1 (Sb2-0-3-1 ∷ []) ∷ []) Eq.refl

private
  q37 : WsL → Eqn
  q37 c4 = eqn (Sw23 ∷ CS02⁻ ∷ []) (CS03⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd02 c4)

-- nat 2 SBOXd(3;0;2;1): 3 steps
lem-nat-2-SBOXd⟨3·0·2·1⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻3-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-3-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·0·2·1⟩ c4 = derive (Sw23 ∷ Sb⁻3-0-2-1 ∷ []) (Sb⁻2-0-3-1 ∷ Sw23 ∷ [])
  (re 1 1 (CS02⁻ ∷ []) ∷
   rw 0 (q37 c4) ∷
   re 0 1 (Sb⁻2-0-3-1 ∷ []) ∷ []) Eq.refl

private
  q38 : WsL → Eqn
  q38 c4 = eqn (Sw23 ∷ Bx3-0412 ∷ []) (Bx2-0413 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·0412⟩ c4)
  q39 : WsL → Eqn
  q39 c4 = eqn (Sw23 ∷ Toff214 ∷ []) (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4)
  q40 : WsL → Eqn
  q40 c4 = eqn (Sw23 ∷ Sb3-0-2-1 ∷ []) (Sb2-0-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·0·2·1⟩ c4)
  q41 : WsL → Eqn
  q41 c4 = eqn (Sw23 ∷ Sb⁻3-0-2-1 ∷ []) (Sb⁻2-0-3-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·0·2·1⟩ c4)

-- nat 2 SBOX(3;0;41;2): 7 steps
lem-nat-2-SBOX⟨3·0·41·2⟩ : WsL → ⟪ (Sw23 ∷ Sb3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·0·41·2⟩ c4 = derive (Sw23 ∷ Sb3-0-41-2 ∷ []) (Sb2-0-41-3 ∷ Sw23 ∷ [])
  (re 1 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   rw 0 (q38 c4) ∷
   rw 1 (q39 c4) ∷
   rw 2 (q40 c4) ∷
   rw 3 (q39 c4) ∷
   rw 4 (q41 c4) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q42 : WsL → Eqn
  q42 c4 = eqn (Sw23 ∷ CZ13 ∷ []) (CZ12 ∷ Sw23 ∷ []) (lem-nat-2-CZ13 c4)

-- nat 2 BOX(4;13): 3 steps
lem-nat-2-BOX⟨4·13⟩ : WsL → ⟪ (Sw23 ∷ Bx4-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-12 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·13⟩ c4 = derive (Sw23 ∷ Bx4-13 ∷ []) (Bx4-12 ∷ Sw23 ∷ [])
  (re 1 1 (CZ13 ∷ []) ∷
   rw 0 (q42 c4) ∷
   re 0 1 (Bx4-12 ∷ []) ∷ []) Eq.refl

private
  q43 : WsL → Eqn
  q43 c4 = eqn (Sw23 ∷ CCZ124 ∷ []) (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4)
  q44 : WsL → Eqn
  q44 c4 = eqn (Sw23 ∷ Toff124 ∷ []) (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4)
  q45 : WsL → Eqn
  q45 c4 = eqn (Sw23 ∷ Bx4-13 ∷ []) (Bx4-12 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·13⟩ c4)

-- nat 2 BOX(1;423): 8 steps
lem-nat-2-BOX⟨1·423⟩ : WsL → ⟪ (Sw23 ∷ Bx1-423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-432 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·423⟩ c4 = derive (Sw23 ∷ Bx1-423 ∷ []) (Bx1-432 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) ∷
   rw 0 (q43 c4) ∷
   rw 1 (q44 c4) ∷
   rw 2 (q45 c4) ∷
   rw 3 (q44 c4) ∷
   rw 4 (q43 c4) ∷
   rw 5 (q45 c4) ∷
   re 0 6 (Bx1-432 ∷ []) ∷ []) Eq.refl

private
  q46 : WsL → Eqn
  q46 c4 = eqn (Sw23 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4)
  q47 : WsL → Eqn
  q47 c4 = eqn (Sw23 ∷ Toff401 ∷ []) (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4)
  q48 : WsL → Eqn
  q48 c4 = eqn (Sw23 ∷ Bx1-423 ∷ []) (Bx1-432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·423⟩ c4)

-- nat 2 BOX(4;1023): 8 steps
lem-nat-2-BOX⟨4·1023⟩ : WsL → ⟪ (Sw23 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1032 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·1023⟩ c4 = derive (Sw23 ∷ Bx4-1023 ∷ []) (Bx4-1032 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ []) ∷
   rw 0 (q46 c4) ∷
   rw 1 (q47 c4) ∷
   rw 2 (q48 c4) ∷
   rw 3 (q47 c4) ∷
   rw 4 (q46 c4) ∷
   rw 5 (q48 c4) ∷
   re 0 6 (Bx4-1032 ∷ []) ∷ []) Eq.refl

private
  q49 : WsL → Eqn
  q49 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl0034 c4)
  q50 : WsL → Eqn
  q50 c4 = eqn (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) (wl0140 c4)
  q51 : WsL → Eqn
  q51 c4 = eqn (Sw12 ∷ Bx4-21 ∷ []) (Bx4-12 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·21⟩ c4)

-- nat 1 BOX(2;431): 8 steps
lem-nat-1-BOX⟨2·431⟩ : WsL → ⟪ (Sw12 ∷ Bx2-431 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-432 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·431⟩ c4 = derive (Sw12 ∷ Bx2-431 ∷ []) (Bx1-432 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) ∷
   rw⁻ 0 (q49 c4) ∷
   rw 1 (q50 c4) ∷
   rw 2 (q51 c4) ∷
   rw 3 (q50 c4) ∷
   rw⁻ 4 (q49 c4) ∷
   rw 5 (q51 c4) ∷
   re 0 6 (Bx1-432 ∷ []) ∷ []) Eq.refl

private
  q52 : WsL → Eqn
  q52 c4 = eqn (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4)
  q53 : WsL → Eqn
  q53 c4 = eqn (Sw12 ∷ Toff402 ∷ []) (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4)
  q54 : WsL → Eqn
  q54 c4 = eqn (Sw12 ∷ Bx2-431 ∷ []) (Bx1-432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·431⟩ c4)

-- nat 1 BOX(4;2031): 8 steps
lem-nat-1-BOX⟨4·2031⟩ : WsL → ⟪ (Sw12 ∷ Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1032 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·2031⟩ c4 = derive (Sw12 ∷ Bx4-2031 ∷ []) (Bx4-1032 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-431 ∷ Toff402 ∷ CCZ024 ∷ Bx2-431 ∷ []) ∷
   rw 0 (q52 c4) ∷
   rw 1 (q53 c4) ∷
   rw 2 (q54 c4) ∷
   rw 3 (q53 c4) ∷
   rw 4 (q52 c4) ∷
   rw 5 (q54 c4) ∷
   re 0 6 (Bx4-1032 ∷ []) ∷ []) Eq.refl

private
  q55 : WsL → Eqn
  q55 c4 = eqn (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ []) (wl0057 c4)
  q56 : WsL → Eqn
  q56 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 c4)
  q57 : WsL → Eqn
  q57 c4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap))
  q58 : WsL → Eqn
  q58 c4 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (c₁ (iI) (Swap ↑))
  q59 : WsL → Eqn
  q59 c4 = eqn (K4 ∷ Sw34 ∷ []) (Sw34 ∷ K3 ∷ []) (wl0067 c4)
  q60 : WsL → Eqn
  q60 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 c4)
  q61 : WsL → Eqn
  q61 c4 = eqn (CX01 ∷ Sw34 ∷ []) (Sw34 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap ↑))
  q62 : WsL → Eqn
  q62 c4 = eqn (ι ∷ Sw34 ∷ []) (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑))
  q63 : WsL → Eqn
  q63 c4 = eqn (Sw12 ∷ K4 ∷ []) (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑))
  q64 : WsL → Eqn
  q64 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0008 c4)
  q65 : WsL → Eqn
  q65 c4 = eqn (CS24⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS14⁻ ∷ []) (wl0009 c4)
  q66 : WsL → Eqn
  q66 c4 = eqn (Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap))
  q67 : WsL → Eqn
  q67 c4 = eqn (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) (wl0010 c4)
  q68 : WsL → Eqn
  q68 c4 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap))
  q69 : WsL → Eqn
  q69 c4 = eqn (Sw23 ∷ K4 ∷ []) (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K))
  q70 : WsL → Eqn
  q70 c4 = eqn (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4)
  q71 : WsL → Eqn
  q71 c4 = eqn (CS01 ∷ Sw34 ∷ []) (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑))
  q72 : WsL → Eqn
  q72 c4 = eqn (K3 ∷ Sw34 ∷ []) (Sw34 ∷ K4 ∷ []) (wl0068 c4)
  q73 : WsL → Eqn
  q73 c4 = eqn (CS34 ∷ Sw34 ∷ []) (Sw34 ∷ CS34 ∷ []) (wl0039 c4)
  q74 : WsL → Eqn
  q74 c4 = eqn (CS34⁻ ∷ Sw34 ∷ []) (Sw34 ∷ CS34⁻ ∷ []) (wl0040 c4)
  q75 : WsL → Eqn
  q75 c4 = eqn (K2 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ []) (wl0058 c4)
  q76 : WsL → Eqn
  q76 c4 = eqn (K1 ∷ Sw12 ∷ []) (Sw12 ∷ K2 ∷ []) (wl0062 c4)
  q77 : WsL → Eqn
  q77 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl0017 c4)
  q78 : WsL → Eqn
  q78 c4 = eqn (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) (wl0014 c4)
  q79 : WsL → Eqn
  q79 c4 = eqn (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ []) (wl0018 c4)
  q80 : WsL → Eqn
  q80 c4 = eqn (K1 ∷ Sw34 ∷ []) (Sw34 ∷ K1 ∷ []) (c₂ (K ↑) (Swap ↑))
  q81 : WsL → Eqn
  q81 c4 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (c₂ (K ↑) (Swap))
  q82 : WsL → Eqn
  q82 c4 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (c₂ (CS) (Swap))
  q83 : WsL → Eqn
  q83 c4 = eqn (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ []) (wl0166 c4)

-- nat 3 TOFF403: 144 steps
lem-nat-3-TOFF403 : WsL → ⟪ (Sw34 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF403 c4 = derive (Sw34 ∷ Toff403 ∷ []) (Toff304 ∷ Sw34 ∷ [])
  (re 1 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) ∷
   re 3 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) ∷
   re 4 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 5 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw⁻ 4 (q55 c4) ∷
   rw⁻ 7 (q56 c4) ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 (q57 c4) ∷
   rw⁻ 9 (q56 c4) ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 (q57 c4) ∷
   rw⁻ 11 (q56 c4) ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 (q55 c4) ∷
   rw⁻ 11 (q58 c4) ∷
   rw 12 (q56 c4) ∷
   rw⁻ 3 (q59 c4) ∷
   rw⁻ 6 (q60 c4) ∷
   re 4 3 (CS14 ∷ []) ∷
   rw⁻ 5 (q61 c4) ∷
   rw⁻ 8 (q60 c4) ∷
   re 6 3 (CS14⁻ ∷ []) ∷
   rw⁻ 7 (q61 c4) ∷
   rw⁻ 10 (q60 c4) ∷
   re 8 3 (CS04 ∷ []) ∷
   rw⁻ 9 (q59 c4) ∷
   rw⁻ 10 (q62 c4) ∷
   rw 11 (q60 c4) ∷
   rw 2 (q63 c4) ∷
   rw⁻ 3 (q64 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw⁻ 5 (q65 c4) ∷
   rw⁻ 8 (q21 c4) ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q66 c4) ∷
   rw⁻ 8 (q67 c4) ∷
   rw 9 (q66 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw 8 (q63 c4) ∷
   rw⁻ 9 (q68 c4) ∷
   rw 10 (q21 c4) ∷
   rw 1 (q69 c4) ∷
   rw⁻ 2 (q7 c4) ∷
   rw⁻ 5 (q56 c4) ∷
   re 3 3 (CX03 ∷ []) ∷
   rw⁻ 4 (q13 c4) ∷
   rw⁻ 7 (q56 c4) ∷
   re 5 3 (CX03 ∷ []) ∷
   re 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 6 (q70 c4) ∷
   rw⁻ 8 (q66 c4) ∷
   rw⁻ 9 (q71 c4) ∷
   rw⁻ 10 (q66 c4) ∷
   rw⁻ 11 (q70 c4) ∷
   re 6 7 (CS04 ∷ []) ∷
   rw 7 (q69 c4) ∷
   rw⁻ 8 (q58 c4) ∷
   rw 9 (q56 c4) ∷
   rw⁻ 0 (q72 c4) ∷
   rw⁻ 1 (q73 c4) ∷
   rw⁻ 4 (q60 c4) ∷
   re 2 3 (CX04 ∷ []) ∷
   rw⁻ 3 (q74 c4) ∷
   rw⁻ 6 (q60 c4) ∷
   re 4 3 (CX04 ∷ []) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q60 c4) ∷
   rw⁻ 6 (q72 c4) ∷
   rw⁻ 7 (q62 c4) ∷
   rw⁻ 0 (q56 c4) ∷
   rw⁻ 1 (q75 c4) ∷
   rw⁻ 2 (q8 c4) ∷
   re 4 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 3 (q70 c4) ∷
   rw⁻ 5 (q66 c4) ∷
   rw⁻ 6 (q61 c4) ∷
   rw⁻ 7 (q66 c4) ∷
   rw⁻ 8 (q70 c4) ∷
   re 3 7 (CX04 ∷ []) ∷
   rw⁻ 4 (q14 c4) ∷
   re 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q70 c4) ∷
   rw⁻ 7 (q66 c4) ∷
   rw⁻ 8 (q61 c4) ∷
   rw⁻ 9 (q66 c4) ∷
   rw⁻ 10 (q70 c4) ∷
   re 5 7 (CX04 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 (q56 c4) ∷
   rw⁻ 7 (q75 c4) ∷
   rw⁻ 8 (q58 c4) ∷
   rw⁻ 1 (q21 c4) ∷
   rw⁻ 2 (q76 c4) ∷
   rw⁻ 3 (q77 c4) ∷
   re 5 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 4 (q66 c4) ∷
   rw⁻ 5 (q78 c4) ∷
   rw 6 (q66 c4) ∷
   re 4 3 (CX04 ∷ []) ∷
   rw⁻ 5 (q79 c4) ∷
   re 7 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 6 (q66 c4) ∷
   rw⁻ 7 (q78 c4) ∷
   rw 8 (q66 c4) ∷
   re 6 3 (CX04 ∷ []) ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 7 (q21 c4) ∷
   rw⁻ 8 (q76 c4) ∷
   rw⁻ 9 (q68 c4) ∷
   rw⁻ 2 (q60 c4) ∷
   rw⁻ 3 (q80 c4) ∷
   re 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 4 (q60 c4) ∷
   re 6 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 5 (q60 c4) ∷
   re 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q60 c4) ∷
   re 8 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 7 (q60 c4) ∷
   rw⁻ 8 (q71 c4) ∷
   rw⁻ 9 (q80 c4) ∷
   rw⁻ 10 (q62 c4) ∷
   rw⁻ 3 (q56 c4) ∷
   rw⁻ 4 (q81 c4) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 (q56 c4) ∷
   re 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 6 (q56 c4) ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 (q56 c4) ∷
   re 9 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 8 (q56 c4) ∷
   rw⁻ 9 (q82 c4) ∷
   rw⁻ 10 (q81 c4) ∷
   rw⁻ 11 (q58 c4) ∷
   rw⁻ 4 (q83 c4) ∷
   re 4 8 (Toff102 ∷ []) ∷
   re 3 3 (Toff103 ∷ []) ∷
   re 2 3 (Toff104 ∷ []) ∷
   re 1 3 (Toff204 ∷ []) ∷
   re 0 3 (Toff304 ∷ []) ∷ []) Eq.refl

private
  q84 : WsL → Eqn
  q84 c4 = eqn (Sw23 ∷ CZ12 ∷ []) (CZ13 ∷ Sw23 ∷ []) (lem-nat-2-CZ12 c4)

-- nat 2 BOX(4;12): 3 steps
lem-nat-2-BOX⟨4·12⟩ : WsL → ⟪ (Sw23 ∷ Bx4-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-13 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·12⟩ c4 = derive (Sw23 ∷ Bx4-12 ∷ []) (Bx4-13 ∷ Sw23 ∷ [])
  (re 1 1 (CZ12 ∷ []) ∷
   rw 0 (q84 c4) ∷
   re 0 1 (Bx4-13 ∷ []) ∷ []) Eq.refl

private
  q85 : WsL → Eqn
  q85 c4 = eqn (Sw23 ∷ CCZ134 ∷ []) (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4)
  q86 : WsL → Eqn
  q86 c4 = eqn (Sw23 ∷ Toff134 ∷ []) (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4)
  q87 : WsL → Eqn
  q87 c4 = eqn (Sw23 ∷ Bx4-12 ∷ []) (Bx4-13 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·12⟩ c4)

-- nat 2 BOX(1;432): 8 steps
lem-nat-2-BOX⟨1·432⟩ : WsL → ⟪ (Sw23 ∷ Bx1-432 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-423 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·432⟩ c4 = derive (Sw23 ∷ Bx1-432 ∷ []) (Bx1-423 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-12 ∷ Toff134 ∷ CCZ134 ∷ Bx4-12 ∷ []) ∷
   rw 0 (q85 c4) ∷
   rw 1 (q86 c4) ∷
   rw 2 (q87 c4) ∷
   rw 3 (q86 c4) ∷
   rw 4 (q85 c4) ∷
   rw 5 (q87 c4) ∷
   re 0 6 (Bx1-423 ∷ []) ∷ []) Eq.refl

private
  q88 : WsL → Eqn
  q88 c4 = eqn (Sw23 ∷ Bx1-432 ∷ []) (Bx1-423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·432⟩ c4)

-- nat 2 BOX(4;1032): 8 steps
lem-nat-2-BOX⟨4·1032⟩ : WsL → ⟪ (Sw23 ∷ Bx4-1032 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·1032⟩ c4 = derive (Sw23 ∷ Bx4-1032 ∷ []) (Bx4-1023 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-432 ∷ Toff401 ∷ CCZ014 ∷ Bx1-432 ∷ []) ∷
   rw 0 (q46 c4) ∷
   rw 1 (q47 c4) ∷
   rw 2 (q88 c4) ∷
   rw 3 (q47 c4) ∷
   rw 4 (q46 c4) ∷
   rw 5 (q88 c4) ∷
   re 0 6 (Bx4-1023 ∷ []) ∷ []) Eq.refl

private
  q89 : WsL → Eqn
  q89 c4 = eqn (CS01 ∷ Sw01 ∷ []) (Sw01 ∷ CS01 ∷ []) (wl0132 c4)

-- nat 0 SBOX(3;1;0;2): 3 steps
lem-nat-0-SBOX⟨3·1·0·2⟩ : WsL → ⟪ (Sw01 ∷ Sb3-1-0-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-1-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨3·1·0·2⟩ c4 = derive (Sw01 ∷ Sb3-1-0-2 ∷ []) (Sb3-0-1-2 ∷ Sw01 ∷ [])
  (re 1 1 (CS01 ∷ []) ∷
   rw⁻ 0 (q89 c4) ∷
   re 0 1 (Sb3-0-1-2 ∷ []) ∷ []) Eq.refl

private
  q90 : WsL → Eqn
  q90 c4 = eqn (CS01⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS01⁻ ∷ []) (wl0133 c4)

-- nat 0 SBOXd(3;1;0;2): 3 steps
lem-nat-0-SBOXd⟨3·1·0·2⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻3-1-0-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-1-2 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨3·1·0·2⟩ c4 = derive (Sw01 ∷ Sb⁻3-1-0-2 ∷ []) (Sb⁻3-0-1-2 ∷ Sw01 ∷ [])
  (re 1 1 (CS01⁻ ∷ []) ∷
   rw⁻ 0 (q90 c4) ∷
   re 0 1 (Sb⁻3-0-1-2 ∷ []) ∷ []) Eq.refl

private
  q91 : WsL → Eqn
  q91 c4 = eqn (K2 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ []) (wl0056 c4)
  q92 : WsL → Eqn
  q92 c4 = eqn (Sw12 ∷ K3 ∷ []) (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K))
  q93 : WsL → Eqn
  q93 c4 = eqn (Sw12 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS))
  q94 : WsL → Eqn
  q94 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q95 : WsL → Eqn
  q95 c4 = eqn (Sw01 ∷ ι ∷ []) (ι ∷ Sw01 ∷ []) (wl0030 c4)
  q96 : WsL → Eqn
  q96 c4 = eqn (Sw01 ∷ K3 ∷ []) (K3 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑))
  q97 : WsL → Eqn
  q97 c4 = eqn (Sw01 ∷ Sw34 ∷ []) (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑))
  q98 : WsL → Eqn
  q98 c4 = eqn (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) (wl0019 c4)
  q99 : WsL → Eqn
  q99 c4 = eqn (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) (wl0020 c4)
  q100 : WsL → Eqn
  q100 c4 = eqn (Sw01 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑))
  q101 : WsL → Eqn
  q101 c4 = eqn (Sw01 ∷ CS34 ∷ []) (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))
  q102 : WsL → Eqn
  q102 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl0021 c4)
  q103 : WsL → Eqn
  q103 c4 = eqn (K2 ∷ Sw34 ∷ []) (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap))
  q104 : WsL → Eqn
  q104 c4 = eqn (CX12 ∷ Sw34 ∷ []) (Sw34 ∷ CX12 ∷ []) (c₃ (CX₀₁ ↑) (Swap))
  q105 : WsL → Eqn
  q105 c4 = eqn (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (wl0059 c4)

-- resp TOFF304 at 2: 236 steps
lem-resp-TOFF304-at-2 : WsL → ⟪ (Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff314 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF304-at-2 c4 = derive (Toff304 ∷ []) (Sw12 ∷ Sw01 ∷ Toff314 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q21 c4) ∷
   re 0 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) ∷
   re 1 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 3 (q81 c4) ∷
   rw⁻ 6 (q56 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q57 c4) ∷
   rw⁻ 8 (q56 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q57 c4) ∷
   rw⁻ 10 (q56 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 (q81 c4) ∷
   rw⁻ 10 (q58 c4) ∷
   rw 11 (q56 c4) ∷
   rw⁻ 2 (q80 c4) ∷
   rw⁻ 5 (q60 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q61 c4) ∷
   rw⁻ 7 (q60 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q61 c4) ∷
   rw⁻ 9 (q60 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q80 c4) ∷
   rw⁻ 9 (q62 c4) ∷
   rw 10 (q60 c4) ∷
   rw⁻ 1 (q91 c4) ∷
   rw⁻ 2 (q64 c4) ∷
   rw⁻ 5 (q21 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q65 c4) ∷
   rw⁻ 7 (q21 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q66 c4) ∷
   rw⁻ 7 (q67 c4) ∷
   rw 8 (q66 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q91 c4) ∷
   rw⁻ 8 (q68 c4) ∷
   rw 9 (q21 c4) ∷
   rw⁻ 0 (q55 c4) ∷
   rw⁻ 1 (q7 c4) ∷
   rw⁻ 4 (q56 c4) ∷
   re 2 3 (CX03 ∷ []) ∷
   rw⁻ 3 (q13 c4) ∷
   rw⁻ 6 (q56 c4) ∷
   re 4 3 (CX03 ∷ []) ∷
   re 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q70 c4) ∷
   rw⁻ 7 (q66 c4) ∷
   rw⁻ 8 (q71 c4) ∷
   rw⁻ 9 (q66 c4) ∷
   rw⁻ 10 (q70 c4) ∷
   re 5 7 (CS04 ∷ []) ∷
   rw⁻ 6 (q55 c4) ∷
   rw⁻ 7 (q58 c4) ∷
   rw 8 (q56 c4) ∷
   rw 7 (q68 c4) ∷
   rw⁻ 6 (q92 c4) ∷
   re 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 7 (q66 c4) ∷
   rw 6 (q67 c4) ∷
   rw⁻ 5 (q66 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw 4 (q78 c4) ∷
   rw⁻ 3 (q93 c4) ∷
   rw 2 (q78 c4) ∷
   rw⁻ 1 (q94 c4) ∷
   rw⁻ 0 (q92 c4) ∷
   rw⁻ 1 (q56 c4) ∷
   rw⁻ 2 (q75 c4) ∷
   rw⁻ 3 (q8 c4) ∷
   re 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 4 (q56 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   re 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 6 (q56 c4) ∷
   re 8 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 7 (q70 c4) ∷
   rw⁻ 9 (q66 c4) ∷
   rw⁻ 10 (q71 c4) ∷
   rw⁻ 11 (q66 c4) ∷
   rw⁻ 12 (q70 c4) ∷
   re 7 7 (CS04 ∷ []) ∷
   rw⁻ 8 (q75 c4) ∷
   rw⁻ 9 (q58 c4) ∷
   rw⁻ 2 (q21 c4) ∷
   rw⁻ 3 (q76 c4) ∷
   rw⁻ 4 (q77 c4) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 (q21 c4) ∷
   rw⁻ 6 (q79 c4) ∷
   re 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 7 (q21 c4) ∷
   re 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 8 (q66 c4) ∷
   rw⁻ 9 (q67 c4) ∷
   rw 10 (q66 c4) ∷
   re 8 3 (CS04 ∷ []) ∷
   rw⁻ 9 (q76 c4) ∷
   rw⁻ 10 (q68 c4) ∷
   rw⁻ 3 (q60 c4) ∷
   rw⁻ 4 (q80 c4) ∷
   re 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 5 (q60 c4) ∷
   rw⁻ 6 (q61 c4) ∷
   re 8 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 7 (q60 c4) ∷
   rw⁻ 8 (q61 c4) ∷
   re 10 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 9 (q60 c4) ∷
   rw⁻ 10 (q80 c4) ∷
   rw⁻ 11 (q62 c4) ∷
   rw⁻ 4 (q56 c4) ∷
   rw⁻ 5 (q81 c4) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 (q56 c4) ∷
   rw⁻ 7 (q57 c4) ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 (q56 c4) ∷
   rw⁻ 9 (q57 c4) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 (q56 c4) ∷
   rw⁻ 11 (q81 c4) ∷
   rw⁻ 12 (q58 c4) ∷
   re 5 8 (Toff102 ∷ []) ∷
   re 4 3 (Toff103 ∷ []) ∷
   re 3 3 (Toff104 ∷ []) ∷
   re 2 3 (Toff204 ∷ []) ∷
   re 1 3 (Toff304 ∷ []) ∷
   rw⁻ 2 (q19 c4) ∷
   re 1 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) ∷
   re 3 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) ∷
   re 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 4 (q81 c4) ∷
   rw⁻ 7 (q56 c4) ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 (q57 c4) ∷
   rw⁻ 9 (q56 c4) ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 (q57 c4) ∷
   rw⁻ 11 (q56 c4) ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 (q81 c4) ∷
   rw⁻ 11 (q58 c4) ∷
   rw 12 (q56 c4) ∷
   rw⁻ 3 (q80 c4) ∷
   rw⁻ 6 (q60 c4) ∷
   re 4 3 (CS14 ∷ []) ∷
   rw⁻ 5 (q61 c4) ∷
   rw⁻ 8 (q60 c4) ∷
   re 6 3 (CS14⁻ ∷ []) ∷
   rw⁻ 7 (q61 c4) ∷
   rw⁻ 10 (q60 c4) ∷
   re 8 3 (CS04 ∷ []) ∷
   rw⁻ 9 (q80 c4) ∷
   rw⁻ 10 (q62 c4) ∷
   rw 11 (q60 c4) ∷
   rw⁻ 2 (q91 c4) ∷
   rw⁻ 3 (q64 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw⁻ 5 (q65 c4) ∷
   rw⁻ 8 (q21 c4) ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q66 c4) ∷
   rw⁻ 8 (q67 c4) ∷
   rw 9 (q66 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q91 c4) ∷
   rw⁻ 9 (q68 c4) ∷
   rw 10 (q21 c4) ∷
   rw⁻ 1 (q55 c4) ∷
   rw⁻ 2 (q7 c4) ∷
   rw⁻ 5 (q56 c4) ∷
   re 3 3 (CX03 ∷ []) ∷
   rw⁻ 4 (q13 c4) ∷
   rw⁻ 7 (q56 c4) ∷
   re 5 3 (CX03 ∷ []) ∷
   re 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 6 (q70 c4) ∷
   rw⁻ 8 (q66 c4) ∷
   rw⁻ 9 (q71 c4) ∷
   rw⁻ 10 (q66 c4) ∷
   rw⁻ 11 (q70 c4) ∷
   re 6 7 (CS04 ∷ []) ∷
   rw⁻ 7 (q55 c4) ∷
   rw⁻ 8 (q58 c4) ∷
   rw 9 (q56 c4) ∷
   rw⁻ 8 (q95 c4) ∷
   rw⁻ 7 (q96 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q97 c4) ∷
   rw 7 (q98 c4) ∷
   rw⁻ 6 (q97 c4) ∷
   re 7 3 (CS14 ∷ []) ∷
   rw 5 (q99 c4) ∷
   rw⁻ 4 (q100 c4) ∷
   rw 3 (q99 c4) ∷
   rw⁻ 2 (q101 c4) ∷
   rw⁻ 1 (q96 c4) ∷
   rw⁻ 2 (q56 c4) ∷
   rw⁻ 3 (q75 c4) ∷
   rw⁻ 4 (q8 c4) ∷
   re 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 5 (q56 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   re 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 7 (q56 c4) ∷
   rw⁻ 8 (q102 c4) ∷
   rw⁻ 9 (q75 c4) ∷
   rw⁻ 10 (q58 c4) ∷
   rw⁻ 3 (q60 c4) ∷
   rw⁻ 4 (q103 c4) ∷
   re 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 5 (q60 c4) ∷
   rw⁻ 6 (q104 c4) ∷
   re 8 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 7 (q60 c4) ∷
   rw⁻ 8 (q104 c4) ∷
   re 10 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 9 (q60 c4) ∷
   rw⁻ 10 (q103 c4) ∷
   rw⁻ 11 (q62 c4) ∷
   rw 4 (q105 c4) ∷
   re 4 8 (Toff213 ∷ []) ∷
   re 3 3 (Toff214 ∷ []) ∷
   re 2 3 (Toff314 ∷ []) ∷ []) Eq.refl

private
  q106 : WsL → Eqn
  q106 c4 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wl0048 c4)

-- resp CX02 at 1: 2 steps
lem-resp-CX02-at-1 : WsL → ⟪ (CX02 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX12 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX02-at-1 c4 = derive (CX02 ∷ []) (Sw01 ∷ CX12 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q19 c4) ∷
   rw 0 (q106 c4) ∷ []) Eq.refl

-- nat 2 BOX(3;12): 3 steps
lem-nat-2-BOX⟨3·12⟩ : WsL → ⟪ (Sw23 ∷ Bx3-12 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-13 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·12⟩ c4 = derive (Sw23 ∷ Bx3-12 ∷ []) (Bx2-13 ∷ Sw23 ∷ [])
  (re 1 1 (CZ12 ∷ []) ∷
   rw 0 (q84 c4) ∷
   re 0 1 (Bx2-13 ∷ []) ∷ []) Eq.refl

private
  q107 : WsL → Eqn
  q107 c4 = eqn (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4)
  q108 : WsL → Eqn
  q108 c4 = eqn (Sw23 ∷ Toff103 ∷ []) (Toff102 ∷ Sw23 ∷ []) (lem-nat-2-TOFF103 c4)
  q109 : WsL → Eqn
  q109 c4 = eqn (Sw23 ∷ Bx3-12 ∷ []) (Bx2-13 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·12⟩ c4)

-- nat 2 BOX(1;302): 8 steps
lem-nat-2-BOX⟨1·302⟩ : WsL → ⟪ (Sw23 ∷ Bx1-302 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-203 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·302⟩ c4 = derive (Sw23 ∷ Bx1-302 ∷ []) (Bx1-203 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) ∷
   rw 0 (q107 c4) ∷
   rw 1 (q108 c4) ∷
   rw 2 (q109 c4) ∷
   rw 3 (q108 c4) ∷
   rw 4 (q107 c4) ∷
   rw 5 (q109 c4) ∷
   re 0 6 (Bx1-203 ∷ []) ∷ []) Eq.refl

private
  q110 : WsL → Eqn
  q110 c4 = eqn (Sw23 ∷ Bx1-302 ∷ []) (Bx1-203 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·302⟩ c4)

-- nat 2 BOX(3;1402): 8 steps
lem-nat-2-BOX⟨3·1402⟩ : WsL → ⟪ (Sw23 ∷ Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1403 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·1402⟩ c4 = derive (Sw23 ∷ Bx3-1402 ∷ []) (Bx2-1403 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-302 ∷ Toff314 ∷ CCZ134 ∷ Bx1-302 ∷ []) ∷
   rw 0 (q85 c4) ∷
   rw 1 (q33 c4) ∷
   rw 2 (q110 c4) ∷
   rw 3 (q33 c4) ∷
   rw 4 (q85 c4) ∷
   rw 5 (q110 c4) ∷
   re 0 6 (Bx2-1403 ∷ []) ∷ []) Eq.refl

private
  q111 : WsL → Eqn
  q111 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4)
  q112 : WsL → Eqn
  q112 c4 = eqn (Sw23 ∷ Toff102 ∷ []) (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4)
  q113 : WsL → Eqn
  q113 c4 = eqn (Sw23 ∷ Bx2-13 ∷ []) (Bx3-12 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·13⟩ c4)

-- nat 2 BOX(1;203): 8 steps
lem-nat-2-BOX⟨1·203⟩ : WsL → ⟪ (Sw23 ∷ Bx1-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-302 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·203⟩ c4 = derive (Sw23 ∷ Bx1-203 ∷ []) (Bx1-302 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx2-13 ∷ Toff102 ∷ CCZ012 ∷ Bx2-13 ∷ []) ∷
   rw 0 (q111 c4) ∷
   rw 1 (q112 c4) ∷
   rw 2 (q113 c4) ∷
   rw 3 (q112 c4) ∷
   rw 4 (q111 c4) ∷
   rw 5 (q113 c4) ∷
   re 0 6 (Bx1-302 ∷ []) ∷ []) Eq.refl

private
  q114 : WsL → Eqn
  q114 c4 = eqn (Sw23 ∷ Bx1-203 ∷ []) (Bx1-302 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·203⟩ c4)

-- nat 2 BOX(2;1403): 8 steps
lem-nat-2-BOX⟨2·1403⟩ : WsL → ⟪ (Sw23 ∷ Bx2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·1403⟩ c4 = derive (Sw23 ∷ Bx2-1403 ∷ []) (Bx3-1402 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-203 ∷ Toff214 ∷ CCZ124 ∷ Bx1-203 ∷ []) ∷
   rw 0 (q43 c4) ∷
   rw 1 (q39 c4) ∷
   rw 2 (q114 c4) ∷
   rw 3 (q39 c4) ∷
   rw 4 (q43 c4) ∷
   rw 5 (q114 c4) ∷
   re 0 6 (Bx3-1402 ∷ []) ∷ []) Eq.refl

private
  q115 : WsL → Eqn
  q115 c4 = eqn (CCZ234 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ234 ∷ []) (wl0086 c4)
  q116 : WsL → Eqn
  q116 c4 = eqn (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) (wl0127 c4)
  q117 : WsL → Eqn
  q117 c4 = eqn (Sw23 ∷ Bx3-21 ∷ []) (Bx2-31 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·21⟩ c4)

-- nat 2 BOX(2;341): 8 steps
lem-nat-2-BOX⟨2·341⟩ : WsL → ⟪ (Sw23 ∷ Bx2-341 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-241 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·341⟩ c4 = derive (Sw23 ∷ Bx2-341 ∷ []) (Bx3-241 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ []) ∷
   rw⁻ 0 (q115 c4) ∷
   rw 1 (q116 c4) ∷
   rw 2 (q117 c4) ∷
   rw 3 (q116 c4) ∷
   rw⁻ 4 (q115 c4) ∷
   rw 5 (q117 c4) ∷
   re 0 6 (Bx3-241 ∷ []) ∷ []) Eq.refl

private
  q118 : WsL → Eqn
  q118 c4 = eqn (Sw23 ∷ Bx2-341 ∷ []) (Bx3-241 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·341⟩ c4)

-- nat 2 BOX(3;2041): 8 steps
lem-nat-2-BOX⟨3·2041⟩ : WsL → ⟪ (Sw23 ∷ Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·2041⟩ c4 = derive (Sw23 ∷ Bx3-2041 ∷ []) (Bx2-3041 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-341 ∷ Toff302 ∷ CCZ023 ∷ Bx2-341 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q118 c4) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw 5 (q118 c4) ∷
   re 0 6 (Bx2-3041 ∷ []) ∷ []) Eq.refl

private
  q119 : WsL → Eqn
  q119 c4 = eqn (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) (wl0144 c4)
  q120 : WsL → Eqn
  q120 c4 = eqn (Sw23 ∷ Bx2-31 ∷ []) (Bx3-21 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·31⟩ c4)

-- nat 2 BOX(3;241): 8 steps
lem-nat-2-BOX⟨3·241⟩ : WsL → ⟪ (Sw23 ∷ Bx3-241 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-341 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·241⟩ c4 = derive (Sw23 ∷ Bx3-241 ∷ []) (Bx2-341 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ []) ∷
   rw⁻ 0 (q115 c4) ∷
   rw 1 (q119 c4) ∷
   rw 2 (q120 c4) ∷
   rw 3 (q119 c4) ∷
   rw⁻ 4 (q115 c4) ∷
   rw 5 (q120 c4) ∷
   re 0 6 (Bx2-341 ∷ []) ∷ []) Eq.refl

private
  q121 : WsL → Eqn
  q121 c4 = eqn (Sw23 ∷ Toff203 ∷ []) (Toff302 ∷ Sw23 ∷ []) (wl0090 c4)
  q122 : WsL → Eqn
  q122 c4 = eqn (Sw23 ∷ Bx3-241 ∷ []) (Bx2-341 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·241⟩ c4)

-- nat 2 BOX(2;3041): 8 steps
lem-nat-2-BOX⟨2·3041⟩ : WsL → ⟪ (Sw23 ∷ Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·3041⟩ c4 = derive (Sw23 ∷ Bx2-3041 ∷ []) (Bx3-2041 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-241 ∷ Toff203 ∷ CCZ023 ∷ Bx3-241 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   rw 1 (q121 c4) ∷
   rw 2 (q122 c4) ∷
   rw 3 (q121 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw 5 (q122 c4) ∷
   re 0 6 (Bx3-2041 ∷ []) ∷ []) Eq.refl

private
  q123 : WsL → Eqn
  q123 c4 = eqn (Bx4-21 ∷ Sw34 ∷ []) (Sw34 ∷ Bx4-21 ∷ []) (c₃ (CZ ↑) (Swap))

-- nat 3 BOX(4;21): 2 steps
lem-nat-3-BOX⟨4·21⟩ : WsL → ⟪ (Sw34 ∷ Bx4-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-21 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·21⟩ c4 = derive (Sw34 ∷ Bx4-21 ∷ []) (Bx3-21 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q123 c4) ∷
   re 0 1 (Bx3-21 ∷ []) ∷ []) Eq.refl

private
  q124 : WsL → Eqn
  q124 c4 = eqn (CCZ234 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ234 ∷ []) (wl0155 c4)
  q125 : WsL → Eqn
  q125 c4 = eqn (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) (wl0128 c4)
  q126 : WsL → Eqn
  q126 c4 = eqn (Sw34 ∷ Bx4-21 ∷ []) (Bx3-21 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·21⟩ c4)

-- nat 3 BOX(2;431): 8 steps
lem-nat-3-BOX⟨2·431⟩ : WsL → ⟪ (Sw34 ∷ Bx2-431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-341 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·431⟩ c4 = derive (Sw34 ∷ Bx2-431 ∷ []) (Bx2-341 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) ∷
   rw⁻ 0 (q124 c4) ∷
   rw 1 (q125 c4) ∷
   rw 2 (q126 c4) ∷
   rw 3 (q125 c4) ∷
   rw⁻ 4 (q124 c4) ∷
   rw 5 (q126 c4) ∷
   re 0 6 (Bx2-341 ∷ []) ∷ []) Eq.refl

private
  q127 : WsL → Eqn
  q127 c4 = eqn (Sw34 ∷ CCZ024 ∷ []) (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4)
  q128 : WsL → Eqn
  q128 c4 = eqn (Sw34 ∷ Toff402 ∷ []) (Toff302 ∷ Sw34 ∷ []) (lem-nat-3-TOFF402 c4)
  q129 : WsL → Eqn
  q129 c4 = eqn (Sw34 ∷ Bx2-431 ∷ []) (Bx2-341 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·431⟩ c4)

-- nat 3 BOX(4;2031): 8 steps
lem-nat-3-BOX⟨4·2031⟩ : WsL → ⟪ (Sw34 ∷ Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·2031⟩ c4 = derive (Sw34 ∷ Bx4-2031 ∷ []) (Bx3-2041 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-431 ∷ Toff402 ∷ CCZ024 ∷ Bx2-431 ∷ []) ∷
   rw 0 (q127 c4) ∷
   rw 1 (q128 c4) ∷
   rw 2 (q129 c4) ∷
   rw 3 (q128 c4) ∷
   rw 4 (q127 c4) ∷
   rw 5 (q129 c4) ∷
   re 0 6 (Bx3-2041 ∷ []) ∷ []) Eq.refl

private
  q130 : WsL → Eqn
  q130 c4 = eqn (Bx3-21 ∷ Sw34 ∷ []) (Sw34 ∷ Bx3-21 ∷ []) (c₃ (CZ ↑) (Swap))

-- nat 3 BOX(3;21): 2 steps
lem-nat-3-BOX⟨3·21⟩ : WsL → ⟪ (Sw34 ∷ Bx3-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-21 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·21⟩ c4 = derive (Sw34 ∷ Bx3-21 ∷ []) (Bx4-21 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q130 c4) ∷
   re 0 1 (Bx4-21 ∷ []) ∷ []) Eq.refl

private
  q131 : WsL → Eqn
  q131 c4 = eqn (Sw34 ∷ Bx3-21 ∷ []) (Bx4-21 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·21⟩ c4)

-- nat 3 BOX(2;341): 8 steps
lem-nat-3-BOX⟨2·341⟩ : WsL → ⟪ (Sw34 ∷ Bx2-341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-431 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·341⟩ c4 = derive (Sw34 ∷ Bx2-341 ∷ []) (Bx2-431 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ []) ∷
   rw⁻ 0 (q124 c4) ∷
   rw 1 (q125 c4) ∷
   rw 2 (q131 c4) ∷
   rw 3 (q125 c4) ∷
   rw⁻ 4 (q124 c4) ∷
   rw 5 (q131 c4) ∷
   re 0 6 (Bx2-431 ∷ []) ∷ []) Eq.refl

private
  q132 : WsL → Eqn
  q132 c4 = eqn (Sw34 ∷ CCZ023 ∷ []) (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4)
  q133 : WsL → Eqn
  q133 c4 = eqn (Sw34 ∷ Toff302 ∷ []) (Toff402 ∷ Sw34 ∷ []) (lem-nat-3-TOFF302 c4)
  q134 : WsL → Eqn
  q134 c4 = eqn (Sw34 ∷ Bx2-341 ∷ []) (Bx2-431 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·341⟩ c4)

-- nat 3 BOX(3;2041): 8 steps
lem-nat-3-BOX⟨3·2041⟩ : WsL → ⟪ (Sw34 ∷ Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·2041⟩ c4 = derive (Sw34 ∷ Bx3-2041 ∷ []) (Bx4-2031 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-341 ∷ Toff302 ∷ CCZ023 ∷ Bx2-341 ∷ []) ∷
   rw 0 (q132 c4) ∷
   rw 1 (q133 c4) ∷
   rw 2 (q134 c4) ∷
   rw 3 (q133 c4) ∷
   rw 4 (q132 c4) ∷
   rw 5 (q134 c4) ∷
   re 0 6 (Bx4-2031 ∷ []) ∷ []) Eq.refl

private
  q135 : WsL → Eqn
  q135 c4 = eqn (Sw23 ∷ CS13 ∷ []) (CS12 ∷ Sw23 ∷ []) (lem-nat-2-CS13 c4)

-- nat 2 SBOX(2;1;3;0): 3 steps
lem-nat-2-SBOX⟨2·1·3·0⟩ : WsL → ⟪ (Sw23 ∷ Sb2-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-2-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·1·3·0⟩ c4 = derive (Sw23 ∷ Sb2-1-3-0 ∷ []) (Sb3-1-2-0 ∷ Sw23 ∷ [])
  (re 1 1 (CS13 ∷ []) ∷
   rw 0 (q135 c4) ∷
   re 0 1 (Sb3-1-2-0 ∷ []) ∷ []) Eq.refl

private
  q136 : WsL → Eqn
  q136 c4 = eqn (Sw23 ∷ CS12 ∷ []) (CS13 ∷ Sw23 ∷ []) (lem-nat-2-CS12 c4)

-- nat 2 SBOX(3;1;2;0): 3 steps
lem-nat-2-SBOX⟨3·1·2·0⟩ : WsL → ⟪ (Sw23 ∷ Sb3-1-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-3-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·1·2·0⟩ c4 = derive (Sw23 ∷ Sb3-1-2-0 ∷ []) (Sb2-1-3-0 ∷ Sw23 ∷ [])
  (re 1 1 (CS12 ∷ []) ∷
   rw 0 (q136 c4) ∷
   re 0 1 (Sb2-1-3-0 ∷ []) ∷ []) Eq.refl

private
  q137 : WsL → Eqn
  q137 c4 = eqn (Sw23 ∷ CS13⁻ ∷ []) (CS12⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd13 c4)

-- nat 2 SBOXd(2;1;3;0): 3 steps
lem-nat-2-SBOXd⟨2·1·3·0⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻2-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-1-2-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨2·1·3·0⟩ c4 = derive (Sw23 ∷ Sb⁻2-1-3-0 ∷ []) (Sb⁻3-1-2-0 ∷ Sw23 ∷ [])
  (re 1 1 (CS13⁻ ∷ []) ∷
   rw 0 (q137 c4) ∷
   re 0 1 (Sb⁻3-1-2-0 ∷ []) ∷ []) Eq.refl

private
  q138 : WsL → Eqn
  q138 c4 = eqn (Sw23 ∷ CS12⁻ ∷ []) (CS13⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd12 c4)

-- nat 2 SBOXd(3;1;2;0): 3 steps
lem-nat-2-SBOXd⟨3·1·2·0⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻3-1-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-3-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·1·2·0⟩ c4 = derive (Sw23 ∷ Sb⁻3-1-2-0 ∷ []) (Sb⁻2-1-3-0 ∷ Sw23 ∷ [])
  (re 1 1 (CS12⁻ ∷ []) ∷
   rw 0 (q138 c4) ∷
   re 0 1 (Sb⁻2-1-3-0 ∷ []) ∷ []) Eq.refl

private
  q139 : WsL → Eqn
  q139 c4 = eqn (CX31 ∷ Sw12 ∷ []) (Sw12 ∷ CX32 ∷ []) (wl0151 c4)
  q140 : WsL → Eqn
  q140 c4 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (c₂ (Swap) (CX₁₀))

-- resp CX31 at 2: 4 steps
lem-resp-CX31-at-2 : WsL → ⟪ (CX31 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX32 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX31-at-2 c4 = derive (CX31 ∷ []) (Sw12 ∷ Sw01 ∷ CX32 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q21 c4) ∷
   rw 0 (q139 c4) ∷
   rw⁻ 2 (q19 c4) ∷
   rw⁻ 1 (q140 c4) ∷ []) Eq.refl

private
  q141 : WsL → Eqn
  q141 c4 = eqn (Sw01 ∷ Bx2-0431 ∷ []) (Bx2-1430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0431⟩ c4)
  q142 : WsL → Eqn
  q142 c4 = eqn (Sw01 ∷ Toff134 ∷ []) (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4)
  q143 : WsL → Eqn
  q143 c4 = eqn (Sw01 ∷ Sb2-0-1-3 ∷ []) (Sb2-1-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·1·3⟩ c4)
  q144 : WsL → Eqn
  q144 c4 = eqn (Sw01 ∷ Sb⁻2-0-1-3 ∷ []) (Sb⁻2-1-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·0·1·3⟩ c4)

-- nat 0 SBOX(2;0;43;1): 7 steps
lem-nat-0-SBOX⟨2·0·43·1⟩ : WsL → ⟪ (Sw01 ∷ Sb2-0-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-43-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·0·43·1⟩ c4 = derive (Sw01 ∷ Sb2-0-43-1 ∷ []) (Sb2-1-43-0 ∷ Sw01 ∷ [])
  (re 1 1 (Bx2-0431 ∷ Toff134 ∷ Sb2-0-1-3 ∷ Toff134 ∷ Sb⁻2-0-1-3 ∷ []) ∷
   rw 0 (q141 c4) ∷
   rw 1 (q142 c4) ∷
   rw 2 (q143 c4) ∷
   rw 3 (q142 c4) ∷
   rw 4 (q144 c4) ∷
   re 0 5 (Sb2-1-43-0 ∷ []) ∷ []) Eq.refl

-- nat 1 SBOX(2;1;0;3): 3 steps
lem-nat-1-SBOX⟨2·1·0·3⟩ : WsL → ⟪ (Sw12 ∷ Sb2-1-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-0-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·1·0·3⟩ c4 = derive (Sw12 ∷ Sb2-1-0-3 ∷ []) (Sb1-2-0-3 ∷ Sw12 ∷ [])
  (re 1 1 (CS01 ∷ []) ∷
   rw 0 (q24 c4) ∷
   re 0 1 (Sb1-2-0-3 ∷ []) ∷ []) Eq.refl

-- nat 1 SBOXd(2;1;0;3): 3 steps
lem-nat-1-SBOXd⟨2·1·0·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-1-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-0-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·1·0·3⟩ c4 = derive (Sw12 ∷ Sb⁻2-1-0-3 ∷ []) (Sb⁻1-2-0-3 ∷ Sw12 ∷ [])
  (re 1 1 (CS01⁻ ∷ []) ∷
   rw 0 (q25 c4) ∷
   re 0 1 (Sb⁻1-2-0-3 ∷ []) ∷ []) Eq.refl

private
  q145 : WsL → Eqn
  q145 c4 = eqn (Sw12 ∷ Bx2-1430 ∷ []) (Bx1-2430 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1430⟩ c4)
  q146 : WsL → Eqn
  q146 c4 = eqn (Sw12 ∷ Toff034 ∷ []) (Toff034 ∷ Sw12 ∷ []) (lem-nat-1-TOFF034 c4)
  q147 : WsL → Eqn
  q147 c4 = eqn (Sw12 ∷ Sb2-1-0-3 ∷ []) (Sb1-2-0-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·1·0·3⟩ c4)
  q148 : WsL → Eqn
  q148 c4 = eqn (Sw12 ∷ Sb⁻2-1-0-3 ∷ []) (Sb⁻1-2-0-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·1·0·3⟩ c4)

-- nat 1 SBOX(2;1;43;0): 7 steps
lem-nat-1-SBOX⟨2·1·43·0⟩ : WsL → ⟪ (Sw12 ∷ Sb2-1-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·1·43·0⟩ c4 = derive (Sw12 ∷ Sb2-1-43-0 ∷ []) (Sb1-2-43-0 ∷ Sw12 ∷ [])
  (re 1 1 (Bx2-1430 ∷ Toff034 ∷ Sb2-1-0-3 ∷ Toff034 ∷ Sb⁻2-1-0-3 ∷ []) ∷
   rw 0 (q145 c4) ∷
   rw 1 (q146 c4) ∷
   rw 2 (q147 c4) ∷
   rw 3 (q146 c4) ∷
   rw 4 (q148 c4) ∷
   re 0 5 (Sb1-2-43-0 ∷ []) ∷ []) Eq.refl

private
  q149 : WsL → Eqn
  q149 c4 = eqn (Bx2-10 ∷ Sw23 ∷ []) (Sw23 ∷ Bx2-10 ∷ []) (c₂ (CZ) (Swap))

-- nat 2 BOX(2;10): 2 steps
lem-nat-2-BOX⟨2·10⟩ : WsL → ⟪ (Sw23 ∷ Bx2-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-10 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·10⟩ c4 = derive (Sw23 ∷ Bx2-10 ∷ []) (Bx3-10 ∷ Sw23 ∷ [])
  (rw⁻ 0 (q149 c4) ∷
   re 0 1 (Bx3-10 ∷ []) ∷ []) Eq.refl

private
  q150 : WsL → Eqn
  q150 c4 = eqn (CCZ123 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ123 ∷ []) (wl0113 c4)
  q151 : WsL → Eqn
  q151 c4 = eqn (Sw23 ∷ Toff123 ∷ []) (Toff123 ∷ Sw23 ∷ []) (wl0114 c4)
  q152 : WsL → Eqn
  q152 c4 = eqn (Sw23 ∷ Bx2-10 ∷ []) (Bx3-10 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·10⟩ c4)

-- nat 2 BOX(1;230): 8 steps
lem-nat-2-BOX⟨1·230⟩ : WsL → ⟪ (Sw23 ∷ Bx1-230 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-320 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·230⟩ c4 = derive (Sw23 ∷ Bx1-230 ∷ []) (Bx1-320 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) ∷
   rw⁻ 0 (q150 c4) ∷
   rw 1 (q151 c4) ∷
   rw 2 (q152 c4) ∷
   rw 3 (q151 c4) ∷
   rw⁻ 4 (q150 c4) ∷
   rw 5 (q152 c4) ∷
   re 0 6 (Bx1-320 ∷ []) ∷ []) Eq.refl

private
  q153 : WsL → Eqn
  q153 c4 = eqn (Sw23 ∷ Bx1-230 ∷ []) (Bx1-320 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·230⟩ c4)

-- nat 2 BOX(2;1430): 8 steps
lem-nat-2-BOX⟨2·1430⟩ : WsL → ⟪ (Sw23 ∷ Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·1430⟩ c4 = derive (Sw23 ∷ Bx2-1430 ∷ []) (Bx3-1420 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-230 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ []) ∷
   rw 0 (q43 c4) ∷
   rw 1 (q39 c4) ∷
   rw 2 (q153 c4) ∷
   rw 3 (q39 c4) ∷
   rw 4 (q43 c4) ∷
   rw 5 (q153 c4) ∷
   re 0 6 (Bx3-1420 ∷ []) ∷ []) Eq.refl

private
  q154 : WsL → Eqn
  q154 c4 = eqn (Sb2-1-0-3 ∷ Sw23 ∷ []) (Sw23 ∷ Sb2-1-0-3 ∷ []) (c₂ (CS) (Swap))

-- nat 2 SBOX(2;1;0;3): 2 steps
lem-nat-2-SBOX⟨2·1·0·3⟩ : WsL → ⟪ (Sw23 ∷ Sb2-1-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-0-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·1·0·3⟩ c4 = derive (Sw23 ∷ Sb2-1-0-3 ∷ []) (Sb3-1-0-2 ∷ Sw23 ∷ [])
  (rw⁻ 0 (q154 c4) ∷
   re 0 1 (Sb3-1-0-2 ∷ []) ∷ []) Eq.refl

private
  q155 : WsL → Eqn
  q155 c4 = eqn (Sb⁻2-1-0-3 ∷ Sw23 ∷ []) (Sw23 ∷ Sb⁻2-1-0-3 ∷ []) (c₂ (CS • CS • CS) (Swap))

-- nat 2 SBOXd(2;1;0;3): 2 steps
lem-nat-2-SBOXd⟨2·1·0·3⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻2-1-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-1-0-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨2·1·0·3⟩ c4 = derive (Sw23 ∷ Sb⁻2-1-0-3 ∷ []) (Sb⁻3-1-0-2 ∷ Sw23 ∷ [])
  (rw⁻ 0 (q155 c4) ∷
   re 0 1 (Sb⁻3-1-0-2 ∷ []) ∷ []) Eq.refl

private
  q156 : WsL → Eqn
  q156 c4 = eqn (Sw23 ∷ Bx2-1430 ∷ []) (Bx3-1420 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·1430⟩ c4)
  q157 : WsL → Eqn
  q157 c4 = eqn (Sw23 ∷ Sb2-1-0-3 ∷ []) (Sb3-1-0-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·1·0·3⟩ c4)
  q158 : WsL → Eqn
  q158 c4 = eqn (Sw23 ∷ Sb⁻2-1-0-3 ∷ []) (Sb⁻3-1-0-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨2·1·0·3⟩ c4)

-- nat 2 SBOX(2;1;43;0): 7 steps
lem-nat-2-SBOX⟨2·1·43·0⟩ : WsL → ⟪ (Sw23 ∷ Sb2-1-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·1·43·0⟩ c4 = derive (Sw23 ∷ Sb2-1-43-0 ∷ []) (Sb3-1-42-0 ∷ Sw23 ∷ [])
  (re 1 1 (Bx2-1430 ∷ Toff034 ∷ Sb2-1-0-3 ∷ Toff034 ∷ Sb⁻2-1-0-3 ∷ []) ∷
   rw 0 (q156 c4) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q157 c4) ∷
   rw 3 (q5 c4) ∷
   rw 4 (q158 c4) ∷
   re 0 5 (Sb3-1-42-0 ∷ []) ∷ []) Eq.refl

private
  q159 : WsL → Eqn
  q159 c4 = eqn (Bx3-10 ∷ Sw23 ∷ []) (Sw23 ∷ Bx3-10 ∷ []) (c₂ (CZ) (Swap))

-- nat 2 BOX(3;10): 2 steps
lem-nat-2-BOX⟨3·10⟩ : WsL → ⟪ (Sw23 ∷ Bx3-10 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-10 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·10⟩ c4 = derive (Sw23 ∷ Bx3-10 ∷ []) (Bx2-10 ∷ Sw23 ∷ [])
  (rw⁻ 0 (q159 c4) ∷
   re 0 1 (Bx2-10 ∷ []) ∷ []) Eq.refl

private
  q160 : WsL → Eqn
  q160 c4 = eqn (Sw23 ∷ Bx3-10 ∷ []) (Bx2-10 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·10⟩ c4)

-- nat 2 BOX(1;320): 8 steps
lem-nat-2-BOX⟨1·320⟩ : WsL → ⟪ (Sw23 ∷ Bx1-320 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-230 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·320⟩ c4 = derive (Sw23 ∷ Bx1-320 ∷ []) (Bx1-230 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) ∷
   rw⁻ 0 (q150 c4) ∷
   rw 1 (q151 c4) ∷
   rw 2 (q160 c4) ∷
   rw 3 (q151 c4) ∷
   rw⁻ 4 (q150 c4) ∷
   rw 5 (q160 c4) ∷
   re 0 6 (Bx1-230 ∷ []) ∷ []) Eq.refl

private
  q161 : WsL → Eqn
  q161 c4 = eqn (Sw23 ∷ Bx1-320 ∷ []) (Bx1-230 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·320⟩ c4)

-- nat 2 BOX(3;1420): 8 steps
lem-nat-2-BOX⟨3·1420⟩ : WsL → ⟪ (Sw23 ∷ Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·1420⟩ c4 = derive (Sw23 ∷ Bx3-1420 ∷ []) (Bx2-1430 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ []) ∷
   rw 0 (q85 c4) ∷
   rw 1 (q33 c4) ∷
   rw 2 (q161 c4) ∷
   rw 3 (q33 c4) ∷
   rw 4 (q85 c4) ∷
   rw 5 (q161 c4) ∷
   re 0 6 (Bx2-1430 ∷ []) ∷ []) Eq.refl

private
  q162 : WsL → Eqn
  q162 c4 = eqn (Sb3-1-0-2 ∷ Sw23 ∷ []) (Sw23 ∷ Sb3-1-0-2 ∷ []) (c₂ (CS) (Swap))

-- nat 2 SBOX(3;1;0;2): 2 steps
lem-nat-2-SBOX⟨3·1·0·2⟩ : WsL → ⟪ (Sw23 ∷ Sb3-1-0-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-0-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·1·0·2⟩ c4 = derive (Sw23 ∷ Sb3-1-0-2 ∷ []) (Sb2-1-0-3 ∷ Sw23 ∷ [])
  (rw⁻ 0 (q162 c4) ∷
   re 0 1 (Sb2-1-0-3 ∷ []) ∷ []) Eq.refl

private
  q163 : WsL → Eqn
  q163 c4 = eqn (Sb⁻3-1-0-2 ∷ Sw23 ∷ []) (Sw23 ∷ Sb⁻3-1-0-2 ∷ []) (c₂ (CS • CS • CS) (Swap))

-- nat 2 SBOXd(3;1;0;2): 2 steps
lem-nat-2-SBOXd⟨3·1·0·2⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻3-1-0-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-0-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·1·0·2⟩ c4 = derive (Sw23 ∷ Sb⁻3-1-0-2 ∷ []) (Sb⁻2-1-0-3 ∷ Sw23 ∷ [])
  (rw⁻ 0 (q163 c4) ∷
   re 0 1 (Sb⁻2-1-0-3 ∷ []) ∷ []) Eq.refl

private
  q164 : WsL → Eqn
  q164 c4 = eqn (Sw23 ∷ Bx3-1420 ∷ []) (Bx2-1430 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·1420⟩ c4)
  q165 : WsL → Eqn
  q165 c4 = eqn (Sw23 ∷ Toff024 ∷ []) (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4)
  q166 : WsL → Eqn
  q166 c4 = eqn (Sw23 ∷ Sb3-1-0-2 ∷ []) (Sb2-1-0-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·1·0·2⟩ c4)
  q167 : WsL → Eqn
  q167 c4 = eqn (Sw23 ∷ Sb⁻3-1-0-2 ∷ []) (Sb⁻2-1-0-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·1·0·2⟩ c4)

-- nat 2 SBOX(3;1;42;0): 7 steps
lem-nat-2-SBOX⟨3·1·42·0⟩ : WsL → ⟪ (Sw23 ∷ Sb3-1-42-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-43-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·1·42·0⟩ c4 = derive (Sw23 ∷ Sb3-1-42-0 ∷ []) (Sb2-1-43-0 ∷ Sw23 ∷ [])
  (re 1 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) ∷
   rw 0 (q164 c4) ∷
   rw 1 (q165 c4) ∷
   rw 2 (q166 c4) ∷
   rw 3 (q165 c4) ∷
   rw 4 (q167 c4) ∷
   re 0 5 (Sb2-1-43-0 ∷ []) ∷ []) Eq.refl

private
  q168 : WsL → Eqn
  q168 c4 = eqn (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4)
  q169 : WsL → Eqn
  q169 c4 = eqn (Sw01 ∷ Toff204 ∷ []) (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4)
  q170 : WsL → Eqn
  q170 c4 = eqn (Sw01 ∷ Bx4-23 ∷ []) (Bx4-23 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ))

-- nat 0 BOX(2;403): 8 steps
lem-nat-0-BOX⟨2·403⟩ : WsL → ⟪ (Sw01 ∷ Bx2-403 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-413 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·403⟩ c4 = derive (Sw01 ∷ Bx2-403 ∷ []) (Bx2-413 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-23 ∷ Toff204 ∷ CCZ024 ∷ Bx4-23 ∷ []) ∷
   rw 0 (q168 c4) ∷
   rw 1 (q169 c4) ∷
   rw 2 (q170 c4) ∷
   rw 3 (q169 c4) ∷
   rw 4 (q168 c4) ∷
   rw 5 (q170 c4) ∷
   re 0 6 (Bx2-413 ∷ []) ∷ []) Eq.refl

private
  q171 : WsL → Eqn
  q171 c4 = eqn (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4)
  q172 : WsL → Eqn
  q172 c4 = eqn (Sw01 ∷ Toff412 ∷ []) (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4)
  q173 : WsL → Eqn
  q173 c4 = eqn (Sw01 ∷ Bx2-403 ∷ []) (Bx2-413 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·403⟩ c4)

-- nat 0 BOX(4;2103): 8 steps
lem-nat-0-BOX⟨4·2103⟩ : WsL → ⟪ (Sw01 ∷ Bx4-2103 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2013 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·2103⟩ c4 = derive (Sw01 ∷ Bx4-2103 ∷ []) (Bx4-2013 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-403 ∷ Toff412 ∷ CCZ124 ∷ Bx2-403 ∷ []) ∷
   rw 0 (q171 c4) ∷
   rw 1 (q172 c4) ∷
   rw 2 (q173 c4) ∷
   rw 3 (q172 c4) ∷
   rw 4 (q171 c4) ∷
   rw 5 (q173 c4) ∷
   re 0 6 (Bx4-2013 ∷ []) ∷ []) Eq.refl

private
  q174 : WsL → Eqn
  q174 c4 = eqn (Bx4-02 ∷ Sw34 ∷ []) (Sw34 ∷ Bx4-02 ∷ []) (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))

-- nat 3 BOX(4;02): 2 steps
lem-nat-3-BOX⟨4·02⟩ : WsL → ⟪ (Sw34 ∷ Bx4-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-02 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·02⟩ c4 = derive (Sw34 ∷ Bx4-02 ∷ []) (Bx3-02 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q174 c4) ∷
   re 0 1 (Bx3-02 ∷ []) ∷ []) Eq.refl

private
  q175 : WsL → Eqn
  q175 c4 = eqn (Sw34 ∷ CCZ014 ∷ []) (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4)
  q176 : WsL → Eqn
  q176 c4 = eqn (Sw34 ∷ Toff014 ∷ []) (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4)
  q177 : WsL → Eqn
  q177 c4 = eqn (Sw34 ∷ Bx4-02 ∷ []) (Bx3-02 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·02⟩ c4)

-- nat 3 BOX(0;412): 8 steps
lem-nat-3-BOX⟨0·412⟩ : WsL → ⟪ (Sw34 ∷ Bx0-412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-312 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·412⟩ c4 = derive (Sw34 ∷ Bx0-412 ∷ []) (Bx0-312 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) ∷
   rw 0 (q175 c4) ∷
   rw 1 (q176 c4) ∷
   rw 2 (q177 c4) ∷
   rw 3 (q176 c4) ∷
   rw 4 (q175 c4) ∷
   rw 5 (q177 c4) ∷
   re 0 6 (Bx0-312 ∷ []) ∷ []) Eq.refl

private
  q178 : WsL → Eqn
  q178 c4 = eqn (Sw34 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4)
  q179 : WsL → Eqn
  q179 c4 = eqn (Sw34 ∷ Toff403 ∷ []) (Toff304 ∷ Sw34 ∷ []) (lem-nat-3-TOFF403 c4)
  q180 : WsL → Eqn
  q180 c4 = eqn (Sw34 ∷ Bx0-412 ∷ []) (Bx0-312 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·412⟩ c4)

-- nat 3 BOX(4;0312): 8 steps
lem-nat-3-BOX⟨4·0312⟩ : WsL → ⟪ (Sw34 ∷ Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·0312⟩ c4 = derive (Sw34 ∷ Bx4-0312 ∷ []) (Bx3-0412 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-412 ∷ Toff403 ∷ CCZ034 ∷ Bx0-412 ∷ []) ∷
   rw 0 (q178 c4) ∷
   rw 1 (q179 c4) ∷
   rw 2 (q180 c4) ∷
   rw 3 (q179 c4) ∷
   rw 4 (q178 c4) ∷
   rw 5 (q180 c4) ∷
   re 0 6 (Bx3-0412 ∷ []) ∷ []) Eq.refl

-- nat 2 SBOX(4;0;3;1): 3 steps
lem-nat-2-SBOX⟨4·0·3·1⟩ : WsL → ⟪ (Sw23 ∷ Sb4-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-0-2-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨4·0·3·1⟩ c4 = derive (Sw23 ∷ Sb4-0-3-1 ∷ []) (Sb4-0-2-1 ∷ Sw23 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   rw 0 (q30 c4) ∷
   re 0 1 (Sb4-0-2-1 ∷ []) ∷ []) Eq.refl

private
  q181 : WsL → Eqn
  q181 c4 = eqn (Sb4-0-2-1 ∷ Sw34 ∷ []) (Sw34 ∷ Sb4-0-2-1 ∷ []) (c₃ (Swap ↑ • CS • Swap ↑) (Swap))

-- nat 3 SBOX(4;0;2;1): 2 steps
lem-nat-3-SBOX⟨4·0·2·1⟩ : WsL → ⟪ (Sw34 ∷ Sb4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-2-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨4·0·2·1⟩ c4 = derive (Sw34 ∷ Sb4-0-2-1 ∷ []) (Sb3-0-2-1 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q181 c4) ∷
   re 0 1 (Sb3-0-2-1 ∷ []) ∷ []) Eq.refl

private
  q182 : WsL → Eqn
  q182 c4 = eqn (Sb⁻4-0-2-1 ∷ Sw34 ∷ []) (Sw34 ∷ Sb⁻4-0-2-1 ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (Swap))

-- nat 3 SBOXd(4;0;2;1): 2 steps
lem-nat-3-SBOXd⟨4·0·2·1⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻4-0-2-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-0-2-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨4·0·2·1⟩ c4 = derive (Sw34 ∷ Sb⁻4-0-2-1 ∷ []) (Sb⁻3-0-2-1 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q182 c4) ∷
   re 0 1 (Sb⁻3-0-2-1 ∷ []) ∷ []) Eq.refl

private
  q183 : WsL → Eqn
  q183 c4 = eqn (Toff012 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS))

-- comm SBOXd(0;1;2;3) TOFF034: 17 steps
lem-comm-SBOXd⟨0·1·2·3⟩-TOFF034 : WsL → ⟪ (Sb⁻0-1-2-3 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ
lem-comm-SBOXd⟨0·1·2·3⟩-TOFF034 c4 = derive (Sb⁻0-1-2-3 ∷ Toff034 ∷ []) (Toff034 ∷ Sb⁻0-1-2-3 ∷ [])
  (re 0 1 (CS12⁻ ∷ []) ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q56 c4) ∷
   re 1 3 (CS13⁻ ∷ []) ∷
   rw 1 (q18 c4) ∷
   rw⁻ 2 (q60 c4) ∷
   re 3 3 (CS24⁻ ∷ []) ∷
   rw 3 (q14 c4) ∷
   rw⁻ 4 (q183 c4) ∷
   rw 5 (q13 c4) ∷
   re 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 8 (q60 c4) ∷
   rw 7 (q17 c4) ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 (q56 c4) ∷
   re 0 9 (Toff034 ∷ []) ∷
   re 1 1 (Sb⁻0-1-2-3 ∷ []) ∷ []) Eq.refl

private
  q184 : WsL → Eqn
  q184 c4 = eqn (Toff012 ∷ CS34 ∷ []) (CS34 ∷ Toff012 ∷ []) (c₃ (Toff) (CS))

-- comm SBOX(0;1;2;3) TOFF034: 17 steps
lem-comm-SBOX⟨0·1·2·3⟩-TOFF034 : WsL → ⟪ (Sb0-1-2-3 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ
lem-comm-SBOX⟨0·1·2·3⟩-TOFF034 c4 = derive (Sb0-1-2-3 ∷ Toff034 ∷ []) (Toff034 ∷ Sb0-1-2-3 ∷ [])
  (re 0 1 (CS12 ∷ []) ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ Sw34 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw34 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw⁻ 0 (q56 c4) ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 (q12 c4) ∷
   rw⁻ 2 (q60 c4) ∷
   re 3 3 (CS24 ∷ []) ∷
   rw 3 (q8 c4) ∷
   rw⁻ 4 (q184 c4) ∷
   rw 5 (q7 c4) ∷
   re 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 8 (q60 c4) ∷
   rw 7 (q11 c4) ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 (q56 c4) ∷
   re 0 9 (Toff034 ∷ []) ∷
   re 1 1 (Sb0-1-2-3 ∷ []) ∷ []) Eq.refl

private
  q185 : WsL → Eqn
  q185 c4 = eqn (Sw23 ∷ CCZ024 ∷ []) (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4)
  q186 : WsL → Eqn
  q186 c4 = eqn (Sw23 ∷ Toff204 ∷ []) (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4)
  q187 : WsL → Eqn
  q187 c4 = eqn (Sw23 ∷ Bx0-21 ∷ []) (Bx0-31 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·21⟩ c4)

-- nat 2 BOX(2;041): 8 steps
lem-nat-2-BOX⟨2·041⟩ : WsL → ⟪ (Sw23 ∷ Bx2-041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-041 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·041⟩ c4 = derive (Sw23 ∷ Bx2-041 ∷ []) (Bx3-041 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) ∷
   rw 0 (q185 c4) ∷
   rw 1 (q186 c4) ∷
   rw 2 (q187 c4) ∷
   rw 3 (q186 c4) ∷
   rw 4 (q185 c4) ∷
   rw 5 (q187 c4) ∷
   re 0 6 (Bx3-041 ∷ []) ∷ []) Eq.refl

private
  q188 : WsL → Eqn
  q188 c4 = eqn (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) (wl0093 c4)
  q189 : WsL → Eqn
  q189 c4 = eqn (Sw23 ∷ Bx2-041 ∷ []) (Bx3-041 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·041⟩ c4)

-- nat 2 BOX(0;2341): 8 steps
lem-nat-2-BOX⟨0·2341⟩ : WsL → ⟪ (Sw23 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·2341⟩ c4 = derive (Sw23 ∷ Bx0-2341 ∷ []) (Bx0-3241 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷
   rw 1 (q188 c4) ∷
   rw 2 (q189 c4) ∷
   rw 3 (q188 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw 5 (q189 c4) ∷
   re 0 6 (Bx0-3241 ∷ []) ∷ []) Eq.refl

private
  q190 : WsL → Eqn
  q190 c4 = eqn (CS12 ∷ Sw12 ∷ []) (Sw12 ∷ CS12 ∷ []) (wl0134 c4)

-- nat 1 SBOX(3;2;1;0): 3 steps
lem-nat-1-SBOX⟨3·2·1·0⟩ : WsL → ⟪ (Sw12 ∷ Sb3-2-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·2·1·0⟩ c4 = derive (Sw12 ∷ Sb3-2-1-0 ∷ []) (Sb3-1-2-0 ∷ Sw12 ∷ [])
  (re 1 1 (CS12 ∷ []) ∷
   rw⁻ 0 (q190 c4) ∷
   re 0 1 (Sb3-1-2-0 ∷ []) ∷ []) Eq.refl

private
  q191 : WsL → Eqn
  q191 c4 = eqn (CS12⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS12⁻ ∷ []) (wl0135 c4)

-- nat 1 SBOXd(3;2;1;0): 3 steps
lem-nat-1-SBOXd⟨3·2·1·0⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻3-2-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-1-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·2·1·0⟩ c4 = derive (Sw12 ∷ Sb⁻3-2-1-0 ∷ []) (Sb⁻3-1-2-0 ∷ Sw12 ∷ [])
  (re 1 1 (CS12⁻ ∷ []) ∷
   rw⁻ 0 (q191 c4) ∷
   re 0 1 (Sb⁻3-1-2-0 ∷ []) ∷ []) Eq.refl

private
  q192 : WsL → Eqn
  q192 c4 = eqn (Sw12 ∷ Bx3-2401 ∷ []) (Bx3-1402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·2401⟩ c4)
  q193 : WsL → Eqn
  q193 c4 = eqn (Sw12 ∷ Toff104 ∷ []) (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4)
  q194 : WsL → Eqn
  q194 c4 = eqn (Sw12 ∷ Sb3-2-1-0 ∷ []) (Sb3-1-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·2·1·0⟩ c4)
  q195 : WsL → Eqn
  q195 c4 = eqn (Sw12 ∷ Sb⁻3-2-1-0 ∷ []) (Sb⁻3-1-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·2·1·0⟩ c4)

-- nat 1 SBOX(3;2;40;1): 7 steps
lem-nat-1-SBOX⟨3·2·40·1⟩ : WsL → ⟪ (Sw12 ∷ Sb3-2-40-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-40-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·2·40·1⟩ c4 = derive (Sw12 ∷ Sb3-2-40-1 ∷ []) (Sb3-1-40-2 ∷ Sw12 ∷ [])
  (re 1 1 (Bx3-2401 ∷ Toff104 ∷ Sb3-2-1-0 ∷ Toff104 ∷ Sb⁻3-2-1-0 ∷ []) ∷
   rw 0 (q192 c4) ∷
   rw 1 (q193 c4) ∷
   rw 2 (q194 c4) ∷
   rw 3 (q193 c4) ∷
   rw 4 (q195 c4) ∷
   re 0 5 (Sb3-1-40-2 ∷ []) ∷ []) Eq.refl

private
  q196 : WsL → Eqn
  q196 c4 = eqn (Sw23 ∷ Bx2-1403 ∷ []) (Bx3-1402 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·1403⟩ c4)
  q197 : WsL → Eqn
  q197 c4 = eqn (Sw23 ∷ Toff304 ∷ []) (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4)
  q198 : WsL → Eqn
  q198 c4 = eqn (Sw23 ∷ Sb2-1-3-0 ∷ []) (Sb3-1-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·1·3·0⟩ c4)
  q199 : WsL → Eqn
  q199 c4 = eqn (Sw23 ∷ Sb⁻2-1-3-0 ∷ []) (Sb⁻3-1-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨2·1·3·0⟩ c4)

-- nat 2 SBOX(2;1;40;3): 7 steps
lem-nat-2-SBOX⟨2·1·40·3⟩ : WsL → ⟪ (Sw23 ∷ Sb2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-40-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·1·40·3⟩ c4 = derive (Sw23 ∷ Sb2-1-40-3 ∷ []) (Sb3-1-40-2 ∷ Sw23 ∷ [])
  (re 1 1 (Bx2-1403 ∷ Toff304 ∷ Sb2-1-3-0 ∷ Toff304 ∷ Sb⁻2-1-3-0 ∷ []) ∷
   rw 0 (q196 c4) ∷
   rw 1 (q197 c4) ∷
   rw 2 (q198 c4) ∷
   rw 3 (q197 c4) ∷
   rw 4 (q199 c4) ∷
   re 0 5 (Sb3-1-40-2 ∷ []) ∷ []) Eq.refl

private
  q200 : WsL → Eqn
  q200 c4 = eqn (Sw23 ∷ Bx3-1402 ∷ []) (Bx2-1403 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·1402⟩ c4)
  q201 : WsL → Eqn
  q201 c4 = eqn (Sw23 ∷ Sb3-1-2-0 ∷ []) (Sb2-1-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·1·2·0⟩ c4)
  q202 : WsL → Eqn
  q202 c4 = eqn (Sw23 ∷ Sb⁻3-1-2-0 ∷ []) (Sb⁻2-1-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·1·2·0⟩ c4)

-- nat 2 SBOX(3;1;40;2): 7 steps
lem-nat-2-SBOX⟨3·1·40·2⟩ : WsL → ⟪ (Sw23 ∷ Sb3-1-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-40-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·1·40·2⟩ c4 = derive (Sw23 ∷ Sb3-1-40-2 ∷ []) (Sb2-1-40-3 ∷ Sw23 ∷ [])
  (re 1 1 (Bx3-1402 ∷ Toff204 ∷ Sb3-1-2-0 ∷ Toff204 ∷ Sb⁻3-1-2-0 ∷ []) ∷
   rw 0 (q200 c4) ∷
   rw 1 (q186 c4) ∷
   rw 2 (q201 c4) ∷
   rw 3 (q186 c4) ∷
   rw 4 (q202 c4) ∷
   re 0 5 (Sb2-1-40-3 ∷ []) ∷ []) Eq.refl

-- nat 2 SBOX(0;2;1;4): 3 steps
lem-nat-2-SBOX⟨0·2·1·4⟩ : WsL → ⟪ (Sw23 ∷ Sb0-2-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-3-1-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·2·1·4⟩ c4 = derive (Sw23 ∷ Sb0-2-1-4 ∷ []) (Sb0-3-1-4 ∷ Sw23 ∷ [])
  (re 1 1 (CS12 ∷ []) ∷
   rw 0 (q136 c4) ∷
   re 0 1 (Sb0-3-1-4 ∷ []) ∷ []) Eq.refl

private
  q203 : WsL → Eqn
  q203 c4 = eqn (Sb0-2-1-3 ∷ Sw34 ∷ []) (Sw34 ∷ Sb0-2-1-3 ∷ []) (c₃ (CS ↑) (Swap))

-- nat 3 SBOX(0;2;1;3): 2 steps
lem-nat-3-SBOX⟨0·2·1·3⟩ : WsL → ⟪ (Sw34 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·2·1·3⟩ c4 = derive (Sw34 ∷ Sb0-2-1-3 ∷ []) (Sb0-2-1-4 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q203 c4) ∷
   re 0 1 (Sb0-2-1-4 ∷ []) ∷ []) Eq.refl

private
  q204 : WsL → Eqn
  q204 c4 = eqn (Sb0-2-1-4 ∷ Sw34 ∷ []) (Sw34 ∷ Sb0-2-1-4 ∷ []) (c₃ (CS ↑) (Swap))

-- nat 3 SBOX(0;2;1;4): 2 steps
lem-nat-3-SBOX⟨0·2·1·4⟩ : WsL → ⟪ (Sw34 ∷ Sb0-2-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨0·2·1·4⟩ c4 = derive (Sw34 ∷ Sb0-2-1-4 ∷ []) (Sb0-2-1-3 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q204 c4) ∷
   re 0 1 (Sb0-2-1-3 ∷ []) ∷ []) Eq.refl

-- nat 2 SBOXd(0;2;1;4): 3 steps
lem-nat-2-SBOXd⟨0·2·1·4⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻0-2-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-3-1-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨0·2·1·4⟩ c4 = derive (Sw23 ∷ Sb⁻0-2-1-4 ∷ []) (Sb⁻0-3-1-4 ∷ Sw23 ∷ [])
  (re 1 1 (CS12⁻ ∷ []) ∷
   rw 0 (q138 c4) ∷
   re 0 1 (Sb⁻0-3-1-4 ∷ []) ∷ []) Eq.refl

private
  q205 : WsL → Eqn
  q205 c4 = eqn (Sb⁻0-2-1-3 ∷ Sw34 ∷ []) (Sw34 ∷ Sb⁻0-2-1-3 ∷ []) (c₃ ((CS • CS • CS) ↑) (Swap))

-- nat 3 SBOXd(0;2;1;3): 2 steps
lem-nat-3-SBOXd⟨0·2·1·3⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·2·1·3⟩ c4 = derive (Sw34 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-2-1-4 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q205 c4) ∷
   re 0 1 (Sb⁻0-2-1-4 ∷ []) ∷ []) Eq.refl

private
  q206 : WsL → Eqn
  q206 c4 = eqn (Sb⁻0-2-1-4 ∷ Sw34 ∷ []) (Sw34 ∷ Sb⁻0-2-1-4 ∷ []) (c₃ ((CS • CS • CS) ↑) (Swap))

-- nat 3 SBOXd(0;2;1;4): 2 steps
lem-nat-3-SBOXd⟨0·2·1·4⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻0-2-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨0·2·1·4⟩ c4 = derive (Sw34 ∷ Sb⁻0-2-1-4 ∷ []) (Sb⁻0-2-1-3 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q206 c4) ∷
   re 0 1 (Sb⁻0-2-1-3 ∷ []) ∷ []) Eq.refl

private
  q207 : WsL → Eqn
  q207 c4 = eqn (CX30 ∷ Sw01 ∷ []) (Sw01 ∷ CX31 ∷ []) (wl0122 c4)

-- resp CX30 at 1: 2 steps
lem-resp-CX30-at-1 : WsL → ⟪ (CX30 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX31 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX30-at-1 c4 = derive (CX30 ∷ []) (Sw01 ∷ CX31 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q19 c4) ∷
   rw 0 (q207 c4) ∷ []) Eq.refl

private
  q208 : WsL → Eqn
  q208 c4 = eqn (Sw34 ∷ CZ24 ∷ []) (CZ23 ∷ Sw34 ∷ []) (lem-nat-3-CZ24 c4)

-- nat 3 BOX(0;42): 3 steps
lem-nat-3-BOX⟨0·42⟩ : WsL → ⟪ (Sw34 ∷ Bx0-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-32 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·42⟩ c4 = derive (Sw34 ∷ Bx0-42 ∷ []) (Bx0-32 ∷ Sw34 ∷ [])
  (re 1 1 (CZ24 ∷ []) ∷
   rw 0 (q208 c4) ∷
   re 0 1 (Bx0-32 ∷ []) ∷ []) Eq.refl

private
  q209 : WsL → Eqn
  q209 c4 = eqn (Sw34 ∷ Toff401 ∷ []) (Toff301 ∷ Sw34 ∷ []) (lem-nat-3-TOFF401 c4)
  q210 : WsL → Eqn
  q210 c4 = eqn (Sw34 ∷ Bx0-42 ∷ []) (Bx0-32 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·42⟩ c4)

-- nat 3 BOX(4;012): 8 steps
lem-nat-3-BOX⟨4·012⟩ : WsL → ⟪ (Sw34 ∷ Bx4-012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-012 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·012⟩ c4 = derive (Sw34 ∷ Bx4-012 ∷ []) (Bx3-012 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) ∷
   rw 0 (q175 c4) ∷
   rw 1 (q209 c4) ∷
   rw 2 (q210 c4) ∷
   rw 3 (q209 c4) ∷
   rw 4 (q175 c4) ∷
   rw 5 (q210 c4) ∷
   re 0 6 (Bx3-012 ∷ []) ∷ []) Eq.refl

private
  q211 : WsL → Eqn
  q211 c4 = eqn (Sw34 ∷ Toff034 ∷ []) (Toff034 ∷ Sw34 ∷ []) (lem-nat-3-TOFF034 c4)
  q212 : WsL → Eqn
  q212 c4 = eqn (Sw34 ∷ Bx4-012 ∷ []) (Bx3-012 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·012⟩ c4)

-- nat 3 BOX(0;4312): 8 steps
lem-nat-3-BOX⟨0·4312⟩ : WsL → ⟪ (Sw34 ∷ Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·4312⟩ c4 = derive (Sw34 ∷ Bx0-4312 ∷ []) (Bx0-3412 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) ∷
   rw 0 (q178 c4) ∷
   rw 1 (q211 c4) ∷
   rw 2 (q212 c4) ∷
   rw 3 (q211 c4) ∷
   rw 4 (q178 c4) ∷
   rw 5 (q212 c4) ∷
   re 0 6 (Bx0-3412 ∷ []) ∷ []) Eq.refl

private
  q213 : WsL → Eqn
  q213 c4 = eqn (Sw34 ∷ CCZ013 ∷ []) (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4)
  q214 : WsL → Eqn
  q214 c4 = eqn (Sw34 ∷ Toff301 ∷ []) (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4)
  q215 : WsL → Eqn
  q215 c4 = eqn (Sw34 ∷ Bx0-32 ∷ []) (Bx0-42 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·32⟩ c4)

-- nat 3 BOX(3;012): 8 steps
lem-nat-3-BOX⟨3·012⟩ : WsL → ⟪ (Sw34 ∷ Bx3-012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-012 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·012⟩ c4 = derive (Sw34 ∷ Bx3-012 ∷ []) (Bx4-012 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-32 ∷ Toff301 ∷ CCZ013 ∷ Bx0-32 ∷ []) ∷
   rw 0 (q213 c4) ∷
   rw 1 (q214 c4) ∷
   rw 2 (q215 c4) ∷
   rw 3 (q214 c4) ∷
   rw 4 (q213 c4) ∷
   rw 5 (q215 c4) ∷
   re 0 6 (Bx4-012 ∷ []) ∷ []) Eq.refl

private
  q216 : WsL → Eqn
  q216 c4 = eqn (Sw34 ∷ Bx3-012 ∷ []) (Bx4-012 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·012⟩ c4)

-- nat 3 BOX(0;3412): 8 steps
lem-nat-3-BOX⟨0·3412⟩ : WsL → ⟪ (Sw34 ∷ Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·3412⟩ c4 = derive (Sw34 ∷ Bx0-3412 ∷ []) (Bx0-4312 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-012 ∷ Toff034 ∷ CCZ034 ∷ Bx3-012 ∷ []) ∷
   rw 0 (q178 c4) ∷
   rw 1 (q211 c4) ∷
   rw 2 (q216 c4) ∷
   rw 3 (q211 c4) ∷
   rw 4 (q178 c4) ∷
   rw 5 (q216 c4) ∷
   re 0 6 (Bx0-4312 ∷ []) ∷ []) Eq.refl

private
  q217 : WsL → Eqn
  q217 c4 = eqn (Sw01 ∷ CCZ034 ∷ []) (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4)
  q218 : WsL → Eqn
  q218 c4 = eqn (Sw01 ∷ Toff034 ∷ []) (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4)
  q219 : WsL → Eqn
  q219 c4 = eqn (Sw01 ∷ Bx3-01 ∷ []) (Bx3-10 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·01⟩ c4)

-- nat 0 BOX(0;341): 8 steps
lem-nat-0-BOX⟨0·341⟩ : WsL → ⟪ (Sw01 ∷ Bx0-341 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-340 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·341⟩ c4 = derive (Sw01 ∷ Bx0-341 ∷ []) (Bx1-340 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) ∷
   rw 0 (q217 c4) ∷
   rw 1 (q218 c4) ∷
   rw 2 (q219 c4) ∷
   rw 3 (q218 c4) ∷
   rw 4 (q217 c4) ∷
   rw 5 (q219 c4) ∷
   re 0 6 (Bx1-340 ∷ []) ∷ []) Eq.refl

private
  q220 : WsL → Eqn
  q220 c4 = eqn (CCZ123 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ023 ∷ []) (wl0103 c4)
  q221 : WsL → Eqn
  q221 c4 = eqn (Sw01 ∷ Toff302 ∷ []) (Toff312 ∷ Sw01 ∷ []) (wl0116 c4)
  q222 : WsL → Eqn
  q222 c4 = eqn (Sw01 ∷ Bx0-341 ∷ []) (Bx1-340 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·341⟩ c4)

-- nat 0 BOX(3;0241): 8 steps
lem-nat-0-BOX⟨3·0241⟩ : WsL → ⟪ (Sw01 ∷ Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·0241⟩ c4 = derive (Sw01 ∷ Bx3-0241 ∷ []) (Bx3-1240 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-341 ∷ Toff302 ∷ CCZ023 ∷ Bx0-341 ∷ []) ∷
   rw⁻ 0 (q220 c4) ∷
   rw 1 (q221 c4) ∷
   rw 2 (q222 c4) ∷
   rw 3 (q221 c4) ∷
   rw⁻ 4 (q220 c4) ∷
   rw 5 (q222 c4) ∷
   re 0 6 (Bx3-1240 ∷ []) ∷ []) Eq.refl

private
  q223 : WsL → Eqn
  q223 c4 = eqn (Sw01 ∷ CCZ134 ∷ []) (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4)
  q224 : WsL → Eqn
  q224 c4 = eqn (Sw01 ∷ Bx3-10 ∷ []) (Bx3-01 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·10⟩ c4)

-- nat 0 BOX(1;340): 8 steps
lem-nat-0-BOX⟨1·340⟩ : WsL → ⟪ (Sw01 ∷ Bx1-340 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-341 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·340⟩ c4 = derive (Sw01 ∷ Bx1-340 ∷ []) (Bx0-341 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) ∷
   rw 0 (q223 c4) ∷
   rw 1 (q142 c4) ∷
   rw 2 (q224 c4) ∷
   rw 3 (q142 c4) ∷
   rw 4 (q223 c4) ∷
   rw 5 (q224 c4) ∷
   re 0 6 (Bx0-341 ∷ []) ∷ []) Eq.refl

private
  q225 : WsL → Eqn
  q225 c4 = eqn (CCZ023 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ123 ∷ []) (wl0003 c4)
  q226 : WsL → Eqn
  q226 c4 = eqn (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) (wl0110 c4)
  q227 : WsL → Eqn
  q227 c4 = eqn (Sw01 ∷ Bx1-340 ∷ []) (Bx0-341 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·340⟩ c4)

-- nat 0 BOX(3;1240): 8 steps
lem-nat-0-BOX⟨3·1240⟩ : WsL → ⟪ (Sw01 ∷ Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·1240⟩ c4 = derive (Sw01 ∷ Bx3-1240 ∷ []) (Bx3-0241 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-340 ∷ Toff312 ∷ CCZ123 ∷ Bx1-340 ∷ []) ∷
   rw⁻ 0 (q225 c4) ∷
   rw 1 (q226 c4) ∷
   rw 2 (q227 c4) ∷
   rw 3 (q226 c4) ∷
   rw⁻ 4 (q225 c4) ∷
   rw 5 (q227 c4) ∷
   re 0 6 (Bx3-0241 ∷ []) ∷ []) Eq.refl
