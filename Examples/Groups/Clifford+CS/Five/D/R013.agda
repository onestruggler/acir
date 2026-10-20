{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R013 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0015 ; wl0016 ; wl0017 ; wl0018 ; wl0019 ; wl0020 ; wl0021 ; wl0022 ; wl0024 ; wl0025 ; wl0026 ; wl0027 ; wl0028 ; wl0029 ; wl0030 ; wl0031 ; wl0032 ; wl0034 ; wl0037 ; wl0038 ; wl0043 ; wl0044 ; wl0045 ; wl0046 ; wl0047 ; wl0061 ; wl0063 ; wl0066 ; wl0078 ; wl0084 ; wl0085 ; wl0086 ; wl0088 ; wl0090 ; wl0091 ; wl0092 ; wl0095 ; wl0096 ; wl0097 ; wl0099 ; wl0115 ; wl0121 ; wl0126 ; wl0127 ; wl0128 ; wl0129 ; wl0144 ; wl0152 ; wl0153 ; wl0154 ; wl0155)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ024 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-2-TOFF301 ; lem-nat-3-TOFF013 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF301 ; lem-nat-1-TOFF302 ; lem-nat-2-CCZ124 ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF201 ; lem-nat-2-TOFF204 ; lem-nat-2-TOFF304 ; lem-nat-3-CCZ013 ; lem-nat-3-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-TOFF014 ; lem-nat-0-TOFF104 ; lem-nat-0-TOFF304 ; lem-nat-0-TOFF314 ; lem-nat-0-TOFF412 ; lem-nat-1-BOX⟨2·43⟩ ; lem-nat-1-TOFF104 ; lem-nat-1-TOFF204 ; lem-nat-2-TOFF413 ; lem-nat-3-CZ23)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-TOFF204 ; lem-nat-0-TOFF214 ; lem-nat-0-TOFF402 ; lem-nat-1-TOFF304 ; lem-nat-2-TOFF412 ; lem-nat-3-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-1-TOFF401 ; lem-nat-2-CCZ014 ; lem-nat-2-CZ04 ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124 ; lem-nat-3-CZ03 ; lem-nat-3-CZ04)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-BOXd⟨2·43⟩ ; lem-nat-3-CZ24)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-BOX⟨2·0413⟩ ; lem-nat-0-BOX⟨2·4013⟩ ; lem-nat-1-CS04 ; lem-nat-2-TOFF124 ; lem-nat-3-CS23)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-1-CSd04 ; lem-nat-2-CS04 ; lem-nat-2-CSd04 ; lem-nat-3-CS04 ; lem-nat-3-CSd04 ; lem-nat-3-TOFF412)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-1-TOFF402 ; lem-nat-2-TOFF401 ; lem-nat-3-CS03 ; lem-nat-3-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-nat-2-TOFF134)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-nat-0-BOX⟨2·3401⟩ ; lem-nat-0-BOX⟨2·3410⟩ ; lem-nat-0-SBOX⟨2·1·3·0⟩ ; lem-nat-0-SBOXd⟨2·1·3·0⟩ ; lem-nat-1-BOX⟨1·3402⟩ ; lem-nat-1-BOX⟨2·1403⟩ ; lem-nat-1-BOX⟨2·3401⟩ ; lem-nat-1-BOX⟨3·40⟩ ; lem-nat-1-SBOX⟨1·2·3·0⟩ ; lem-nat-1-SBOXd⟨1·2·3·0⟩ ; lem-nat-2-SBOX⟨1·3·2·0⟩ ; lem-nat-2-SBOX⟨1·4·2·0⟩ ; lem-nat-2-SBOXd⟨1·3·2·0⟩ ; lem-nat-2-SBOXd⟨1·4·2·0⟩)

private
  q1 : WsL → Eqn
  q1 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 c4)
  q2 : WsL → Eqn
  q2 c4 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (c₁ (K) (Swap ↑))
  q3 : WsL → Eqn
  q3 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 c4)
  q4 : WsL → Eqn
  q4 c4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap))
  q5 : WsL → Eqn
  q5 c4 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (c₁ (iI) (Swap ↑))
  q6 : WsL → Eqn
  q6 c4 = eqn (K0 ∷ Sw34 ∷ []) (Sw34 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑))
  q7 : WsL → Eqn
  q7 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 c4)
  q8 : WsL → Eqn
  q8 c4 = eqn (CX01 ∷ Sw34 ∷ []) (Sw34 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap ↑))
  q9 : WsL → Eqn
  q9 c4 = eqn (ι ∷ Sw34 ∷ []) (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑))
  q10 : WsL → Eqn
  q10 c4 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (c₁ (K) (Swap))
  q11 : WsL → Eqn
  q11 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0008 c4)
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
  q20 c4 = eqn (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) (wl0014 c4)
  q21 : WsL → Eqn
  q21 c4 = eqn (Sw12 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS))
  q22 : WsL → Eqn
  q22 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q23 : WsL → Eqn
  q23 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl0015 c4)
  q24 : WsL → Eqn
  q24 c4 = eqn (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) (wl0016 c4)
  q25 : WsL → Eqn
  q25 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl0017 c4)
  q26 : WsL → Eqn
  q26 c4 = eqn (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ []) (wl0018 c4)
  q27 : WsL → Eqn
  q27 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 c4)
  q28 : WsL → Eqn
  q28 c4 = eqn (Sw01 ∷ ι ∷ []) (ι ∷ Sw01 ∷ []) (wl0030 c4)
  q29 : WsL → Eqn
  q29 c4 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wl0031 c4)
  q30 : WsL → Eqn
  q30 c4 = eqn (Sw01 ∷ Sw34 ∷ []) (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑))
  q31 : WsL → Eqn
  q31 c4 = eqn (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) (wl0019 c4)
  q32 : WsL → Eqn
  q32 c4 = eqn (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) (wl0020 c4)
  q33 : WsL → Eqn
  q33 c4 = eqn (Sw01 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑))
  q34 : WsL → Eqn
  q34 c4 = eqn (Sw01 ∷ CS34 ∷ []) (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))
  q35 : WsL → Eqn
  q35 c4 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (c₂ (K ↑) (Swap))
  q36 : WsL → Eqn
  q36 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl0021 c4)
  q37 : WsL → Eqn
  q37 c4 = eqn (K1 ∷ Sw34 ∷ []) (Sw34 ∷ K1 ∷ []) (c₂ (K ↑) (Swap ↑))
  q38 : WsL → Eqn
  q38 c4 = eqn (CX12 ∷ Sw34 ∷ []) (Sw34 ∷ CX12 ∷ []) (c₃ (CX₀₁ ↑) (Swap))
  q39 : WsL → Eqn
  q39 c4 = eqn (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wl0032 c4)

-- resp TOFF034 at 2: 236 steps
lem-resp-TOFF034-at-2 : WsL → ⟪ (Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff134 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF034-at-2 c4 = derive (Toff034 ∷ []) (Sw12 ∷ Sw01 ∷ Toff134 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q1 c4) ∷
   re 0 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) ∷
   re 1 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 10 (q3 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 (q2 c4) ∷
   rw⁻ 10 (q5 c4) ∷
   rw 11 (q3 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q8 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q8 c4) ∷
   rw⁻ 9 (q7 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q6 c4) ∷
   rw⁻ 9 (q9 c4) ∷
   rw 10 (q7 c4) ∷
   rw⁻ 1 (q10 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q12 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q13 c4) ∷
   rw⁻ 7 (q14 c4) ∷
   rw 8 (q13 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q10 c4) ∷
   rw⁻ 8 (q15 c4) ∷
   rw 9 (q1 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw⁻ 1 (q16 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 2 3 (CX03 ∷ []) ∷
   rw⁻ 3 (q17 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (CX03 ∷ []) ∷
   re 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q18 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   re 5 7 (CS04 ∷ []) ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw 8 (q3 c4) ∷
   rw 7 (q15 c4) ∷
   rw 6 (q10 c4) ∷
   re 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 7 (q13 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 5 (q13 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw 4 (q20 c4) ∷
   rw⁻ 3 (q21 c4) ∷
   rw 2 (q20 c4) ∷
   rw⁻ 1 (q22 c4) ∷
   rw 0 (q10 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   re 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q24 c4) ∷
   re 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 6 (q3 c4) ∷
   re 8 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 7 (q18 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw⁻ 10 (q19 c4) ∷
   rw⁻ 11 (q13 c4) ∷
   rw⁻ 12 (q18 c4) ∷
   re 7 7 (CS04 ∷ []) ∷
   rw⁻ 8 (q2 c4) ∷
   rw⁻ 9 (q5 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   rw⁻ 4 (q25 c4) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 6 (q26 c4) ∷
   re 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 7 (q1 c4) ∷
   re 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 8 (q13 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw 10 (q13 c4) ∷
   re 8 3 (CS04 ∷ []) ∷
   rw⁻ 9 (q10 c4) ∷
   rw⁻ 10 (q15 c4) ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 6 (q8 c4) ∷
   re 8 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   re 10 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   rw⁻ 11 (q9 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 (q3 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 (q3 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 (q3 c4) ∷
   rw⁻ 11 (q2 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   re 5 8 (Toff012 ∷ []) ∷
   re 4 3 (Toff013 ∷ []) ∷
   re 3 3 (Toff014 ∷ []) ∷
   re 2 3 (Toff024 ∷ []) ∷
   re 1 3 (Toff034 ∷ []) ∷
   rw⁻ 2 (q27 c4) ∷
   re 1 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) ∷
   re 3 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   re 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 4 (q2 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 (q4 c4) ∷
   rw⁻ 11 (q3 c4) ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 (q2 c4) ∷
   rw⁻ 11 (q5 c4) ∷
   rw 12 (q3 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   re 4 3 (CS14 ∷ []) ∷
   rw⁻ 5 (q8 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   re 6 3 (CS14⁻ ∷ []) ∷
   rw⁻ 7 (q8 c4) ∷
   rw⁻ 10 (q7 c4) ∷
   re 8 3 (CS04 ∷ []) ∷
   rw⁻ 9 (q6 c4) ∷
   rw⁻ 10 (q9 c4) ∷
   rw 11 (q7 c4) ∷
   rw⁻ 2 (q10 c4) ∷
   rw⁻ 3 (q11 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw⁻ 5 (q12 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q13 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw 9 (q13 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q10 c4) ∷
   rw⁻ 9 (q15 c4) ∷
   rw 10 (q1 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   rw⁻ 2 (q16 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (CX03 ∷ []) ∷
   rw⁻ 4 (q17 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (CX03 ∷ []) ∷
   re 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 6 (q18 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw⁻ 10 (q13 c4) ∷
   rw⁻ 11 (q18 c4) ∷
   re 6 7 (CS04 ∷ []) ∷
   rw⁻ 7 (q2 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw 9 (q3 c4) ∷
   rw⁻ 8 (q28 c4) ∷
   rw 7 (q29 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q30 c4) ∷
   rw 7 (q31 c4) ∷
   rw⁻ 6 (q30 c4) ∷
   re 7 3 (CS14 ∷ []) ∷
   rw 5 (q32 c4) ∷
   rw⁻ 4 (q33 c4) ∷
   rw 3 (q32 c4) ∷
   rw⁻ 2 (q34 c4) ∷
   rw 1 (q29 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 3 (q35 c4) ∷
   rw⁻ 4 (q23 c4) ∷
   re 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 6 (q24 c4) ∷
   re 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 7 (q3 c4) ∷
   rw⁻ 8 (q36 c4) ∷
   rw⁻ 9 (q35 c4) ∷
   rw⁻ 10 (q5 c4) ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 4 (q37 c4) ∷
   re 6 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 6 (q38 c4) ∷
   re 8 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 8 (q38 c4) ∷
   re 10 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 10 (q37 c4) ∷
   rw⁻ 11 (q9 c4) ∷
   rw 4 (q39 c4) ∷
   re 4 8 (Toff123 ∷ []) ∷
   re 3 3 (Toff124 ∷ []) ∷
   re 2 3 (Toff134 ∷ []) ∷ []) Eq.refl

private
  q40 : WsL → Eqn
  q40 c4 = eqn (Sw12 ∷ Toff423 ∷ []) (Toff413 ∷ Sw12 ∷ []) (wl0091 c4)
  q41 : WsL → Eqn
  q41 c4 = eqn (Sw01 ∷ Toff423 ∷ []) (Toff423 ∷ Sw01 ∷ []) (c₂ (Swap) (Toffᵗ))

-- resp TOFF412 at 3: 7 steps
lem-resp-TOFF412-at-3 : WsL → ⟪ (Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff423 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF412-at-3 c4 = derive (Toff412 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff423 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q3 c4) ∷
   rw⁻ 0 (q3 c4) ∷
   re 1 3 (Toff413 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 1 (q40 c4) ∷
   rw⁻ 3 (q27 c4) ∷
   rw⁻ 2 (q41 c4) ∷ []) Eq.refl

private
  q42 : WsL → Eqn
  q42 c4 = eqn (CZ24 ∷ Sw23 ∷ []) (Sw23 ∷ CZ34 ∷ []) (wl0027 c4)

-- nat 2 BOX(1;43): 3 steps
lem-nat-2-BOX⟨1·43⟩ : WsL → ⟪ (Sw23 ∷ Bx1-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-42 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·43⟩ c4 = derive (Sw23 ∷ Bx1-43 ∷ []) (Bx1-42 ∷ Sw23 ∷ [])
  (re 1 1 (CZ34 ∷ []) ∷
   rw⁻ 0 (q42 c4) ∷
   re 0 1 (Bx1-42 ∷ []) ∷ []) Eq.refl

private
  q43 : WsL → Eqn
  q43 c4 = eqn (Sw23 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4)
  q44 : WsL → Eqn
  q44 c4 = eqn (Sw23 ∷ Toff401 ∷ []) (Toff401 ∷ Sw23 ∷ []) (lem-nat-2-TOFF401 c4)
  q45 : WsL → Eqn
  q45 c4 = eqn (Sw23 ∷ Bx1-43 ∷ []) (Bx1-42 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·43⟩ c4)

-- nat 2 BOX(4;103): 8 steps
lem-nat-2-BOX⟨4·103⟩ : WsL → ⟪ (Sw23 ∷ Bx4-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-102 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·103⟩ c4 = derive (Sw23 ∷ Bx4-103 ∷ []) (Bx4-102 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-43 ∷ Toff401 ∷ CCZ014 ∷ Bx1-43 ∷ []) ∷
   rw 0 (q43 c4) ∷
   rw 1 (q44 c4) ∷
   rw 2 (q45 c4) ∷
   rw 3 (q44 c4) ∷
   rw 4 (q43 c4) ∷
   rw 5 (q45 c4) ∷
   re 0 6 (Bx4-102 ∷ []) ∷ []) Eq.refl

private
  q46 : WsL → Eqn
  q46 c4 = eqn (Sw23 ∷ CCZ124 ∷ []) (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4)
  q47 : WsL → Eqn
  q47 c4 = eqn (Sw23 ∷ Toff124 ∷ []) (Toff134 ∷ Sw23 ∷ []) (lem-nat-2-TOFF124 c4)
  q48 : WsL → Eqn
  q48 c4 = eqn (Sw23 ∷ Bx4-103 ∷ []) (Bx4-102 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·103⟩ c4)

-- nat 2 BOX(1;4203): 8 steps
lem-nat-2-BOX⟨1·4203⟩ : WsL → ⟪ (Sw23 ∷ Bx1-4203 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4302 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·4203⟩ c4 = derive (Sw23 ∷ Bx1-4203 ∷ []) (Bx1-4302 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-103 ∷ Toff124 ∷ CCZ124 ∷ Bx4-103 ∷ []) ∷
   rw 0 (q46 c4) ∷
   rw 1 (q47 c4) ∷
   rw 2 (q48 c4) ∷
   rw 3 (q47 c4) ∷
   rw 4 (q46 c4) ∷
   rw 5 (q48 c4) ∷
   re 0 6 (Bx1-4302 ∷ []) ∷ []) Eq.refl

-- nat 2 SBOX(1;4;3;0): 3 steps
lem-nat-2-SBOX⟨1·4·3·0⟩ : WsL → ⟪ (Sw23 ∷ Sb1-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-2-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·4·3·0⟩ c4 = derive (Sw23 ∷ Sb1-4-3-0 ∷ []) (Sb1-4-2-0 ∷ Sw23 ∷ [])
  (re 1 1 (CS34 ∷ []) ∷
   rw⁻ 0 (q23 c4) ∷
   re 0 1 (Sb1-4-2-0 ∷ []) ∷ []) Eq.refl

-- nat 2 SBOXd(1;4;3;0): 3 steps
lem-nat-2-SBOXd⟨1·4·3·0⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-2-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·4·3·0⟩ c4 = derive (Sw23 ∷ Sb⁻1-4-3-0 ∷ []) (Sb⁻1-4-2-0 ∷ Sw23 ∷ [])
  (re 1 1 (CS34⁻ ∷ []) ∷
   rw⁻ 0 (q24 c4) ∷
   re 0 1 (Sb⁻1-4-2-0 ∷ []) ∷ []) Eq.refl

private
  q49 : WsL → Eqn
  q49 c4 = eqn (Sw23 ∷ Bx1-4203 ∷ []) (Bx1-4302 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·4203⟩ c4)
  q50 : WsL → Eqn
  q50 c4 = eqn (Sw23 ∷ Toff302 ∷ []) (Toff203 ∷ Sw23 ∷ []) (wl0066 c4)
  q51 : WsL → Eqn
  q51 c4 = eqn (Sw23 ∷ Sb1-4-3-0 ∷ []) (Sb1-4-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·4·3·0⟩ c4)
  q52 : WsL → Eqn
  q52 c4 = eqn (Sw23 ∷ Sb⁻1-4-3-0 ∷ []) (Sb⁻1-4-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·4·3·0⟩ c4)

-- nat 2 SBOX(1;4;20;3): 7 steps
lem-nat-2-SBOX⟨1·4·20·3⟩ : WsL → ⟪ (Sw23 ∷ Sb1-4-20-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-30-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·4·20·3⟩ c4 = derive (Sw23 ∷ Sb1-4-20-3 ∷ []) (Sb1-4-30-2 ∷ Sw23 ∷ [])
  (re 1 1 (Bx1-4203 ∷ Toff302 ∷ Sb1-4-3-0 ∷ Toff302 ∷ Sb⁻1-4-3-0 ∷ []) ∷
   rw 0 (q49 c4) ∷
   rw 1 (q50 c4) ∷
   rw 2 (q51 c4) ∷
   rw 3 (q50 c4) ∷
   rw 4 (q52 c4) ∷
   re 0 5 (Sb1-4-30-2 ∷ []) ∷ []) Eq.refl

private
  q53 : WsL → Eqn
  q53 c4 = eqn (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4)
  q54 : WsL → Eqn
  q54 c4 = eqn (Sw12 ∷ Toff402 ∷ []) (Toff401 ∷ Sw12 ∷ []) (lem-nat-1-TOFF402 c4)
  q55 : WsL → Eqn
  q55 c4 = eqn (Sw12 ∷ Bx2-43 ∷ []) (Bx1-43 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·43⟩ c4)

-- nat 1 BOX(4;203): 8 steps
lem-nat-1-BOX⟨4·203⟩ : WsL → ⟪ (Sw12 ∷ Bx4-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-103 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·203⟩ c4 = derive (Sw12 ∷ Bx4-203 ∷ []) (Bx4-103 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) ∷
   rw 0 (q53 c4) ∷
   rw 1 (q54 c4) ∷
   rw 2 (q55 c4) ∷
   rw 3 (q54 c4) ∷
   rw 4 (q53 c4) ∷
   rw 5 (q55 c4) ∷
   re 0 6 (Bx4-103 ∷ []) ∷ []) Eq.refl

private
  q56 : WsL → Eqn
  q56 c4 = eqn (CCZ124 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ124 ∷ []) (wl0078 c4)
  q57 : WsL → Eqn
  q57 c4 = eqn (Sw12 ∷ Toff214 ∷ []) (Toff124 ∷ Sw12 ∷ []) (wl0126 c4)
  q58 : WsL → Eqn
  q58 c4 = eqn (Sw12 ∷ Bx4-203 ∷ []) (Bx4-103 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·203⟩ c4)

-- nat 1 BOX(2;4103): 8 steps
lem-nat-1-BOX⟨2·4103⟩ : WsL → ⟪ (Sw12 ∷ Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4203 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·4103⟩ c4 = derive (Sw12 ∷ Bx2-4103 ∷ []) (Bx1-4203 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff214 ∷ Bx4-203 ∷ Toff214 ∷ CCZ124 ∷ Bx4-203 ∷ []) ∷
   rw⁻ 0 (q56 c4) ∷
   rw 1 (q57 c4) ∷
   rw 2 (q58 c4) ∷
   rw 3 (q57 c4) ∷
   rw⁻ 4 (q56 c4) ∷
   rw 5 (q58 c4) ∷
   re 0 6 (Bx1-4203 ∷ []) ∷ []) Eq.refl

private
  q59 : WsL → Eqn
  q59 c4 = eqn (Sw12 ∷ Sb2-4-3-0 ∷ []) (Sb2-4-3-0 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))

-- nat 1 SBOX(2;4;3;0): 2 steps
lem-nat-1-SBOX⟨2·4·3·0⟩ : WsL → ⟪ (Sw12 ∷ Sb2-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·4·3·0⟩ c4 = derive (Sw12 ∷ Sb2-4-3-0 ∷ []) (Sb1-4-3-0 ∷ Sw12 ∷ [])
  (rw 0 (q59 c4) ∷
   re 0 1 (Sb1-4-3-0 ∷ []) ∷ []) Eq.refl

private
  q60 : WsL → Eqn
  q60 c4 = eqn (Sw12 ∷ Sb⁻2-4-3-0 ∷ []) (Sb⁻2-4-3-0 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS))

-- nat 1 SBOXd(2;4;3;0): 2 steps
lem-nat-1-SBOXd⟨2·4·3·0⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·4·3·0⟩ c4 = derive (Sw12 ∷ Sb⁻2-4-3-0 ∷ []) (Sb⁻1-4-3-0 ∷ Sw12 ∷ [])
  (rw 0 (q60 c4) ∷
   re 0 1 (Sb⁻1-4-3-0 ∷ []) ∷ []) Eq.refl

private
  q61 : WsL → Eqn
  q61 c4 = eqn (Sw12 ∷ Bx2-4103 ∷ []) (Bx1-4203 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·4103⟩ c4)
  q62 : WsL → Eqn
  q62 c4 = eqn (Sw12 ∷ Toff301 ∷ []) (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4)
  q63 : WsL → Eqn
  q63 c4 = eqn (Sw12 ∷ Sb2-4-3-0 ∷ []) (Sb1-4-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·4·3·0⟩ c4)
  q64 : WsL → Eqn
  q64 c4 = eqn (Sw12 ∷ Sb⁻2-4-3-0 ∷ []) (Sb⁻1-4-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·4·3·0⟩ c4)

-- nat 1 SBOX(2;4;10;3): 7 steps
lem-nat-1-SBOX⟨2·4·10·3⟩ : WsL → ⟪ (Sw12 ∷ Sb2-4-10-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-20-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·4·10·3⟩ c4 = derive (Sw12 ∷ Sb2-4-10-3 ∷ []) (Sb1-4-20-3 ∷ Sw12 ∷ [])
  (re 1 1 (Bx2-4103 ∷ Toff301 ∷ Sb2-4-3-0 ∷ Toff301 ∷ Sb⁻2-4-3-0 ∷ []) ∷
   rw 0 (q61 c4) ∷
   rw 1 (q62 c4) ∷
   rw 2 (q63 c4) ∷
   rw 3 (q62 c4) ∷
   rw 4 (q64 c4) ∷
   re 0 5 (Sb1-4-20-3 ∷ []) ∷ []) Eq.refl

private
  q65 : WsL → Eqn
  q65 c4 = eqn (Sw01 ∷ Sb2-4-3-1 ∷ []) (Sb2-4-3-1 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))

-- nat 0 SBOX(2;4;3;1): 2 steps
lem-nat-0-SBOX⟨2·4·3·1⟩ : WsL → ⟪ (Sw01 ∷ Sb2-4-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-3-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·4·3·1⟩ c4 = derive (Sw01 ∷ Sb2-4-3-1 ∷ []) (Sb2-4-3-0 ∷ Sw01 ∷ [])
  (rw 0 (q65 c4) ∷
   re 0 1 (Sb2-4-3-0 ∷ []) ∷ []) Eq.refl

private
  q66 : WsL → Eqn
  q66 c4 = eqn (Sw01 ∷ Sb⁻2-4-3-1 ∷ []) (Sb⁻2-4-3-1 ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑))

-- nat 0 SBOXd(2;4;3;1): 2 steps
lem-nat-0-SBOXd⟨2·4·3·1⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-4-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-3-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·4·3·1⟩ c4 = derive (Sw01 ∷ Sb⁻2-4-3-1 ∷ []) (Sb⁻2-4-3-0 ∷ Sw01 ∷ [])
  (rw 0 (q66 c4) ∷
   re 0 1 (Sb⁻2-4-3-0 ∷ []) ∷ []) Eq.refl

private
  q67 : WsL → Eqn
  q67 c4 = eqn (Sw01 ∷ Bx2-4013 ∷ []) (Bx2-4103 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·4013⟩ c4)
  q68 : WsL → Eqn
  q68 c4 = eqn (Sw01 ∷ Toff301 ∷ []) (Toff301 ∷ Sw01 ∷ []) (wl0115 c4)
  q69 : WsL → Eqn
  q69 c4 = eqn (Sw01 ∷ Sb2-4-3-1 ∷ []) (Sb2-4-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·4·3·1⟩ c4)
  q70 : WsL → Eqn
  q70 c4 = eqn (Sw01 ∷ Sb⁻2-4-3-1 ∷ []) (Sb⁻2-4-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·4·3·1⟩ c4)

-- nat 0 SBOX(2;4;01;3): 7 steps
lem-nat-0-SBOX⟨2·4·01·3⟩ : WsL → ⟪ (Sw01 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-10-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·4·01·3⟩ c4 = derive (Sw01 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-10-3 ∷ Sw01 ∷ [])
  (re 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   rw 0 (q67 c4) ∷
   rw 1 (q68 c4) ∷
   rw 2 (q69 c4) ∷
   rw 3 (q68 c4) ∷
   rw 4 (q70 c4) ∷
   re 0 5 (Sb2-4-10-3 ∷ []) ∷ []) Eq.refl

private
  q71 : WsL → Eqn
  q71 c4 = eqn (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) (wl0084 c4)
  q72 : WsL → Eqn
  q72 c4 = eqn (Sw12 ∷ Toff413 ∷ []) (Toff423 ∷ Sw12 ∷ []) (wl0085 c4)
  q73 : WsL → Eqn
  q73 c4 = eqn (Sw12 ∷ Bx3-40 ∷ []) (Bx3-40 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·40⟩ c4)

-- nat 1 BOX(4;310): 8 steps
lem-nat-1-BOX⟨4·310⟩ : WsL → ⟪ (Sw12 ∷ Bx4-310 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-320 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·310⟩ c4 = derive (Sw12 ∷ Bx4-310 ∷ []) (Bx4-320 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ []) ∷
   rw⁻ 0 (q71 c4) ∷
   rw 1 (q72 c4) ∷
   rw 2 (q73 c4) ∷
   rw 3 (q72 c4) ∷
   rw⁻ 4 (q71 c4) ∷
   rw 5 (q73 c4) ∷
   re 0 6 (Bx4-320 ∷ []) ∷ []) Eq.refl

private
  q74 : WsL → Eqn
  q74 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl0034 c4)
  q75 : WsL → Eqn
  q75 c4 = eqn (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) (wl0063 c4)
  q76 : WsL → Eqn
  q76 c4 = eqn (Sw12 ∷ Bx4-310 ∷ []) (Bx4-320 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·310⟩ c4)

-- nat 1 BOX(3;4210): 8 steps
lem-nat-1-BOX⟨3·4210⟩ : WsL → ⟪ (Sw12 ∷ Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·4210⟩ c4 = derive (Sw12 ∷ Bx3-4210 ∷ []) (Bx3-4120 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff324 ∷ Bx4-310 ∷ Toff324 ∷ CCZ234 ∷ Bx4-310 ∷ []) ∷
   rw⁻ 0 (q74 c4) ∷
   rw 1 (q75 c4) ∷
   rw 2 (q76 c4) ∷
   rw 3 (q75 c4) ∷
   rw⁻ 4 (q74 c4) ∷
   rw 5 (q76 c4) ∷
   re 0 6 (Bx3-4120 ∷ []) ∷ []) Eq.refl

private
  q77 : WsL → Eqn
  q77 c4 = eqn (Sw12 ∷ CS04 ∷ []) (CS04 ∷ Sw12 ∷ []) (lem-nat-1-CS04 c4)

-- nat 1 SBOX(3;4;0;1): 3 steps
lem-nat-1-SBOX⟨3·4·0·1⟩ : WsL → ⟪ (Sw12 ∷ Sb3-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-0-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·4·0·1⟩ c4 = derive (Sw12 ∷ Sb3-4-0-1 ∷ []) (Sb3-4-0-2 ∷ Sw12 ∷ [])
  (re 1 1 (CS04 ∷ []) ∷
   rw 0 (q77 c4) ∷
   re 0 1 (Sb3-4-0-2 ∷ []) ∷ []) Eq.refl

private
  q78 : WsL → Eqn
  q78 c4 = eqn (Sw12 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Sw12 ∷ []) (lem-nat-1-CSd04 c4)

-- nat 1 SBOXd(3;4;0;1): 3 steps
lem-nat-1-SBOXd⟨3·4·0·1⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻3-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-0-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨3·4·0·1⟩ c4 = derive (Sw12 ∷ Sb⁻3-4-0-1 ∷ []) (Sb⁻3-4-0-2 ∷ Sw12 ∷ [])
  (re 1 1 (CS04⁻ ∷ []) ∷
   rw 0 (q78 c4) ∷
   re 0 1 (Sb⁻3-4-0-2 ∷ []) ∷ []) Eq.refl

private
  q79 : WsL → Eqn
  q79 c4 = eqn (Sw12 ∷ Bx3-4210 ∷ []) (Bx3-4120 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·4210⟩ c4)
  q80 : WsL → Eqn
  q80 c4 = eqn (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) (wl0038 c4)
  q81 : WsL → Eqn
  q81 c4 = eqn (Sw12 ∷ Sb3-4-0-1 ∷ []) (Sb3-4-0-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨3·4·0·1⟩ c4)
  q82 : WsL → Eqn
  q82 c4 = eqn (Sw12 ∷ Sb⁻3-4-0-1 ∷ []) (Sb⁻3-4-0-2 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨3·4·0·1⟩ c4)

-- nat 1 SBOX(3;4;21;0): 7 steps
lem-nat-1-SBOX⟨3·4·21·0⟩ : WsL → ⟪ (Sw12 ∷ Sb3-4-21-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-12-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨3·4·21·0⟩ c4 = derive (Sw12 ∷ Sb3-4-21-0 ∷ []) (Sb3-4-12-0 ∷ Sw12 ∷ [])
  (re 1 1 (Bx3-4210 ∷ Toff012 ∷ Sb3-4-0-1 ∷ Toff012 ∷ Sb⁻3-4-0-1 ∷ []) ∷
   rw 0 (q79 c4) ∷
   rw 1 (q80 c4) ∷
   rw 2 (q81 c4) ∷
   rw 3 (q80 c4) ∷
   rw 4 (q82 c4) ∷
   re 0 5 (Sb3-4-12-0 ∷ []) ∷ []) Eq.refl

private
  q83 : WsL → Eqn
  q83 c4 = eqn (Sw23 ∷ CZ04 ∷ []) (CZ04 ∷ Sw23 ∷ []) (lem-nat-2-CZ04 c4)

-- nat 2 BOX(2;40): 3 steps
lem-nat-2-BOX⟨2·40⟩ : WsL → ⟪ (Sw23 ∷ Bx2-40 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-40 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·40⟩ c4 = derive (Sw23 ∷ Bx2-40 ∷ []) (Bx3-40 ∷ Sw23 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   rw 0 (q83 c4) ∷
   re 0 1 (Bx3-40 ∷ []) ∷ []) Eq.refl

private
  q84 : WsL → Eqn
  q84 c4 = eqn (Sw23 ∷ Toff412 ∷ []) (Toff413 ∷ Sw23 ∷ []) (lem-nat-2-TOFF412 c4)
  q85 : WsL → Eqn
  q85 c4 = eqn (Sw23 ∷ Bx2-40 ∷ []) (Bx3-40 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·40⟩ c4)

-- nat 2 BOX(4;210): 8 steps
lem-nat-2-BOX⟨4·210⟩ : WsL → ⟪ (Sw23 ∷ Bx4-210 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-310 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·210⟩ c4 = derive (Sw23 ∷ Bx4-210 ∷ []) (Bx4-310 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-40 ∷ Toff412 ∷ CCZ124 ∷ Bx2-40 ∷ []) ∷
   rw 0 (q46 c4) ∷
   rw 1 (q84 c4) ∷
   rw 2 (q85 c4) ∷
   rw 3 (q84 c4) ∷
   rw 4 (q46 c4) ∷
   rw 5 (q85 c4) ∷
   re 0 6 (Bx4-310 ∷ []) ∷ []) Eq.refl

private
  q86 : WsL → Eqn
  q86 c4 = eqn (CCZ234 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ234 ∷ []) (wl0086 c4)
  q87 : WsL → Eqn
  q87 c4 = eqn (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) (wl0127 c4)
  q88 : WsL → Eqn
  q88 c4 = eqn (Sw23 ∷ Bx4-210 ∷ []) (Bx4-310 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·210⟩ c4)

-- nat 2 BOX(2;4310): 8 steps
lem-nat-2-BOX⟨2·4310⟩ : WsL → ⟪ (Sw23 ∷ Bx2-4310 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·4310⟩ c4 = derive (Sw23 ∷ Bx2-4310 ∷ []) (Bx3-4210 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-210 ∷ Toff234 ∷ CCZ234 ∷ Bx4-210 ∷ []) ∷
   rw⁻ 0 (q86 c4) ∷
   rw 1 (q87 c4) ∷
   rw 2 (q88 c4) ∷
   rw 3 (q87 c4) ∷
   rw⁻ 4 (q86 c4) ∷
   rw 5 (q88 c4) ∷
   re 0 6 (Bx3-4210 ∷ []) ∷ []) Eq.refl

private
  q89 : WsL → Eqn
  q89 c4 = eqn (Sw23 ∷ CS04 ∷ []) (CS04 ∷ Sw23 ∷ []) (lem-nat-2-CS04 c4)

-- nat 2 SBOX(2;4;0;1): 3 steps
lem-nat-2-SBOX⟨2·4·0·1⟩ : WsL → ⟪ (Sw23 ∷ Sb2-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-0-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·4·0·1⟩ c4 = derive (Sw23 ∷ Sb2-4-0-1 ∷ []) (Sb3-4-0-1 ∷ Sw23 ∷ [])
  (re 1 1 (CS04 ∷ []) ∷
   rw 0 (q89 c4) ∷
   re 0 1 (Sb3-4-0-1 ∷ []) ∷ []) Eq.refl

private
  q90 : WsL → Eqn
  q90 c4 = eqn (Sw23 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd04 c4)

-- nat 2 SBOXd(2;4;0;1): 3 steps
lem-nat-2-SBOXd⟨2·4·0·1⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻2-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻3-4-0-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨2·4·0·1⟩ c4 = derive (Sw23 ∷ Sb⁻2-4-0-1 ∷ []) (Sb⁻3-4-0-1 ∷ Sw23 ∷ [])
  (re 1 1 (CS04⁻ ∷ []) ∷
   rw 0 (q90 c4) ∷
   re 0 1 (Sb⁻3-4-0-1 ∷ []) ∷ []) Eq.refl

private
  q91 : WsL → Eqn
  q91 c4 = eqn (Sw23 ∷ Bx2-4310 ∷ []) (Bx3-4210 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·4310⟩ c4)
  q92 : WsL → Eqn
  q92 c4 = eqn (Sw23 ∷ Toff013 ∷ []) (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4)
  q93 : WsL → Eqn
  q93 c4 = eqn (Sw23 ∷ Sb2-4-0-1 ∷ []) (Sb3-4-0-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨2·4·0·1⟩ c4)
  q94 : WsL → Eqn
  q94 c4 = eqn (Sw23 ∷ Sb⁻2-4-0-1 ∷ []) (Sb⁻3-4-0-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨2·4·0·1⟩ c4)

-- nat 2 SBOX(2;4;31;0): 7 steps
lem-nat-2-SBOX⟨2·4·31·0⟩ : WsL → ⟪ (Sw23 ∷ Sb2-4-31-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-4-21-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨2·4·31·0⟩ c4 = derive (Sw23 ∷ Sb2-4-31-0 ∷ []) (Sb3-4-21-0 ∷ Sw23 ∷ [])
  (re 1 1 (Bx2-4310 ∷ Toff013 ∷ Sb2-4-0-1 ∷ Toff013 ∷ Sb⁻2-4-0-1 ∷ []) ∷
   rw 0 (q91 c4) ∷
   rw 1 (q92 c4) ∷
   rw 2 (q93 c4) ∷
   rw 3 (q92 c4) ∷
   rw 4 (q94 c4) ∷
   re 0 5 (Sb3-4-21-0 ∷ []) ∷ []) Eq.refl

-- nat 2 BOX(3;40): 3 steps
lem-nat-2-BOX⟨3·40⟩ : WsL → ⟪ (Sw23 ∷ Bx3-40 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-40 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·40⟩ c4 = derive (Sw23 ∷ Bx3-40 ∷ []) (Bx2-40 ∷ Sw23 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   rw 0 (q83 c4) ∷
   re 0 1 (Bx2-40 ∷ []) ∷ []) Eq.refl

private
  q95 : WsL → Eqn
  q95 c4 = eqn (Sw23 ∷ CCZ134 ∷ []) (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4)
  q96 : WsL → Eqn
  q96 c4 = eqn (Sw23 ∷ Toff413 ∷ []) (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4)
  q97 : WsL → Eqn
  q97 c4 = eqn (Sw23 ∷ Bx3-40 ∷ []) (Bx2-40 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·40⟩ c4)

-- nat 2 BOX(4;310): 8 steps
lem-nat-2-BOX⟨4·310⟩ : WsL → ⟪ (Sw23 ∷ Bx4-310 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-210 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·310⟩ c4 = derive (Sw23 ∷ Bx4-310 ∷ []) (Bx4-210 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ []) ∷
   rw 0 (q95 c4) ∷
   rw 1 (q96 c4) ∷
   rw 2 (q97 c4) ∷
   rw 3 (q96 c4) ∷
   rw 4 (q95 c4) ∷
   rw 5 (q97 c4) ∷
   re 0 6 (Bx4-210 ∷ []) ∷ []) Eq.refl

private
  q98 : WsL → Eqn
  q98 c4 = eqn (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) (wl0144 c4)
  q99 : WsL → Eqn
  q99 c4 = eqn (Sw23 ∷ Bx4-310 ∷ []) (Bx4-210 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·310⟩ c4)

-- nat 2 BOX(3;4210): 8 steps
lem-nat-2-BOX⟨3·4210⟩ : WsL → ⟪ (Sw23 ∷ Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4310 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·4210⟩ c4 = derive (Sw23 ∷ Bx3-4210 ∷ []) (Bx2-4310 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff324 ∷ Bx4-310 ∷ Toff324 ∷ CCZ234 ∷ Bx4-310 ∷ []) ∷
   rw⁻ 0 (q86 c4) ∷
   rw 1 (q98 c4) ∷
   rw 2 (q99 c4) ∷
   rw 3 (q98 c4) ∷
   rw⁻ 4 (q86 c4) ∷
   rw 5 (q99 c4) ∷
   re 0 6 (Bx2-4310 ∷ []) ∷ []) Eq.refl

-- nat 2 SBOX(3;4;0;1): 3 steps
lem-nat-2-SBOX⟨3·4·0·1⟩ : WsL → ⟪ (Sw23 ∷ Sb3-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-0-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·4·0·1⟩ c4 = derive (Sw23 ∷ Sb3-4-0-1 ∷ []) (Sb2-4-0-1 ∷ Sw23 ∷ [])
  (re 1 1 (CS04 ∷ []) ∷
   rw 0 (q89 c4) ∷
   re 0 1 (Sb2-4-0-1 ∷ []) ∷ []) Eq.refl

-- nat 2 SBOXd(3;4;0;1): 3 steps
lem-nat-2-SBOXd⟨3·4·0·1⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻3-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-0-1 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨3·4·0·1⟩ c4 = derive (Sw23 ∷ Sb⁻3-4-0-1 ∷ []) (Sb⁻2-4-0-1 ∷ Sw23 ∷ [])
  (re 1 1 (CS04⁻ ∷ []) ∷
   rw 0 (q90 c4) ∷
   re 0 1 (Sb⁻2-4-0-1 ∷ []) ∷ []) Eq.refl

private
  q100 : WsL → Eqn
  q100 c4 = eqn (Sw23 ∷ Bx3-4210 ∷ []) (Bx2-4310 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·4210⟩ c4)
  q101 : WsL → Eqn
  q101 c4 = eqn (Sw23 ∷ Toff012 ∷ []) (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4)
  q102 : WsL → Eqn
  q102 c4 = eqn (Sw23 ∷ Sb3-4-0-1 ∷ []) (Sb2-4-0-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨3·4·0·1⟩ c4)
  q103 : WsL → Eqn
  q103 c4 = eqn (Sw23 ∷ Sb⁻3-4-0-1 ∷ []) (Sb⁻2-4-0-1 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨3·4·0·1⟩ c4)

-- nat 2 SBOX(3;4;21;0): 7 steps
lem-nat-2-SBOX⟨3·4·21·0⟩ : WsL → ⟪ (Sw23 ∷ Sb3-4-21-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-31-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨3·4·21·0⟩ c4 = derive (Sw23 ∷ Sb3-4-21-0 ∷ []) (Sb2-4-31-0 ∷ Sw23 ∷ [])
  (re 1 1 (Bx3-4210 ∷ Toff012 ∷ Sb3-4-0-1 ∷ Toff012 ∷ Sb⁻3-4-0-1 ∷ []) ∷
   rw 0 (q100 c4) ∷
   rw 1 (q101 c4) ∷
   rw 2 (q102 c4) ∷
   rw 3 (q101 c4) ∷
   rw 4 (q103 c4) ∷
   re 0 5 (Sb2-4-31-0 ∷ []) ∷ []) Eq.refl

-- nat 3 TOFF312: 2 steps
lem-nat-3-TOFF312 : WsL → ⟪ (Sw34 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF312 c4 = derive (Sw34 ∷ Toff312 ∷ []) (Toff412 ∷ Sw34 ∷ [])
  (rw⁻ 2 (q7 c4) ∷
   re 0 3 (Toff412 ∷ []) ∷ []) Eq.refl

private
  q104 : WsL → Eqn
  q104 c4 = eqn (Sw34 ∷ CZ03 ∷ []) (CZ04 ∷ Sw34 ∷ []) (lem-nat-3-CZ03 c4)

-- nat 3 BOX(2;30): 3 steps
lem-nat-3-BOX⟨2·30⟩ : WsL → ⟪ (Sw34 ∷ Bx2-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-40 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·30⟩ c4 = derive (Sw34 ∷ Bx2-30 ∷ []) (Bx2-40 ∷ Sw34 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw 0 (q104 c4) ∷
   re 0 1 (Bx2-40 ∷ []) ∷ []) Eq.refl

private
  q105 : WsL → Eqn
  q105 c4 = eqn (Sw34 ∷ CCZ123 ∷ []) (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4)
  q106 : WsL → Eqn
  q106 c4 = eqn (Sw34 ∷ Toff312 ∷ []) (Toff412 ∷ Sw34 ∷ []) (lem-nat-3-TOFF312 c4)
  q107 : WsL → Eqn
  q107 c4 = eqn (Sw34 ∷ Bx2-30 ∷ []) (Bx2-40 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·30⟩ c4)

-- nat 3 BOX(3;210): 8 steps
lem-nat-3-BOX⟨3·210⟩ : WsL → ⟪ (Sw34 ∷ Bx3-210 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-210 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·210⟩ c4 = derive (Sw34 ∷ Bx3-210 ∷ []) (Bx4-210 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) ∷
   rw 0 (q105 c4) ∷
   rw 1 (q106 c4) ∷
   rw 2 (q107 c4) ∷
   rw 3 (q106 c4) ∷
   rw 4 (q105 c4) ∷
   rw 5 (q107 c4) ∷
   re 0 6 (Bx4-210 ∷ []) ∷ []) Eq.refl

private
  q108 : WsL → Eqn
  q108 c4 = eqn (CCZ234 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ234 ∷ []) (wl0155 c4)
  q109 : WsL → Eqn
  q109 c4 = eqn (Sw34 ∷ Toff234 ∷ []) (Toff234 ∷ Sw34 ∷ []) (wl0128 c4)
  q110 : WsL → Eqn
  q110 c4 = eqn (Sw34 ∷ Bx3-210 ∷ []) (Bx4-210 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·210⟩ c4)

-- nat 3 BOX(2;3410): 8 steps
lem-nat-3-BOX⟨2·3410⟩ : WsL → ⟪ (Sw34 ∷ Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4310 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·3410⟩ c4 = derive (Sw34 ∷ Bx2-3410 ∷ []) (Bx2-4310 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-210 ∷ Toff234 ∷ CCZ234 ∷ Bx3-210 ∷ []) ∷
   rw⁻ 0 (q108 c4) ∷
   rw 1 (q109 c4) ∷
   rw 2 (q110 c4) ∷
   rw 3 (q109 c4) ∷
   rw⁻ 4 (q108 c4) ∷
   rw 5 (q110 c4) ∷
   re 0 6 (Bx2-4310 ∷ []) ∷ []) Eq.refl

private
  q111 : WsL → Eqn
  q111 c4 = eqn (Sw34 ∷ CS03 ∷ []) (CS04 ∷ Sw34 ∷ []) (lem-nat-3-CS03 c4)

-- nat 3 SBOX(2;3;0;1): 3 steps
lem-nat-3-SBOX⟨2·3·0·1⟩ : WsL → ⟪ (Sw34 ∷ Sb2-3-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-0-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·3·0·1⟩ c4 = derive (Sw34 ∷ Sb2-3-0-1 ∷ []) (Sb2-4-0-1 ∷ Sw34 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   rw 0 (q111 c4) ∷
   re 0 1 (Sb2-4-0-1 ∷ []) ∷ []) Eq.refl

private
  q112 : WsL → Eqn
  q112 c4 = eqn (Sw34 ∷ CS03⁻ ∷ []) (CS04⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd03 c4)

-- nat 3 SBOXd(2;3;0;1): 3 steps
lem-nat-3-SBOXd⟨2·3·0·1⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻2-3-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-0-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·3·0·1⟩ c4 = derive (Sw34 ∷ Sb⁻2-3-0-1 ∷ []) (Sb⁻2-4-0-1 ∷ Sw34 ∷ [])
  (re 1 1 (CS03⁻ ∷ []) ∷
   rw 0 (q112 c4) ∷
   re 0 1 (Sb⁻2-4-0-1 ∷ []) ∷ []) Eq.refl

private
  q113 : WsL → Eqn
  q113 c4 = eqn (Sw34 ∷ Bx2-3410 ∷ []) (Bx2-4310 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·3410⟩ c4)
  q114 : WsL → Eqn
  q114 c4 = eqn (Sw34 ∷ Toff014 ∷ []) (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4)
  q115 : WsL → Eqn
  q115 c4 = eqn (Sw34 ∷ Sb2-3-0-1 ∷ []) (Sb2-4-0-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·3·0·1⟩ c4)
  q116 : WsL → Eqn
  q116 c4 = eqn (Sw34 ∷ Sb⁻2-3-0-1 ∷ []) (Sb⁻2-4-0-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·3·0·1⟩ c4)

-- nat 3 SBOX(2;3;41;0): 7 steps
lem-nat-3-SBOX⟨2·3·41·0⟩ : WsL → ⟪ (Sw34 ∷ Sb2-3-41-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-31-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·3·41·0⟩ c4 = derive (Sw34 ∷ Sb2-3-41-0 ∷ []) (Sb2-4-31-0 ∷ Sw34 ∷ [])
  (re 1 1 (Bx2-3410 ∷ Toff014 ∷ Sb2-3-0-1 ∷ Toff014 ∷ Sb⁻2-3-0-1 ∷ []) ∷
   rw 0 (q113 c4) ∷
   rw 1 (q114 c4) ∷
   rw 2 (q115 c4) ∷
   rw 3 (q114 c4) ∷
   rw 4 (q116 c4) ∷
   re 0 5 (Sb2-4-31-0 ∷ []) ∷ []) Eq.refl

private
  q117 : WsL → Eqn
  q117 c4 = eqn (Sw34 ∷ CZ04 ∷ []) (CZ03 ∷ Sw34 ∷ []) (lem-nat-3-CZ04 c4)

-- nat 3 BOX(2;40): 3 steps
lem-nat-3-BOX⟨2·40⟩ : WsL → ⟪ (Sw34 ∷ Bx2-40 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-30 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·40⟩ c4 = derive (Sw34 ∷ Bx2-40 ∷ []) (Bx2-30 ∷ Sw34 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   rw 0 (q117 c4) ∷
   re 0 1 (Bx2-30 ∷ []) ∷ []) Eq.refl

private
  q118 : WsL → Eqn
  q118 c4 = eqn (Sw34 ∷ CCZ124 ∷ []) (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4)
  q119 : WsL → Eqn
  q119 c4 = eqn (Sw34 ∷ Toff412 ∷ []) (Toff312 ∷ Sw34 ∷ []) (lem-nat-3-TOFF412 c4)
  q120 : WsL → Eqn
  q120 c4 = eqn (Sw34 ∷ Bx2-40 ∷ []) (Bx2-30 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·40⟩ c4)

-- nat 3 BOX(4;210): 8 steps
lem-nat-3-BOX⟨4·210⟩ : WsL → ⟪ (Sw34 ∷ Bx4-210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-210 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨4·210⟩ c4 = derive (Sw34 ∷ Bx4-210 ∷ []) (Bx3-210 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-40 ∷ Toff412 ∷ CCZ124 ∷ Bx2-40 ∷ []) ∷
   rw 0 (q118 c4) ∷
   rw 1 (q119 c4) ∷
   rw 2 (q120 c4) ∷
   rw 3 (q119 c4) ∷
   rw 4 (q118 c4) ∷
   rw 5 (q120 c4) ∷
   re 0 6 (Bx3-210 ∷ []) ∷ []) Eq.refl

private
  q121 : WsL → Eqn
  q121 c4 = eqn (Sw34 ∷ Bx4-210 ∷ []) (Bx3-210 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·210⟩ c4)

-- nat 3 BOX(2;4310): 8 steps
lem-nat-3-BOX⟨2·4310⟩ : WsL → ⟪ (Sw34 ∷ Bx2-4310 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·4310⟩ c4 = derive (Sw34 ∷ Bx2-4310 ∷ []) (Bx2-3410 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-210 ∷ Toff234 ∷ CCZ234 ∷ Bx4-210 ∷ []) ∷
   rw⁻ 0 (q108 c4) ∷
   rw 1 (q109 c4) ∷
   rw 2 (q121 c4) ∷
   rw 3 (q109 c4) ∷
   rw⁻ 4 (q108 c4) ∷
   rw 5 (q121 c4) ∷
   re 0 6 (Bx2-3410 ∷ []) ∷ []) Eq.refl

private
  q122 : WsL → Eqn
  q122 c4 = eqn (Sw34 ∷ CS04 ∷ []) (CS03 ∷ Sw34 ∷ []) (lem-nat-3-CS04 c4)

-- nat 3 SBOX(2;4;0;1): 3 steps
lem-nat-3-SBOX⟨2·4·0·1⟩ : WsL → ⟪ (Sw34 ∷ Sb2-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-0-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·4·0·1⟩ c4 = derive (Sw34 ∷ Sb2-4-0-1 ∷ []) (Sb2-3-0-1 ∷ Sw34 ∷ [])
  (re 1 1 (CS04 ∷ []) ∷
   rw 0 (q122 c4) ∷
   re 0 1 (Sb2-3-0-1 ∷ []) ∷ []) Eq.refl

private
  q123 : WsL → Eqn
  q123 c4 = eqn (Sw34 ∷ CS04⁻ ∷ []) (CS03⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd04 c4)

-- nat 3 SBOXd(2;4;0;1): 3 steps
lem-nat-3-SBOXd⟨2·4·0·1⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻2-4-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-0-1 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨2·4·0·1⟩ c4 = derive (Sw34 ∷ Sb⁻2-4-0-1 ∷ []) (Sb⁻2-3-0-1 ∷ Sw34 ∷ [])
  (re 1 1 (CS04⁻ ∷ []) ∷
   rw 0 (q123 c4) ∷
   re 0 1 (Sb⁻2-3-0-1 ∷ []) ∷ []) Eq.refl

private
  q124 : WsL → Eqn
  q124 c4 = eqn (Sw34 ∷ Bx2-4310 ∷ []) (Bx2-3410 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·4310⟩ c4)
  q125 : WsL → Eqn
  q125 c4 = eqn (Sw34 ∷ Toff013 ∷ []) (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4)
  q126 : WsL → Eqn
  q126 c4 = eqn (Sw34 ∷ Sb2-4-0-1 ∷ []) (Sb2-3-0-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·4·0·1⟩ c4)
  q127 : WsL → Eqn
  q127 c4 = eqn (Sw34 ∷ Sb⁻2-4-0-1 ∷ []) (Sb⁻2-3-0-1 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨2·4·0·1⟩ c4)

-- nat 3 SBOX(2;4;31;0): 7 steps
lem-nat-3-SBOX⟨2·4·31·0⟩ : WsL → ⟪ (Sw34 ∷ Sb2-4-31-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-41-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨2·4·31·0⟩ c4 = derive (Sw34 ∷ Sb2-4-31-0 ∷ []) (Sb2-3-41-0 ∷ Sw34 ∷ [])
  (re 1 1 (Bx2-4310 ∷ Toff013 ∷ Sb2-4-0-1 ∷ Toff013 ∷ Sb⁻2-4-0-1 ∷ []) ∷
   rw 0 (q124 c4) ∷
   rw 1 (q125 c4) ∷
   rw 2 (q126 c4) ∷
   rw 3 (q125 c4) ∷
   rw 4 (q127 c4) ∷
   re 0 5 (Sb2-3-41-0 ∷ []) ∷ []) Eq.refl

-- nat 0 SBOX(2;3;1;0): 3 steps
lem-nat-0-SBOX⟨2·3·1·0⟩ : WsL → ⟪ (Sw01 ∷ Sb2-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-0-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·3·1·0⟩ c4 = derive (Sw01 ∷ Sb2-3-1-0 ∷ []) (Sb2-3-0-1 ∷ Sw01 ∷ [])
  (re 1 1 (CS13 ∷ []) ∷
   rw⁻ 0 (q31 c4) ∷
   re 0 1 (Sb2-3-0-1 ∷ []) ∷ []) Eq.refl

private
  q128 : WsL → Eqn
  q128 c4 = eqn (CS03⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS13⁻ ∷ []) (wl0022 c4)

-- nat 0 SBOXd(2;3;1;0): 3 steps
lem-nat-0-SBOXd⟨2·3·1·0⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-0-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·3·1·0⟩ c4 = derive (Sw01 ∷ Sb⁻2-3-1-0 ∷ []) (Sb⁻2-3-0-1 ∷ Sw01 ∷ [])
  (re 1 1 (CS13⁻ ∷ []) ∷
   rw⁻ 0 (q128 c4) ∷
   re 0 1 (Sb⁻2-3-0-1 ∷ []) ∷ []) Eq.refl

private
  q129 : WsL → Eqn
  q129 c4 = eqn (Sw01 ∷ Bx2-3401 ∷ []) (Bx2-3410 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3401⟩ c4)
  q130 : WsL → Eqn
  q130 c4 = eqn (Sw01 ∷ Toff104 ∷ []) (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4)
  q131 : WsL → Eqn
  q131 c4 = eqn (Sw01 ∷ Sb2-3-1-0 ∷ []) (Sb2-3-0-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·1·0⟩ c4)
  q132 : WsL → Eqn
  q132 c4 = eqn (Sw01 ∷ Sb⁻2-3-1-0 ∷ []) (Sb⁻2-3-0-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·3·1·0⟩ c4)

-- nat 0 SBOX(2;3;40;1): 7 steps
lem-nat-0-SBOX⟨2·3·40·1⟩ : WsL → ⟪ (Sw01 ∷ Sb2-3-40-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-41-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·3·40·1⟩ c4 = derive (Sw01 ∷ Sb2-3-40-1 ∷ []) (Sb2-3-41-0 ∷ Sw01 ∷ [])
  (re 1 1 (Bx2-3401 ∷ Toff104 ∷ Sb2-3-1-0 ∷ Toff104 ∷ Sb⁻2-3-1-0 ∷ []) ∷
   rw 0 (q129 c4) ∷
   rw 1 (q130 c4) ∷
   rw 2 (q131 c4) ∷
   rw 3 (q130 c4) ∷
   rw 4 (q132 c4) ∷
   re 0 5 (Sb2-3-41-0 ∷ []) ∷ []) Eq.refl

private
  q133 : WsL → Eqn
  q133 c4 = eqn (CS13 ∷ Sw01 ∷ []) (Sw01 ∷ CS03 ∷ []) (wl0061 c4)

-- nat 0 SBOX(2;3;0;1): 3 steps
lem-nat-0-SBOX⟨2·3·0·1⟩ : WsL → ⟪ (Sw01 ∷ Sb2-3-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-1-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·3·0·1⟩ c4 = derive (Sw01 ∷ Sb2-3-0-1 ∷ []) (Sb2-3-1-0 ∷ Sw01 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   rw⁻ 0 (q133 c4) ∷
   re 0 1 (Sb2-3-1-0 ∷ []) ∷ []) Eq.refl

private
  q134 : WsL → Eqn
  q134 c4 = eqn (CS13⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS03⁻ ∷ []) (wl0121 c4)

-- nat 0 SBOXd(2;3;0;1): 3 steps
lem-nat-0-SBOXd⟨2·3·0·1⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-3-0-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-1-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·3·0·1⟩ c4 = derive (Sw01 ∷ Sb⁻2-3-0-1 ∷ []) (Sb⁻2-3-1-0 ∷ Sw01 ∷ [])
  (re 1 1 (CS03⁻ ∷ []) ∷
   rw⁻ 0 (q134 c4) ∷
   re 0 1 (Sb⁻2-3-1-0 ∷ []) ∷ []) Eq.refl

private
  q135 : WsL → Eqn
  q135 c4 = eqn (Sw01 ∷ Bx2-3410 ∷ []) (Bx2-3401 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3410⟩ c4)
  q136 : WsL → Eqn
  q136 c4 = eqn (Sw01 ∷ Toff014 ∷ []) (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4)
  q137 : WsL → Eqn
  q137 c4 = eqn (Sw01 ∷ Sb2-3-0-1 ∷ []) (Sb2-3-1-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·0·1⟩ c4)
  q138 : WsL → Eqn
  q138 c4 = eqn (Sw01 ∷ Sb⁻2-3-0-1 ∷ []) (Sb⁻2-3-1-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·3·0·1⟩ c4)

-- nat 0 SBOX(2;3;41;0): 7 steps
lem-nat-0-SBOX⟨2·3·41·0⟩ : WsL → ⟪ (Sw01 ∷ Sb2-3-41-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-40-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·3·41·0⟩ c4 = derive (Sw01 ∷ Sb2-3-41-0 ∷ []) (Sb2-3-40-1 ∷ Sw01 ∷ [])
  (re 1 1 (Bx2-3410 ∷ Toff014 ∷ Sb2-3-0-1 ∷ Toff014 ∷ Sb⁻2-3-0-1 ∷ []) ∷
   rw 0 (q135 c4) ∷
   rw 1 (q136 c4) ∷
   rw 2 (q137 c4) ∷
   rw 3 (q136 c4) ∷
   rw 4 (q138 c4) ∷
   re 0 5 (Sb2-3-40-1 ∷ []) ∷ []) Eq.refl

private
  q139 : WsL → Eqn
  q139 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl0024 c4)

-- nat 1 SBOX(1;3;2;0): 3 steps
lem-nat-1-SBOX⟨1·3·2·0⟩ : WsL → ⟪ (Sw12 ∷ Sb1-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-1-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·3·2·0⟩ c4 = derive (Sw12 ∷ Sb1-3-2-0 ∷ []) (Sb2-3-1-0 ∷ Sw12 ∷ [])
  (re 1 1 (CS23 ∷ []) ∷
   rw⁻ 0 (q139 c4) ∷
   re 0 1 (Sb2-3-1-0 ∷ []) ∷ []) Eq.refl

private
  q140 : WsL → Eqn
  q140 c4 = eqn (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) (wl0043 c4)

-- nat 1 SBOXd(1;3;2;0): 3 steps
lem-nat-1-SBOXd⟨1·3·2·0⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-1-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·3·2·0⟩ c4 = derive (Sw12 ∷ Sb⁻1-3-2-0 ∷ []) (Sb⁻2-3-1-0 ∷ Sw12 ∷ [])
  (re 1 1 (CS23⁻ ∷ []) ∷
   rw⁻ 0 (q140 c4) ∷
   re 0 1 (Sb⁻2-3-1-0 ∷ []) ∷ []) Eq.refl

private
  q141 : WsL → Eqn
  q141 c4 = eqn (Sw12 ∷ Bx1-3402 ∷ []) (Bx2-3401 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3402⟩ c4)
  q142 : WsL → Eqn
  q142 c4 = eqn (Sw12 ∷ Toff204 ∷ []) (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4)
  q143 : WsL → Eqn
  q143 c4 = eqn (Sw12 ∷ Sb1-3-2-0 ∷ []) (Sb2-3-1-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·3·2·0⟩ c4)
  q144 : WsL → Eqn
  q144 c4 = eqn (Sw12 ∷ Sb⁻1-3-2-0 ∷ []) (Sb⁻2-3-1-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·3·2·0⟩ c4)

-- nat 1 SBOX(1;3;40;2): 7 steps
lem-nat-1-SBOX⟨1·3·40·2⟩ : WsL → ⟪ (Sw12 ∷ Sb1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-40-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·3·40·2⟩ c4 = derive (Sw12 ∷ Sb1-3-40-2 ∷ []) (Sb2-3-40-1 ∷ Sw12 ∷ [])
  (re 1 1 (Bx1-3402 ∷ Toff204 ∷ Sb1-3-2-0 ∷ Toff204 ∷ Sb⁻1-3-2-0 ∷ []) ∷
   rw 0 (q141 c4) ∷
   rw 1 (q142 c4) ∷
   rw 2 (q143 c4) ∷
   rw 3 (q142 c4) ∷
   rw 4 (q144 c4) ∷
   re 0 5 (Sb2-3-40-1 ∷ []) ∷ []) Eq.refl

private
  q145 : WsL → Eqn
  q145 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl0025 c4)

-- nat 1 SBOX(2;3;1;0): 3 steps
lem-nat-1-SBOX⟨2·3·1·0⟩ : WsL → ⟪ (Sw12 ∷ Sb2-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·3·1·0⟩ c4 = derive (Sw12 ∷ Sb2-3-1-0 ∷ []) (Sb1-3-2-0 ∷ Sw12 ∷ [])
  (re 1 1 (CS13 ∷ []) ∷
   rw⁻ 0 (q145 c4) ∷
   re 0 1 (Sb1-3-2-0 ∷ []) ∷ []) Eq.refl

private
  q146 : WsL → Eqn
  q146 c4 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wl0046 c4)

-- nat 1 SBOXd(2;3;1;0): 3 steps
lem-nat-1-SBOXd⟨2·3·1·0⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-3-1-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-2-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·3·1·0⟩ c4 = derive (Sw12 ∷ Sb⁻2-3-1-0 ∷ []) (Sb⁻1-3-2-0 ∷ Sw12 ∷ [])
  (re 1 1 (CS13⁻ ∷ []) ∷
   rw⁻ 0 (q146 c4) ∷
   re 0 1 (Sb⁻1-3-2-0 ∷ []) ∷ []) Eq.refl

private
  q147 : WsL → Eqn
  q147 c4 = eqn (Sw12 ∷ Bx2-3401 ∷ []) (Bx1-3402 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·3401⟩ c4)
  q148 : WsL → Eqn
  q148 c4 = eqn (Sw12 ∷ Toff104 ∷ []) (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4)
  q149 : WsL → Eqn
  q149 c4 = eqn (Sw12 ∷ Sb2-3-1-0 ∷ []) (Sb1-3-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·3·1·0⟩ c4)
  q150 : WsL → Eqn
  q150 c4 = eqn (Sw12 ∷ Sb⁻2-3-1-0 ∷ []) (Sb⁻1-3-2-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·3·1·0⟩ c4)

-- nat 1 SBOX(2;3;40;1): 7 steps
lem-nat-1-SBOX⟨2·3·40·1⟩ : WsL → ⟪ (Sw12 ∷ Sb2-3-40-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-40-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·3·40·1⟩ c4 = derive (Sw12 ∷ Sb2-3-40-1 ∷ []) (Sb1-3-40-2 ∷ Sw12 ∷ [])
  (re 1 1 (Bx2-3401 ∷ Toff104 ∷ Sb2-3-1-0 ∷ Toff104 ∷ Sb⁻2-3-1-0 ∷ []) ∷
   rw 0 (q147 c4) ∷
   rw 1 (q148 c4) ∷
   rw 2 (q149 c4) ∷
   rw 3 (q148 c4) ∷
   rw 4 (q150 c4) ∷
   re 0 5 (Sb1-3-40-2 ∷ []) ∷ []) Eq.refl

private
  q151 : WsL → Eqn
  q151 c4 = eqn (CZ23 ∷ Sw23 ∷ []) (Sw23 ∷ CZ23 ∷ []) (wl0045 c4)

-- nat 2 BOX(1;23): 3 steps
lem-nat-2-BOX⟨1·23⟩ : WsL → ⟪ (Sw23 ∷ Bx1-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-32 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·23⟩ c4 = derive (Sw23 ∷ Bx1-23 ∷ []) (Bx1-32 ∷ Sw23 ∷ [])
  (re 1 1 (CZ23 ∷ []) ∷
   rw⁻ 0 (q151 c4) ∷
   re 0 1 (Bx1-32 ∷ []) ∷ []) Eq.refl

private
  q152 : WsL → Eqn
  q152 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4)
  q153 : WsL → Eqn
  q153 c4 = eqn (Sw23 ∷ Toff201 ∷ []) (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4)
  q154 : WsL → Eqn
  q154 c4 = eqn (Sw23 ∷ Bx1-23 ∷ []) (Bx1-32 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·23⟩ c4)

-- nat 2 BOX(2;103): 8 steps
lem-nat-2-BOX⟨2·103⟩ : WsL → ⟪ (Sw23 ∷ Bx2-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-102 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·103⟩ c4 = derive (Sw23 ∷ Bx2-103 ∷ []) (Bx3-102 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-23 ∷ Toff201 ∷ CCZ012 ∷ Bx1-23 ∷ []) ∷
   rw 0 (q152 c4) ∷
   rw 1 (q153 c4) ∷
   rw 2 (q154 c4) ∷
   rw 3 (q153 c4) ∷
   rw 4 (q152 c4) ∷
   rw 5 (q154 c4) ∷
   re 0 6 (Bx3-102 ∷ []) ∷ []) Eq.refl

private
  q155 : WsL → Eqn
  q155 c4 = eqn (Sw23 ∷ Bx2-103 ∷ []) (Bx3-102 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·103⟩ c4)

-- nat 2 BOX(1;2403): 8 steps
lem-nat-2-BOX⟨1·2403⟩ : WsL → ⟪ (Sw23 ∷ Bx1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3402 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·2403⟩ c4 = derive (Sw23 ∷ Bx1-2403 ∷ []) (Bx1-3402 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-103 ∷ Toff124 ∷ CCZ124 ∷ Bx2-103 ∷ []) ∷
   rw 0 (q46 c4) ∷
   rw 1 (q47 c4) ∷
   rw 2 (q155 c4) ∷
   rw 3 (q47 c4) ∷
   rw 4 (q46 c4) ∷
   rw 5 (q155 c4) ∷
   re 0 6 (Bx1-3402 ∷ []) ∷ []) Eq.refl

private
  q156 : WsL → Eqn
  q156 c4 = eqn (CS23 ∷ Sw23 ∷ []) (Sw23 ∷ CS23 ∷ []) (wl0152 c4)

-- nat 2 SBOX(1;2;3;0): 3 steps
lem-nat-2-SBOX⟨1·2·3·0⟩ : WsL → ⟪ (Sw23 ∷ Sb1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-2-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·2·3·0⟩ c4 = derive (Sw23 ∷ Sb1-2-3-0 ∷ []) (Sb1-3-2-0 ∷ Sw23 ∷ [])
  (re 1 1 (CS23 ∷ []) ∷
   rw⁻ 0 (q156 c4) ∷
   re 0 1 (Sb1-3-2-0 ∷ []) ∷ []) Eq.refl

private
  q157 : WsL → Eqn
  q157 c4 = eqn (CS23⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS23⁻ ∷ []) (wl0153 c4)

-- nat 2 SBOXd(1;2;3;0): 3 steps
lem-nat-2-SBOXd⟨1·2·3·0⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-2-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-2-0 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·2·3·0⟩ c4 = derive (Sw23 ∷ Sb⁻1-2-3-0 ∷ []) (Sb⁻1-3-2-0 ∷ Sw23 ∷ [])
  (re 1 1 (CS23⁻ ∷ []) ∷
   rw⁻ 0 (q157 c4) ∷
   re 0 1 (Sb⁻1-3-2-0 ∷ []) ∷ []) Eq.refl

private
  q158 : WsL → Eqn
  q158 c4 = eqn (Sw23 ∷ Bx1-2403 ∷ []) (Bx1-3402 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·2403⟩ c4)
  q159 : WsL → Eqn
  q159 c4 = eqn (Sw23 ∷ Toff304 ∷ []) (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4)
  q160 : WsL → Eqn
  q160 c4 = eqn (Sw23 ∷ Sb1-2-3-0 ∷ []) (Sb1-3-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·2·3·0⟩ c4)
  q161 : WsL → Eqn
  q161 c4 = eqn (Sw23 ∷ Sb⁻1-2-3-0 ∷ []) (Sb⁻1-3-2-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·2·3·0⟩ c4)

-- nat 2 SBOX(1;2;40;3): 7 steps
lem-nat-2-SBOX⟨1·2·40·3⟩ : WsL → ⟪ (Sw23 ∷ Sb1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-40-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·2·40·3⟩ c4 = derive (Sw23 ∷ Sb1-2-40-3 ∷ []) (Sb1-3-40-2 ∷ Sw23 ∷ [])
  (re 1 1 (Bx1-2403 ∷ Toff304 ∷ Sb1-2-3-0 ∷ Toff304 ∷ Sb⁻1-2-3-0 ∷ []) ∷
   rw 0 (q158 c4) ∷
   rw 1 (q159 c4) ∷
   rw 2 (q160 c4) ∷
   rw 3 (q159 c4) ∷
   rw 4 (q161 c4) ∷
   re 0 5 (Sb1-3-40-2 ∷ []) ∷ []) Eq.refl

-- nat 1 SBOX(2;1;3;0): 3 steps
lem-nat-1-SBOX⟨2·1·3·0⟩ : WsL → ⟪ (Sw12 ∷ Sb2-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·1·3·0⟩ c4 = derive (Sw12 ∷ Sb2-1-3-0 ∷ []) (Sb1-2-3-0 ∷ Sw12 ∷ [])
  (re 1 1 (CS13 ∷ []) ∷
   rw⁻ 0 (q145 c4) ∷
   re 0 1 (Sb1-2-3-0 ∷ []) ∷ []) Eq.refl

-- nat 1 SBOXd(2;1;3;0): 3 steps
lem-nat-1-SBOXd⟨2·1·3·0⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-1-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·1·3·0⟩ c4 = derive (Sw12 ∷ Sb⁻2-1-3-0 ∷ []) (Sb⁻1-2-3-0 ∷ Sw12 ∷ [])
  (re 1 1 (CS13⁻ ∷ []) ∷
   rw⁻ 0 (q146 c4) ∷
   re 0 1 (Sb⁻1-2-3-0 ∷ []) ∷ []) Eq.refl

private
  q162 : WsL → Eqn
  q162 c4 = eqn (Sw12 ∷ Bx2-1403 ∷ []) (Bx1-2403 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·1403⟩ c4)
  q163 : WsL → Eqn
  q163 c4 = eqn (Sw12 ∷ Toff304 ∷ []) (Toff304 ∷ Sw12 ∷ []) (lem-nat-1-TOFF304 c4)
  q164 : WsL → Eqn
  q164 c4 = eqn (Sw12 ∷ Sb2-1-3-0 ∷ []) (Sb1-2-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·1·3·0⟩ c4)
  q165 : WsL → Eqn
  q165 c4 = eqn (Sw12 ∷ Sb⁻2-1-3-0 ∷ []) (Sb⁻1-2-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·1·3·0⟩ c4)

-- nat 1 SBOX(2;1;40;3): 7 steps
lem-nat-1-SBOX⟨2·1·40·3⟩ : WsL → ⟪ (Sw12 ∷ Sb2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-40-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·1·40·3⟩ c4 = derive (Sw12 ∷ Sb2-1-40-3 ∷ []) (Sb1-2-40-3 ∷ Sw12 ∷ [])
  (re 1 1 (Bx2-1403 ∷ Toff304 ∷ Sb2-1-3-0 ∷ Toff304 ∷ Sb⁻2-1-3-0 ∷ []) ∷
   rw 0 (q162 c4) ∷
   rw 1 (q163 c4) ∷
   rw 2 (q164 c4) ∷
   rw 3 (q163 c4) ∷
   rw 4 (q165 c4) ∷
   re 0 5 (Sb1-2-40-3 ∷ []) ∷ []) Eq.refl

-- nat 0 SBOX(2;0;3;1): 3 steps
lem-nat-0-SBOX⟨2·0·3·1⟩ : WsL → ⟪ (Sw01 ∷ Sb2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-3-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·0·3·1⟩ c4 = derive (Sw01 ∷ Sb2-0-3-1 ∷ []) (Sb2-1-3-0 ∷ Sw01 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   rw⁻ 0 (q133 c4) ∷
   re 0 1 (Sb2-1-3-0 ∷ []) ∷ []) Eq.refl

-- nat 0 SBOXd(2;0;3;1): 3 steps
lem-nat-0-SBOXd⟨2·0·3·1⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-0-3-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-3-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·0·3·1⟩ c4 = derive (Sw01 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻2-1-3-0 ∷ Sw01 ∷ [])
  (re 1 1 (CS03⁻ ∷ []) ∷
   rw⁻ 0 (q134 c4) ∷
   re 0 1 (Sb⁻2-1-3-0 ∷ []) ∷ []) Eq.refl

private
  q166 : WsL → Eqn
  q166 c4 = eqn (Sw01 ∷ Bx2-0413 ∷ []) (Bx2-1403 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·0413⟩ c4)
  q167 : WsL → Eqn
  q167 c4 = eqn (Sw01 ∷ Toff314 ∷ []) (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4)
  q168 : WsL → Eqn
  q168 c4 = eqn (Sw01 ∷ Sb2-0-3-1 ∷ []) (Sb2-1-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·0·3·1⟩ c4)
  q169 : WsL → Eqn
  q169 c4 = eqn (Sw01 ∷ Sb⁻2-0-3-1 ∷ []) (Sb⁻2-1-3-0 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·0·3·1⟩ c4)

-- nat 0 SBOX(2;0;41;3): 7 steps
lem-nat-0-SBOX⟨2·0·41·3⟩ : WsL → ⟪ (Sw01 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-1-40-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·0·41·3⟩ c4 = derive (Sw01 ∷ Sb2-0-41-3 ∷ []) (Sb2-1-40-3 ∷ Sw01 ∷ [])
  (re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw 0 (q166 c4) ∷
   rw 1 (q167 c4) ∷
   rw 2 (q168 c4) ∷
   rw 3 (q167 c4) ∷
   rw 4 (q169 c4) ∷
   re 0 5 (Sb2-1-40-3 ∷ []) ∷ []) Eq.refl

private
  q170 : WsL → Eqn
  q170 c4 = eqn (CZ13 ∷ Sw01 ∷ []) (Sw01 ∷ CZ03 ∷ []) (wl0092 c4)

-- nat 0 BOXd(2;03): 3 steps
lem-nat-0-BOXd⟨2·03⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻2-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-13 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨2·03⟩ c4 = derive (Sw01 ∷ Bx⁻2-03 ∷ []) (Bx⁻2-13 ∷ Sw01 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw⁻ 0 (q170 c4) ∷
   re 0 1 (Bx⁻2-13 ∷ []) ∷ []) Eq.refl

private
  q171 : WsL → Eqn
  q171 c4 = eqn (Sw01 ∷ Bx⁻2-03 ∷ []) (Bx⁻2-13 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·03⟩ c4)
  q172 : WsL → Eqn
  q172 c4 = eqn (CCZ012 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ012 ∷ []) (wl0096 c4)
  q173 : WsL → Eqn
  q173 c4 = eqn (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) (wl0099 c4)

-- nat 0 BOXd(0;213): 8 steps
lem-nat-0-BOXd⟨0·213⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻0-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-203 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨0·213⟩ c4 = derive (Sw01 ∷ Bx⁻0-213 ∷ []) (Bx⁻1-203 ∷ Sw01 ∷ [])
  (re 1 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   rw 0 (q171 c4) ∷
   rw⁻ 1 (q172 c4) ∷
   rw 2 (q173 c4) ∷
   rw 3 (q171 c4) ∷
   rw 4 (q173 c4) ∷
   rw⁻ 5 (q172 c4) ∷
   re 0 6 (Bx⁻1-203 ∷ []) ∷ []) Eq.refl

private
  q174 : WsL → Eqn
  q174 c4 = eqn (Sw01 ∷ Bx⁻0-213 ∷ []) (Bx⁻1-203 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨0·213⟩ c4)
  q175 : WsL → Eqn
  q175 c4 = eqn (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4)
  q176 : WsL → Eqn
  q176 c4 = eqn (Sw01 ∷ Toff204 ∷ []) (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4)

-- nat 0 BOXd(2;0413): 8 steps
lem-nat-0-BOXd⟨2·0413⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-1403 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨2·0413⟩ c4 = derive (Sw01 ∷ Bx⁻2-0413 ∷ []) (Bx⁻2-1403 ∷ Sw01 ∷ [])
  (re 1 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) ∷
   rw 0 (q174 c4) ∷
   rw 1 (q175 c4) ∷
   rw 2 (q176 c4) ∷
   rw 3 (q174 c4) ∷
   rw 4 (q176 c4) ∷
   rw 5 (q175 c4) ∷
   re 0 6 (Bx⁻2-1403 ∷ []) ∷ []) Eq.refl

private
  q177 : WsL → Eqn
  q177 c4 = eqn (Sw01 ∷ Bx⁻2-0413 ∷ []) (Bx⁻2-1403 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·0413⟩ c4)

-- nat 0 SBOXd(2;0;41;3): 7 steps
lem-nat-0-SBOXd⟨2·0·41·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-40-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·0·41·3⟩ c4 = derive (Sw01 ∷ Sb⁻2-0-41-3 ∷ []) (Sb⁻2-1-40-3 ∷ Sw01 ∷ [])
  (re 1 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   rw 0 (q168 c4) ∷
   rw 1 (q167 c4) ∷
   rw 2 (q169 c4) ∷
   rw 3 (q167 c4) ∷
   rw 4 (q177 c4) ∷
   re 0 5 (Sb⁻2-1-40-3 ∷ []) ∷ []) Eq.refl

private
  q178 : WsL → Eqn
  q178 c4 = eqn (CZ23 ∷ Sw12 ∷ []) (Sw12 ∷ CZ13 ∷ []) (wl0029 c4)

-- nat 1 BOXd(2;13): 3 steps
lem-nat-1-BOXd⟨2·13⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻2-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-23 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·13⟩ c4 = derive (Sw12 ∷ Bx⁻2-13 ∷ []) (Bx⁻1-23 ∷ Sw12 ∷ [])
  (re 1 1 (CZ13 ∷ []) ∷
   rw⁻ 0 (q178 c4) ∷
   re 0 1 (Bx⁻1-23 ∷ []) ∷ []) Eq.refl

private
  q179 : WsL → Eqn
  q179 c4 = eqn (Sw12 ∷ Bx⁻2-13 ∷ []) (Bx⁻1-23 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·13⟩ c4)
  q180 : WsL → Eqn
  q180 c4 = eqn (CCZ012 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ012 ∷ []) (wl0037 c4)
  q181 : WsL → Eqn
  q181 c4 = eqn (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) (wl0047 c4)

-- nat 1 BOXd(1;203): 8 steps
lem-nat-1-BOXd⟨1·203⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻1-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-103 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·203⟩ c4 = derive (Sw12 ∷ Bx⁻1-203 ∷ []) (Bx⁻2-103 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻2-13 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻2-13 ∷ Toff102 ∷ CCZ012 ∷ []) ∷
   rw 0 (q179 c4) ∷
   rw⁻ 1 (q180 c4) ∷
   rw 2 (q181 c4) ∷
   rw 3 (q179 c4) ∷
   rw 4 (q181 c4) ∷
   rw⁻ 5 (q180 c4) ∷
   re 0 6 (Bx⁻2-103 ∷ []) ∷ []) Eq.refl

private
  q182 : WsL → Eqn
  q182 c4 = eqn (Sw12 ∷ Bx⁻1-203 ∷ []) (Bx⁻2-103 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·203⟩ c4)

-- nat 1 BOXd(2;1403): 8 steps
lem-nat-1-BOXd⟨2·1403⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-2403 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·1403⟩ c4 = derive (Sw12 ∷ Bx⁻2-1403 ∷ []) (Bx⁻1-2403 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻1-203 ∷ CCZ124 ∷ Toff214 ∷ Bx⁻1-203 ∷ Toff214 ∷ CCZ124 ∷ []) ∷
   rw 0 (q182 c4) ∷
   rw⁻ 1 (q56 c4) ∷
   rw 2 (q57 c4) ∷
   rw 3 (q182 c4) ∷
   rw 4 (q57 c4) ∷
   rw⁻ 5 (q56 c4) ∷
   re 0 6 (Bx⁻1-2403 ∷ []) ∷ []) Eq.refl

private
  q183 : WsL → Eqn
  q183 c4 = eqn (Sw12 ∷ Bx⁻2-1403 ∷ []) (Bx⁻1-2403 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·1403⟩ c4)

-- nat 1 SBOXd(2;1;40;3): 7 steps
lem-nat-1-SBOXd⟨2·1·40·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-40-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·1·40·3⟩ c4 = derive (Sw12 ∷ Sb⁻2-1-40-3 ∷ []) (Sb⁻1-2-40-3 ∷ Sw12 ∷ [])
  (re 1 1 (Sb2-1-3-0 ∷ Toff304 ∷ Sb⁻2-1-3-0 ∷ Toff304 ∷ Bx⁻2-1403 ∷ []) ∷
   rw 0 (q164 c4) ∷
   rw 1 (q163 c4) ∷
   rw 2 (q165 c4) ∷
   rw 3 (q163 c4) ∷
   rw 4 (q183 c4) ∷
   re 0 5 (Sb⁻1-2-40-3 ∷ []) ∷ []) Eq.refl

-- nat 2 BOXd(1;23): 3 steps
lem-nat-2-BOXd⟨1·23⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-32 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·23⟩ c4 = derive (Sw23 ∷ Bx⁻1-23 ∷ []) (Bx⁻1-32 ∷ Sw23 ∷ [])
  (re 1 1 (CZ23 ∷ []) ∷
   rw⁻ 0 (q151 c4) ∷
   re 0 1 (Bx⁻1-32 ∷ []) ∷ []) Eq.refl

private
  q184 : WsL → Eqn
  q184 c4 = eqn (Sw23 ∷ Bx⁻1-23 ∷ []) (Bx⁻1-32 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·23⟩ c4)

-- nat 2 BOXd(2;103): 8 steps
lem-nat-2-BOXd⟨2·103⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻2-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻3-102 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨2·103⟩ c4 = derive (Sw23 ∷ Bx⁻2-103 ∷ []) (Bx⁻3-102 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻1-23 ∷ CCZ012 ∷ Toff201 ∷ Bx⁻1-23 ∷ Toff201 ∷ CCZ012 ∷ []) ∷
   rw 0 (q184 c4) ∷
   rw 1 (q152 c4) ∷
   rw 2 (q153 c4) ∷
   rw 3 (q184 c4) ∷
   rw 4 (q153 c4) ∷
   rw 5 (q152 c4) ∷
   re 0 6 (Bx⁻3-102 ∷ []) ∷ []) Eq.refl

private
  q185 : WsL → Eqn
  q185 c4 = eqn (Sw23 ∷ Bx⁻2-103 ∷ []) (Bx⁻3-102 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨2·103⟩ c4)

-- nat 2 BOXd(1;2403): 8 steps
lem-nat-2-BOXd⟨1·2403⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-3402 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·2403⟩ c4 = derive (Sw23 ∷ Bx⁻1-2403 ∷ []) (Bx⁻1-3402 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻2-103 ∷ CCZ124 ∷ Toff124 ∷ Bx⁻2-103 ∷ Toff124 ∷ CCZ124 ∷ []) ∷
   rw 0 (q185 c4) ∷
   rw 1 (q46 c4) ∷
   rw 2 (q47 c4) ∷
   rw 3 (q185 c4) ∷
   rw 4 (q47 c4) ∷
   rw 5 (q46 c4) ∷
   re 0 6 (Bx⁻1-3402 ∷ []) ∷ []) Eq.refl

private
  q186 : WsL → Eqn
  q186 c4 = eqn (Sw23 ∷ Bx⁻1-2403 ∷ []) (Bx⁻1-3402 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·2403⟩ c4)

-- nat 2 SBOXd(1;2;40;3): 7 steps
lem-nat-2-SBOXd⟨1·2·40·3⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-3-40-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·2·40·3⟩ c4 = derive (Sw23 ∷ Sb⁻1-2-40-3 ∷ []) (Sb⁻1-3-40-2 ∷ Sw23 ∷ [])
  (re 1 1 (Sb1-2-3-0 ∷ Toff304 ∷ Sb⁻1-2-3-0 ∷ Toff304 ∷ Bx⁻1-2403 ∷ []) ∷
   rw 0 (q160 c4) ∷
   rw 1 (q159 c4) ∷
   rw 2 (q161 c4) ∷
   rw 3 (q159 c4) ∷
   rw 4 (q186 c4) ∷
   re 0 5 (Sb⁻1-3-40-2 ∷ []) ∷ []) Eq.refl

private
  q187 : WsL → Eqn
  q187 c4 = eqn (Sw34 ∷ CS23 ∷ []) (CS24 ∷ Sw34 ∷ []) (lem-nat-3-CS23 c4)

-- nat 3 SBOX(1;3;2;0): 3 steps
lem-nat-3-SBOX⟨1·3·2·0⟩ : WsL → ⟪ (Sw34 ∷ Sb1-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-4-2-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·3·2·0⟩ c4 = derive (Sw34 ∷ Sb1-3-2-0 ∷ []) (Sb1-4-2-0 ∷ Sw34 ∷ [])
  (re 1 1 (CS23 ∷ []) ∷
   rw 0 (q187 c4) ∷
   re 0 1 (Sb1-4-2-0 ∷ []) ∷ []) Eq.refl

-- nat 3 CSd23: 2 steps
lem-nat-3-CSd23 : WsL → ⟪ (Sw34 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS24⁻ ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CSd23 c4 = derive (Sw34 ∷ CS23⁻ ∷ []) (CS24⁻ ∷ Sw34 ∷ [])
  (rw⁻ 2 (q7 c4) ∷
   re 0 3 (CS24⁻ ∷ []) ∷ []) Eq.refl

private
  q188 : WsL → Eqn
  q188 c4 = eqn (Sw34 ∷ CS23⁻ ∷ []) (CS24⁻ ∷ Sw34 ∷ []) (lem-nat-3-CSd23 c4)

-- nat 3 SBOXd(1;3;2;0): 3 steps
lem-nat-3-SBOXd⟨1·3·2·0⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻1-3-2-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-2-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·3·2·0⟩ c4 = derive (Sw34 ∷ Sb⁻1-3-2-0 ∷ []) (Sb⁻1-4-2-0 ∷ Sw34 ∷ [])
  (re 1 1 (CS23⁻ ∷ []) ∷
   rw 0 (q188 c4) ∷
   re 0 1 (Sb⁻1-4-2-0 ∷ []) ∷ []) Eq.refl

private
  q189 : WsL → Eqn
  q189 c4 = eqn (Sw34 ∷ CZ23 ∷ []) (CZ24 ∷ Sw34 ∷ []) (lem-nat-3-CZ23 c4)

-- nat 3 BOXd(1;32): 3 steps
lem-nat-3-BOXd⟨1·32⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻1-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-42 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·32⟩ c4 = derive (Sw34 ∷ Bx⁻1-32 ∷ []) (Bx⁻1-42 ∷ Sw34 ∷ [])
  (re 1 1 (CZ23 ∷ []) ∷
   rw 0 (q189 c4) ∷
   re 0 1 (Bx⁻1-42 ∷ []) ∷ []) Eq.refl

private
  q190 : WsL → Eqn
  q190 c4 = eqn (Sw34 ∷ Bx⁻1-32 ∷ []) (Bx⁻1-42 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·32⟩ c4)
  q191 : WsL → Eqn
  q191 c4 = eqn (Sw34 ∷ CCZ013 ∷ []) (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4)
  q192 : WsL → Eqn
  q192 c4 = eqn (Sw34 ∷ Toff301 ∷ []) (Toff401 ∷ Sw34 ∷ []) (lem-nat-3-TOFF301 c4)

-- nat 3 BOXd(3;102): 8 steps
lem-nat-3-BOXd⟨3·102⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻3-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-102 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨3·102⟩ c4 = derive (Sw34 ∷ Bx⁻3-102 ∷ []) (Bx⁻4-102 ∷ Sw34 ∷ [])
  (re 1 1 (Bx⁻1-32 ∷ CCZ013 ∷ Toff301 ∷ Bx⁻1-32 ∷ Toff301 ∷ CCZ013 ∷ []) ∷
   rw 0 (q190 c4) ∷
   rw 1 (q191 c4) ∷
   rw 2 (q192 c4) ∷
   rw 3 (q190 c4) ∷
   rw 4 (q192 c4) ∷
   rw 5 (q191 c4) ∷
   re 0 6 (Bx⁻4-102 ∷ []) ∷ []) Eq.refl

private
  q193 : WsL → Eqn
  q193 c4 = eqn (Sw34 ∷ Bx⁻3-102 ∷ []) (Bx⁻4-102 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨3·102⟩ c4)
  q194 : WsL → Eqn
  q194 c4 = eqn (CCZ134 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ134 ∷ []) (wl0154 c4)
  q195 : WsL → Eqn
  q195 c4 = eqn (Sw34 ∷ Toff134 ∷ []) (Toff134 ∷ Sw34 ∷ []) (wl0129 c4)

-- nat 3 BOXd(1;3402): 8 steps
lem-nat-3-BOXd⟨1·3402⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻1-3402 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-4302 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·3402⟩ c4 = derive (Sw34 ∷ Bx⁻1-3402 ∷ []) (Bx⁻1-4302 ∷ Sw34 ∷ [])
  (re 1 1 (Bx⁻3-102 ∷ CCZ134 ∷ Toff134 ∷ Bx⁻3-102 ∷ Toff134 ∷ CCZ134 ∷ []) ∷
   rw 0 (q193 c4) ∷
   rw⁻ 1 (q194 c4) ∷
   rw 2 (q195 c4) ∷
   rw 3 (q193 c4) ∷
   rw 4 (q195 c4) ∷
   rw⁻ 5 (q194 c4) ∷
   re 0 6 (Bx⁻1-4302 ∷ []) ∷ []) Eq.refl

private
  q196 : WsL → Eqn
  q196 c4 = eqn (Sw34 ∷ Sb1-3-2-0 ∷ []) (Sb1-4-2-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·3·2·0⟩ c4)
  q197 : WsL → Eqn
  q197 c4 = eqn (Sw34 ∷ Toff204 ∷ []) (Toff203 ∷ Sw34 ∷ []) (lem-nat-3-TOFF204 c4)
  q198 : WsL → Eqn
  q198 c4 = eqn (Sw34 ∷ Sb⁻1-3-2-0 ∷ []) (Sb⁻1-4-2-0 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·3·2·0⟩ c4)
  q199 : WsL → Eqn
  q199 c4 = eqn (Sw34 ∷ Bx⁻1-3402 ∷ []) (Bx⁻1-4302 ∷ Sw34 ∷ []) (lem-nat-3-BOXd⟨1·3402⟩ c4)

-- nat 3 SBOXd(1;3;40;2): 7 steps
lem-nat-3-SBOXd⟨1·3·40·2⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-30-2 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·3·40·2⟩ c4 = derive (Sw34 ∷ Sb⁻1-3-40-2 ∷ []) (Sb⁻1-4-30-2 ∷ Sw34 ∷ [])
  (re 1 1 (Sb1-3-2-0 ∷ Toff204 ∷ Sb⁻1-3-2-0 ∷ Toff204 ∷ Bx⁻1-3402 ∷ []) ∷
   rw 0 (q196 c4) ∷
   rw 1 (q197 c4) ∷
   rw 2 (q198 c4) ∷
   rw 3 (q197 c4) ∷
   rw 4 (q199 c4) ∷
   re 0 5 (Sb⁻1-4-30-2 ∷ []) ∷ []) Eq.refl

private
  q200 : WsL → Eqn
  q200 c4 = eqn (CZ34 ∷ Sw23 ∷ []) (Sw23 ∷ CZ24 ∷ []) (wl0028 c4)

-- nat 2 BOXd(1;42): 3 steps
lem-nat-2-BOXd⟨1·42⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-43 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·42⟩ c4 = derive (Sw23 ∷ Bx⁻1-42 ∷ []) (Bx⁻1-43 ∷ Sw23 ∷ [])
  (re 1 1 (CZ24 ∷ []) ∷
   rw⁻ 0 (q200 c4) ∷
   re 0 1 (Bx⁻1-43 ∷ []) ∷ []) Eq.refl

private
  q201 : WsL → Eqn
  q201 c4 = eqn (Sw23 ∷ Bx⁻1-42 ∷ []) (Bx⁻1-43 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·42⟩ c4)

-- nat 2 BOXd(4;102): 8 steps
lem-nat-2-BOXd⟨4·102⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻4-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-103 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨4·102⟩ c4 = derive (Sw23 ∷ Bx⁻4-102 ∷ []) (Bx⁻4-103 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻1-42 ∷ CCZ014 ∷ Toff401 ∷ Bx⁻1-42 ∷ Toff401 ∷ CCZ014 ∷ []) ∷
   rw 0 (q201 c4) ∷
   rw 1 (q43 c4) ∷
   rw 2 (q44 c4) ∷
   rw 3 (q201 c4) ∷
   rw 4 (q44 c4) ∷
   rw 5 (q43 c4) ∷
   re 0 6 (Bx⁻4-103 ∷ []) ∷ []) Eq.refl

private
  q202 : WsL → Eqn
  q202 c4 = eqn (Sw23 ∷ Bx⁻4-102 ∷ []) (Bx⁻4-103 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·102⟩ c4)
  q203 : WsL → Eqn
  q203 c4 = eqn (Sw23 ∷ Toff134 ∷ []) (Toff124 ∷ Sw23 ∷ []) (lem-nat-2-TOFF134 c4)

-- nat 2 BOXd(1;4302): 8 steps
lem-nat-2-BOXd⟨1·4302⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-4302 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-4203 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·4302⟩ c4 = derive (Sw23 ∷ Bx⁻1-4302 ∷ []) (Bx⁻1-4203 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻4-102 ∷ CCZ134 ∷ Toff134 ∷ Bx⁻4-102 ∷ Toff134 ∷ CCZ134 ∷ []) ∷
   rw 0 (q202 c4) ∷
   rw 1 (q95 c4) ∷
   rw 2 (q203 c4) ∷
   rw 3 (q202 c4) ∷
   rw 4 (q203 c4) ∷
   rw 5 (q95 c4) ∷
   re 0 6 (Bx⁻1-4203 ∷ []) ∷ []) Eq.refl

private
  q204 : WsL → Eqn
  q204 c4 = eqn (Sw23 ∷ Sb1-4-2-0 ∷ []) (Sb1-4-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·4·2·0⟩ c4)
  q205 : WsL → Eqn
  q205 c4 = eqn (Sw23 ∷ Toff203 ∷ []) (Toff302 ∷ Sw23 ∷ []) (wl0090 c4)
  q206 : WsL → Eqn
  q206 c4 = eqn (Sw23 ∷ Sb⁻1-4-2-0 ∷ []) (Sb⁻1-4-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·4·2·0⟩ c4)
  q207 : WsL → Eqn
  q207 c4 = eqn (Sw23 ∷ Bx⁻1-4302 ∷ []) (Bx⁻1-4203 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·4302⟩ c4)

-- nat 2 SBOXd(1;4;30;2): 7 steps
lem-nat-2-SBOXd⟨1·4·30·2⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-4-30-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-20-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·4·30·2⟩ c4 = derive (Sw23 ∷ Sb⁻1-4-30-2 ∷ []) (Sb⁻1-4-20-3 ∷ Sw23 ∷ [])
  (re 1 1 (Sb1-4-2-0 ∷ Toff203 ∷ Sb⁻1-4-2-0 ∷ Toff203 ∷ Bx⁻1-4302 ∷ []) ∷
   rw 0 (q204 c4) ∷
   rw 1 (q205 c4) ∷
   rw 2 (q206 c4) ∷
   rw 3 (q205 c4) ∷
   rw 4 (q207 c4) ∷
   re 0 5 (Sb⁻1-4-20-3 ∷ []) ∷ []) Eq.refl

private
  q208 : WsL → Eqn
  q208 c4 = eqn (Sw12 ∷ Sb1-4-3-0 ∷ []) (Sb1-4-3-0 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))

-- nat 1 SBOX(1;4;3;0): 2 steps
lem-nat-1-SBOX⟨1·4·3·0⟩ : WsL → ⟪ (Sw12 ∷ Sb1-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·4·3·0⟩ c4 = derive (Sw12 ∷ Sb1-4-3-0 ∷ []) (Sb2-4-3-0 ∷ Sw12 ∷ [])
  (rw 0 (q208 c4) ∷
   re 0 1 (Sb2-4-3-0 ∷ []) ∷ []) Eq.refl

private
  q209 : WsL → Eqn
  q209 c4 = eqn (Sw12 ∷ Sb⁻1-4-3-0 ∷ []) (Sb⁻1-4-3-0 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS))

-- nat 1 SBOXd(1;4;3;0): 2 steps
lem-nat-1-SBOXd⟨1·4·3·0⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-3-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·4·3·0⟩ c4 = derive (Sw12 ∷ Sb⁻1-4-3-0 ∷ []) (Sb⁻2-4-3-0 ∷ Sw12 ∷ [])
  (rw 0 (q209 c4) ∷
   re 0 1 (Sb⁻2-4-3-0 ∷ []) ∷ []) Eq.refl

private
  q210 : WsL → Eqn
  q210 c4 = eqn (Sw12 ∷ Bx⁻1-43 ∷ []) (Bx⁻1-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ))

-- nat 1 BOXd(1;43): 2 steps
lem-nat-1-BOXd⟨1·43⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻1-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-43 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·43⟩ c4 = derive (Sw12 ∷ Bx⁻1-43 ∷ []) (Bx⁻2-43 ∷ Sw12 ∷ [])
  (rw 0 (q210 c4) ∷
   re 0 1 (Bx⁻2-43 ∷ []) ∷ []) Eq.refl

private
  q211 : WsL → Eqn
  q211 c4 = eqn (Sw12 ∷ Bx⁻1-43 ∷ []) (Bx⁻2-43 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·43⟩ c4)
  q212 : WsL → Eqn
  q212 c4 = eqn (Sw12 ∷ CCZ014 ∷ []) (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4)
  q213 : WsL → Eqn
  q213 c4 = eqn (Sw12 ∷ Toff401 ∷ []) (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4)

-- nat 1 BOXd(4;103): 8 steps
lem-nat-1-BOXd⟨4·103⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻4-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-203 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·103⟩ c4 = derive (Sw12 ∷ Bx⁻4-103 ∷ []) (Bx⁻4-203 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻1-43 ∷ CCZ014 ∷ Toff401 ∷ Bx⁻1-43 ∷ Toff401 ∷ CCZ014 ∷ []) ∷
   rw 0 (q211 c4) ∷
   rw 1 (q212 c4) ∷
   rw 2 (q213 c4) ∷
   rw 3 (q211 c4) ∷
   rw 4 (q213 c4) ∷
   rw 5 (q212 c4) ∷
   re 0 6 (Bx⁻4-203 ∷ []) ∷ []) Eq.refl

private
  q214 : WsL → Eqn
  q214 c4 = eqn (Sw12 ∷ Bx⁻4-103 ∷ []) (Bx⁻4-203 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·103⟩ c4)
  q215 : WsL → Eqn
  q215 c4 = eqn (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) (wl0095 c4)

-- nat 1 BOXd(1;4203): 8 steps
lem-nat-1-BOXd⟨1·4203⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻1-4203 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-4103 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·4203⟩ c4 = derive (Sw12 ∷ Bx⁻1-4203 ∷ []) (Bx⁻2-4103 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻4-103 ∷ CCZ124 ∷ Toff124 ∷ Bx⁻4-103 ∷ Toff124 ∷ CCZ124 ∷ []) ∷
   rw 0 (q214 c4) ∷
   rw⁻ 1 (q56 c4) ∷
   rw 2 (q215 c4) ∷
   rw 3 (q214 c4) ∷
   rw 4 (q215 c4) ∷
   rw⁻ 5 (q56 c4) ∷
   re 0 6 (Bx⁻2-4103 ∷ []) ∷ []) Eq.refl

private
  q216 : WsL → Eqn
  q216 c4 = eqn (Sw12 ∷ Sb1-4-3-0 ∷ []) (Sb2-4-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·4·3·0⟩ c4)
  q217 : WsL → Eqn
  q217 c4 = eqn (Sw12 ∷ Toff302 ∷ []) (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4)
  q218 : WsL → Eqn
  q218 c4 = eqn (Sw12 ∷ Sb⁻1-4-3-0 ∷ []) (Sb⁻2-4-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·4·3·0⟩ c4)
  q219 : WsL → Eqn
  q219 c4 = eqn (Sw12 ∷ Bx⁻1-4203 ∷ []) (Bx⁻2-4103 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·4203⟩ c4)

-- nat 1 SBOXd(1;4;20;3): 7 steps
lem-nat-1-SBOXd⟨1·4·20·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-4-20-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-10-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·4·20·3⟩ c4 = derive (Sw12 ∷ Sb⁻1-4-20-3 ∷ []) (Sb⁻2-4-10-3 ∷ Sw12 ∷ [])
  (re 1 1 (Sb1-4-3-0 ∷ Toff302 ∷ Sb⁻1-4-3-0 ∷ Toff302 ∷ Bx⁻1-4203 ∷ []) ∷
   rw 0 (q216 c4) ∷
   rw 1 (q217 c4) ∷
   rw 2 (q218 c4) ∷
   rw 3 (q217 c4) ∷
   rw 4 (q219 c4) ∷
   re 0 5 (Sb⁻2-4-10-3 ∷ []) ∷ []) Eq.refl

private
  q220 : WsL → Eqn
  q220 c4 = eqn (Sw01 ∷ Sb2-4-3-0 ∷ []) (Sb2-4-3-0 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))

-- nat 0 SBOX(2;4;3;0): 2 steps
lem-nat-0-SBOX⟨2·4·3·0⟩ : WsL → ⟪ (Sw01 ∷ Sb2-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·4·3·0⟩ c4 = derive (Sw01 ∷ Sb2-4-3-0 ∷ []) (Sb2-4-3-1 ∷ Sw01 ∷ [])
  (rw 0 (q220 c4) ∷
   re 0 1 (Sb2-4-3-1 ∷ []) ∷ []) Eq.refl

private
  q221 : WsL → Eqn
  q221 c4 = eqn (Sw01 ∷ Sb⁻2-4-3-0 ∷ []) (Sb⁻2-4-3-0 ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑))

-- nat 0 SBOXd(2;4;3;0): 2 steps
lem-nat-0-SBOXd⟨2·4·3·0⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-4-3-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-3-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·4·3·0⟩ c4 = derive (Sw01 ∷ Sb⁻2-4-3-0 ∷ []) (Sb⁻2-4-3-1 ∷ Sw01 ∷ [])
  (rw 0 (q221 c4) ∷
   re 0 1 (Sb⁻2-4-3-1 ∷ []) ∷ []) Eq.refl

private
  q222 : WsL → Eqn
  q222 c4 = eqn (Sw01 ∷ Bx⁻2-43 ∷ []) (Bx⁻2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑))
  q223 : WsL → Eqn
  q223 c4 = eqn (Sw01 ∷ Toff402 ∷ []) (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4)

-- nat 0 BOXd(4;203): 8 steps
lem-nat-0-BOXd⟨4·203⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻4-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-213 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨4·203⟩ c4 = derive (Sw01 ∷ Bx⁻4-203 ∷ []) (Bx⁻4-213 ∷ Sw01 ∷ [])
  (re 1 1 (Bx⁻2-43 ∷ CCZ024 ∷ Toff402 ∷ Bx⁻2-43 ∷ Toff402 ∷ CCZ024 ∷ []) ∷
   rw 0 (q222 c4) ∷
   rw 1 (q175 c4) ∷
   rw 2 (q223 c4) ∷
   rw 3 (q222 c4) ∷
   rw 4 (q223 c4) ∷
   rw 5 (q175 c4) ∷
   re 0 6 (Bx⁻4-213 ∷ []) ∷ []) Eq.refl

private
  q224 : WsL → Eqn
  q224 c4 = eqn (Sw01 ∷ Bx⁻4-203 ∷ []) (Bx⁻4-213 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·203⟩ c4)
  q225 : WsL → Eqn
  q225 c4 = eqn (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4)
  q226 : WsL → Eqn
  q226 c4 = eqn (Sw01 ∷ Toff214 ∷ []) (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4)

-- nat 0 BOXd(2;4103): 8 steps
lem-nat-0-BOXd⟨2·4103⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-4013 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨2·4103⟩ c4 = derive (Sw01 ∷ Bx⁻2-4103 ∷ []) (Bx⁻2-4013 ∷ Sw01 ∷ [])
  (re 1 1 (Bx⁻4-203 ∷ CCZ124 ∷ Toff214 ∷ Bx⁻4-203 ∷ Toff214 ∷ CCZ124 ∷ []) ∷
   rw 0 (q224 c4) ∷
   rw 1 (q225 c4) ∷
   rw 2 (q226 c4) ∷
   rw 3 (q224 c4) ∷
   rw 4 (q226 c4) ∷
   rw 5 (q225 c4) ∷
   re 0 6 (Bx⁻2-4013 ∷ []) ∷ []) Eq.refl

private
  q227 : WsL → Eqn
  q227 c4 = eqn (Sw01 ∷ Sb2-4-3-0 ∷ []) (Sb2-4-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·4·3·0⟩ c4)
  q228 : WsL → Eqn
  q228 c4 = eqn (Sw01 ∷ Sb⁻2-4-3-0 ∷ []) (Sb⁻2-4-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·4·3·0⟩ c4)
  q229 : WsL → Eqn
  q229 c4 = eqn (Sw01 ∷ Bx⁻2-4103 ∷ []) (Bx⁻2-4013 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·4103⟩ c4)

-- nat 0 SBOXd(2;4;10;3): 7 steps
lem-nat-0-SBOXd⟨2·4·10·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-4-10-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-01-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·4·10·3⟩ c4 = derive (Sw01 ∷ Sb⁻2-4-10-3 ∷ []) (Sb⁻2-4-01-3 ∷ Sw01 ∷ [])
  (re 1 1 (Sb2-4-3-0 ∷ Toff301 ∷ Sb⁻2-4-3-0 ∷ Toff301 ∷ Bx⁻2-4103 ∷ []) ∷
   rw 0 (q227 c4) ∷
   rw 1 (q68 c4) ∷
   rw 2 (q228 c4) ∷
   rw 3 (q68 c4) ∷
   rw 4 (q229 c4) ∷
   re 0 5 (Sb⁻2-4-01-3 ∷ []) ∷ []) Eq.refl

private
  q230 : WsL → Eqn
  q230 c4 = eqn (CZ03 ∷ Sw01 ∷ []) (Sw01 ∷ CZ13 ∷ []) (wl0088 c4)

-- nat 0 BOXd(2;13): 3 steps
lem-nat-0-BOXd⟨2·13⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻2-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-03 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨2·13⟩ c4 = derive (Sw01 ∷ Bx⁻2-13 ∷ []) (Bx⁻2-03 ∷ Sw01 ∷ [])
  (re 1 1 (CZ13 ∷ []) ∷
   rw⁻ 0 (q230 c4) ∷
   re 0 1 (Bx⁻2-03 ∷ []) ∷ []) Eq.refl

private
  q231 : WsL → Eqn
  q231 c4 = eqn (Sw01 ∷ Bx⁻2-13 ∷ []) (Bx⁻2-03 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·13⟩ c4)
  q232 : WsL → Eqn
  q232 c4 = eqn (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) (wl0097 c4)

-- nat 0 BOXd(1;203): 8 steps
lem-nat-0-BOXd⟨1·203⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻1-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻0-213 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨1·203⟩ c4 = derive (Sw01 ∷ Bx⁻1-203 ∷ []) (Bx⁻0-213 ∷ Sw01 ∷ [])
  (re 1 1 (Bx⁻2-13 ∷ CCZ012 ∷ Toff102 ∷ Bx⁻2-13 ∷ Toff102 ∷ CCZ012 ∷ []) ∷
   rw 0 (q231 c4) ∷
   rw⁻ 1 (q172 c4) ∷
   rw 2 (q232 c4) ∷
   rw 3 (q231 c4) ∷
   rw 4 (q232 c4) ∷
   rw⁻ 5 (q172 c4) ∷
   re 0 6 (Bx⁻0-213 ∷ []) ∷ []) Eq.refl

private
  q233 : WsL → Eqn
  q233 c4 = eqn (Sw01 ∷ Bx⁻1-203 ∷ []) (Bx⁻0-213 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨1·203⟩ c4)

-- nat 0 BOXd(2;1403): 8 steps
lem-nat-0-BOXd⟨2·1403⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻2-1403 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-0413 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨2·1403⟩ c4 = derive (Sw01 ∷ Bx⁻2-1403 ∷ []) (Bx⁻2-0413 ∷ Sw01 ∷ [])
  (re 1 1 (Bx⁻1-203 ∷ CCZ124 ∷ Toff214 ∷ Bx⁻1-203 ∷ Toff214 ∷ CCZ124 ∷ []) ∷
   rw 0 (q233 c4) ∷
   rw 1 (q225 c4) ∷
   rw 2 (q226 c4) ∷
   rw 3 (q233 c4) ∷
   rw 4 (q226 c4) ∷
   rw 5 (q225 c4) ∷
   re 0 6 (Bx⁻2-0413 ∷ []) ∷ []) Eq.refl

private
  q234 : WsL → Eqn
  q234 c4 = eqn (Sw01 ∷ Sb2-1-3-0 ∷ []) (Sb2-0-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·1·3·0⟩ c4)
  q235 : WsL → Eqn
  q235 c4 = eqn (Sw01 ∷ Toff304 ∷ []) (Toff314 ∷ Sw01 ∷ []) (lem-nat-0-TOFF304 c4)
  q236 : WsL → Eqn
  q236 c4 = eqn (Sw01 ∷ Sb⁻2-1-3-0 ∷ []) (Sb⁻2-0-3-1 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·1·3·0⟩ c4)
  q237 : WsL → Eqn
  q237 c4 = eqn (Sw01 ∷ Bx⁻2-1403 ∷ []) (Bx⁻2-0413 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·1403⟩ c4)

-- nat 0 SBOXd(2;1;40;3): 7 steps
lem-nat-0-SBOXd⟨2·1·40·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-1-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-0-41-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·1·40·3⟩ c4 = derive (Sw01 ∷ Sb⁻2-1-40-3 ∷ []) (Sb⁻2-0-41-3 ∷ Sw01 ∷ [])
  (re 1 1 (Sb2-1-3-0 ∷ Toff304 ∷ Sb⁻2-1-3-0 ∷ Toff304 ∷ Bx⁻2-1403 ∷ []) ∷
   rw 0 (q234 c4) ∷
   rw 1 (q235 c4) ∷
   rw 2 (q236 c4) ∷
   rw 3 (q235 c4) ∷
   rw 4 (q237 c4) ∷
   re 0 5 (Sb⁻2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q238 : WsL → Eqn
  q238 c4 = eqn (Sw01 ∷ Toff412 ∷ []) (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4)

-- nat 0 BOXd(4;213): 8 steps
lem-nat-0-BOXd⟨4·213⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻4-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-203 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨4·213⟩ c4 = derive (Sw01 ∷ Bx⁻4-213 ∷ []) (Bx⁻4-203 ∷ Sw01 ∷ [])
  (re 1 1 (Bx⁻2-43 ∷ CCZ124 ∷ Toff412 ∷ Bx⁻2-43 ∷ Toff412 ∷ CCZ124 ∷ []) ∷
   rw 0 (q222 c4) ∷
   rw 1 (q225 c4) ∷
   rw 2 (q238 c4) ∷
   rw 3 (q222 c4) ∷
   rw 4 (q238 c4) ∷
   rw 5 (q225 c4) ∷
   re 0 6 (Bx⁻4-203 ∷ []) ∷ []) Eq.refl

private
  q239 : WsL → Eqn
  q239 c4 = eqn (Sw01 ∷ Bx⁻4-213 ∷ []) (Bx⁻4-203 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨4·213⟩ c4)

-- nat 0 BOXd(2;4013): 8 steps
lem-nat-0-BOXd⟨2·4013⟩ : WsL → ⟪ (Sw01 ∷ Bx⁻2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-4103 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOXd⟨2·4013⟩ c4 = derive (Sw01 ∷ Bx⁻2-4013 ∷ []) (Bx⁻2-4103 ∷ Sw01 ∷ [])
  (re 1 1 (Bx⁻4-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻4-213 ∷ Toff204 ∷ CCZ024 ∷ []) ∷
   rw 0 (q239 c4) ∷
   rw 1 (q175 c4) ∷
   rw 2 (q176 c4) ∷
   rw 3 (q239 c4) ∷
   rw 4 (q176 c4) ∷
   rw 5 (q175 c4) ∷
   re 0 6 (Bx⁻2-4103 ∷ []) ∷ []) Eq.refl

private
  q240 : WsL → Eqn
  q240 c4 = eqn (Sw01 ∷ Bx⁻2-4013 ∷ []) (Bx⁻2-4103 ∷ Sw01 ∷ []) (lem-nat-0-BOXd⟨2·4013⟩ c4)

-- nat 0 SBOXd(2;4;01;3): 7 steps
lem-nat-0-SBOXd⟨2·4·01·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-4-10-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·4·01·3⟩ c4 = derive (Sw01 ∷ Sb⁻2-4-01-3 ∷ []) (Sb⁻2-4-10-3 ∷ Sw01 ∷ [])
  (re 1 1 (Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ Toff301 ∷ Bx⁻2-4013 ∷ []) ∷
   rw 0 (q69 c4) ∷
   rw 1 (q68 c4) ∷
   rw 2 (q70 c4) ∷
   rw 3 (q68 c4) ∷
   rw 4 (q240 c4) ∷
   re 0 5 (Sb⁻2-4-10-3 ∷ []) ∷ []) Eq.refl

private
  q241 : WsL → Eqn
  q241 c4 = eqn (CZ13 ∷ Sw12 ∷ []) (Sw12 ∷ CZ23 ∷ []) (wl0026 c4)

-- nat 1 BOXd(1;23): 3 steps
lem-nat-1-BOXd⟨1·23⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻1-23 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-13 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·23⟩ c4 = derive (Sw12 ∷ Bx⁻1-23 ∷ []) (Bx⁻2-13 ∷ Sw12 ∷ [])
  (re 1 1 (CZ23 ∷ []) ∷
   rw⁻ 0 (q241 c4) ∷
   re 0 1 (Bx⁻2-13 ∷ []) ∷ []) Eq.refl

private
  q242 : WsL → Eqn
  q242 c4 = eqn (Sw12 ∷ Bx⁻1-23 ∷ []) (Bx⁻2-13 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·23⟩ c4)
  q243 : WsL → Eqn
  q243 c4 = eqn (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) (wl0044 c4)

-- nat 1 BOXd(2;103): 8 steps
lem-nat-1-BOXd⟨2·103⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻2-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-203 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·103⟩ c4 = derive (Sw12 ∷ Bx⁻2-103 ∷ []) (Bx⁻1-203 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻1-23 ∷ CCZ012 ∷ Toff201 ∷ Bx⁻1-23 ∷ Toff201 ∷ CCZ012 ∷ []) ∷
   rw 0 (q242 c4) ∷
   rw⁻ 1 (q180 c4) ∷
   rw 2 (q243 c4) ∷
   rw 3 (q242 c4) ∷
   rw 4 (q243 c4) ∷
   rw⁻ 5 (q180 c4) ∷
   re 0 6 (Bx⁻1-203 ∷ []) ∷ []) Eq.refl

private
  q244 : WsL → Eqn
  q244 c4 = eqn (Sw12 ∷ Bx⁻2-103 ∷ []) (Bx⁻1-203 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·103⟩ c4)

-- nat 1 BOXd(1;2403): 8 steps
lem-nat-1-BOXd⟨1·2403⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻1-2403 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-1403 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨1·2403⟩ c4 = derive (Sw12 ∷ Bx⁻1-2403 ∷ []) (Bx⁻2-1403 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻2-103 ∷ CCZ124 ∷ Toff124 ∷ Bx⁻2-103 ∷ Toff124 ∷ CCZ124 ∷ []) ∷
   rw 0 (q244 c4) ∷
   rw⁻ 1 (q56 c4) ∷
   rw 2 (q215 c4) ∷
   rw 3 (q244 c4) ∷
   rw 4 (q215 c4) ∷
   rw⁻ 5 (q56 c4) ∷
   re 0 6 (Bx⁻2-1403 ∷ []) ∷ []) Eq.refl

private
  q245 : WsL → Eqn
  q245 c4 = eqn (Sw12 ∷ Sb1-2-3-0 ∷ []) (Sb2-1-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·2·3·0⟩ c4)
  q246 : WsL → Eqn
  q246 c4 = eqn (Sw12 ∷ Sb⁻1-2-3-0 ∷ []) (Sb⁻2-1-3-0 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·2·3·0⟩ c4)
  q247 : WsL → Eqn
  q247 c4 = eqn (Sw12 ∷ Bx⁻1-2403 ∷ []) (Bx⁻2-1403 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨1·2403⟩ c4)

-- nat 1 SBOXd(1;2;40;3): 7 steps
lem-nat-1-SBOXd⟨1·2·40·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-2-40-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-1-40-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·2·40·3⟩ c4 = derive (Sw12 ∷ Sb⁻1-2-40-3 ∷ []) (Sb⁻2-1-40-3 ∷ Sw12 ∷ [])
  (re 1 1 (Sb1-2-3-0 ∷ Toff304 ∷ Sb⁻1-2-3-0 ∷ Toff304 ∷ Bx⁻1-2403 ∷ []) ∷
   rw 0 (q245 c4) ∷
   rw 1 (q163 c4) ∷
   rw 2 (q246 c4) ∷
   rw 3 (q163 c4) ∷
   rw 4 (q247 c4) ∷
   re 0 5 (Sb⁻2-1-40-3 ∷ []) ∷ []) Eq.refl

private
  q248 : WsL → Eqn
  q248 c4 = eqn (Sw12 ∷ Bx⁻2-43 ∷ []) (Bx⁻1-43 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·43⟩ c4)

-- nat 1 BOXd(4;203): 8 steps
lem-nat-1-BOXd⟨4·203⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻4-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-103 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨4·203⟩ c4 = derive (Sw12 ∷ Bx⁻4-203 ∷ []) (Bx⁻4-103 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻2-43 ∷ CCZ024 ∷ Toff402 ∷ Bx⁻2-43 ∷ Toff402 ∷ CCZ024 ∷ []) ∷
   rw 0 (q248 c4) ∷
   rw 1 (q53 c4) ∷
   rw 2 (q54 c4) ∷
   rw 3 (q248 c4) ∷
   rw 4 (q54 c4) ∷
   rw 5 (q53 c4) ∷
   re 0 6 (Bx⁻4-103 ∷ []) ∷ []) Eq.refl

private
  q249 : WsL → Eqn
  q249 c4 = eqn (Sw12 ∷ Bx⁻4-203 ∷ []) (Bx⁻4-103 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨4·203⟩ c4)

-- nat 1 BOXd(2;4103): 8 steps
lem-nat-1-BOXd⟨2·4103⟩ : WsL → ⟪ (Sw12 ∷ Bx⁻2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-4203 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOXd⟨2·4103⟩ c4 = derive (Sw12 ∷ Bx⁻2-4103 ∷ []) (Bx⁻1-4203 ∷ Sw12 ∷ [])
  (re 1 1 (Bx⁻4-203 ∷ CCZ124 ∷ Toff214 ∷ Bx⁻4-203 ∷ Toff214 ∷ CCZ124 ∷ []) ∷
   rw 0 (q249 c4) ∷
   rw⁻ 1 (q56 c4) ∷
   rw 2 (q57 c4) ∷
   rw 3 (q249 c4) ∷
   rw 4 (q57 c4) ∷
   rw⁻ 5 (q56 c4) ∷
   re 0 6 (Bx⁻1-4203 ∷ []) ∷ []) Eq.refl

private
  q250 : WsL → Eqn
  q250 c4 = eqn (Sw12 ∷ Bx⁻2-4103 ∷ []) (Bx⁻1-4203 ∷ Sw12 ∷ []) (lem-nat-1-BOXd⟨2·4103⟩ c4)

-- nat 1 SBOXd(2;4;10;3): 7 steps
lem-nat-1-SBOXd⟨2·4·10·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-4-10-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-20-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·4·10·3⟩ c4 = derive (Sw12 ∷ Sb⁻2-4-10-3 ∷ []) (Sb⁻1-4-20-3 ∷ Sw12 ∷ [])
  (re 1 1 (Sb2-4-3-0 ∷ Toff301 ∷ Sb⁻2-4-3-0 ∷ Toff301 ∷ Bx⁻2-4103 ∷ []) ∷
   rw 0 (q63 c4) ∷
   rw 1 (q62 c4) ∷
   rw 2 (q64 c4) ∷
   rw 3 (q62 c4) ∷
   rw 4 (q250 c4) ∷
   re 0 5 (Sb⁻1-4-20-3 ∷ []) ∷ []) Eq.refl

-- nat 2 BOXd(1;32): 3 steps
lem-nat-2-BOXd⟨1·32⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-23 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·32⟩ c4 = derive (Sw23 ∷ Bx⁻1-32 ∷ []) (Bx⁻1-23 ∷ Sw23 ∷ [])
  (re 1 1 (CZ23 ∷ []) ∷
   rw⁻ 0 (q151 c4) ∷
   re 0 1 (Bx⁻1-23 ∷ []) ∷ []) Eq.refl

private
  q251 : WsL → Eqn
  q251 c4 = eqn (Sw23 ∷ Bx⁻1-32 ∷ []) (Bx⁻1-23 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·32⟩ c4)
  q252 : WsL → Eqn
  q252 c4 = eqn (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4)
  q253 : WsL → Eqn
  q253 c4 = eqn (Sw23 ∷ Toff301 ∷ []) (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4)

-- nat 2 BOXd(3;102): 8 steps
lem-nat-2-BOXd⟨3·102⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻3-102 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻2-103 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨3·102⟩ c4 = derive (Sw23 ∷ Bx⁻3-102 ∷ []) (Bx⁻2-103 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻1-32 ∷ CCZ013 ∷ Toff301 ∷ Bx⁻1-32 ∷ Toff301 ∷ CCZ013 ∷ []) ∷
   rw 0 (q251 c4) ∷
   rw 1 (q252 c4) ∷
   rw 2 (q253 c4) ∷
   rw 3 (q251 c4) ∷
   rw 4 (q253 c4) ∷
   rw 5 (q252 c4) ∷
   re 0 6 (Bx⁻2-103 ∷ []) ∷ []) Eq.refl

private
  q254 : WsL → Eqn
  q254 c4 = eqn (Sw23 ∷ Bx⁻3-102 ∷ []) (Bx⁻2-103 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨3·102⟩ c4)

-- nat 2 BOXd(1;3402): 8 steps
lem-nat-2-BOXd⟨1·3402⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-3402 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-2403 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·3402⟩ c4 = derive (Sw23 ∷ Bx⁻1-3402 ∷ []) (Bx⁻1-2403 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻3-102 ∷ CCZ134 ∷ Toff134 ∷ Bx⁻3-102 ∷ Toff134 ∷ CCZ134 ∷ []) ∷
   rw 0 (q254 c4) ∷
   rw 1 (q95 c4) ∷
   rw 2 (q203 c4) ∷
   rw 3 (q254 c4) ∷
   rw 4 (q203 c4) ∷
   rw 5 (q95 c4) ∷
   re 0 6 (Bx⁻1-2403 ∷ []) ∷ []) Eq.refl

private
  q255 : WsL → Eqn
  q255 c4 = eqn (Sw23 ∷ Sb1-3-2-0 ∷ []) (Sb1-2-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·3·2·0⟩ c4)
  q256 : WsL → Eqn
  q256 c4 = eqn (Sw23 ∷ Toff204 ∷ []) (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4)
  q257 : WsL → Eqn
  q257 c4 = eqn (Sw23 ∷ Sb⁻1-3-2-0 ∷ []) (Sb⁻1-2-3-0 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·3·2·0⟩ c4)
  q258 : WsL → Eqn
  q258 c4 = eqn (Sw23 ∷ Bx⁻1-3402 ∷ []) (Bx⁻1-2403 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·3402⟩ c4)

-- nat 2 SBOXd(1;3;40;2): 7 steps
lem-nat-2-SBOXd⟨1·3·40·2⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-3-40-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-40-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·3·40·2⟩ c4 = derive (Sw23 ∷ Sb⁻1-3-40-2 ∷ []) (Sb⁻1-2-40-3 ∷ Sw23 ∷ [])
  (re 1 1 (Sb1-3-2-0 ∷ Toff204 ∷ Sb⁻1-3-2-0 ∷ Toff204 ∷ Bx⁻1-3402 ∷ []) ∷
   rw 0 (q255 c4) ∷
   rw 1 (q256 c4) ∷
   rw 2 (q257 c4) ∷
   rw 3 (q256 c4) ∷
   rw 4 (q258 c4) ∷
   re 0 5 (Sb⁻1-2-40-3 ∷ []) ∷ []) Eq.refl

-- nat 2 BOXd(1;43): 3 steps
lem-nat-2-BOXd⟨1·43⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-42 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·43⟩ c4 = derive (Sw23 ∷ Bx⁻1-43 ∷ []) (Bx⁻1-42 ∷ Sw23 ∷ [])
  (re 1 1 (CZ34 ∷ []) ∷
   rw⁻ 0 (q42 c4) ∷
   re 0 1 (Bx⁻1-42 ∷ []) ∷ []) Eq.refl

private
  q259 : WsL → Eqn
  q259 c4 = eqn (Sw23 ∷ Bx⁻1-43 ∷ []) (Bx⁻1-42 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·43⟩ c4)

-- nat 2 BOXd(4;103): 8 steps
lem-nat-2-BOXd⟨4·103⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻4-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻4-102 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨4·103⟩ c4 = derive (Sw23 ∷ Bx⁻4-103 ∷ []) (Bx⁻4-102 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻1-43 ∷ CCZ014 ∷ Toff401 ∷ Bx⁻1-43 ∷ Toff401 ∷ CCZ014 ∷ []) ∷
   rw 0 (q259 c4) ∷
   rw 1 (q43 c4) ∷
   rw 2 (q44 c4) ∷
   rw 3 (q259 c4) ∷
   rw 4 (q44 c4) ∷
   rw 5 (q43 c4) ∷
   re 0 6 (Bx⁻4-102 ∷ []) ∷ []) Eq.refl

private
  q260 : WsL → Eqn
  q260 c4 = eqn (Sw23 ∷ Bx⁻4-103 ∷ []) (Bx⁻4-102 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨4·103⟩ c4)

-- nat 2 BOXd(1;4203): 8 steps
lem-nat-2-BOXd⟨1·4203⟩ : WsL → ⟪ (Sw23 ∷ Bx⁻1-4203 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-4302 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOXd⟨1·4203⟩ c4 = derive (Sw23 ∷ Bx⁻1-4203 ∷ []) (Bx⁻1-4302 ∷ Sw23 ∷ [])
  (re 1 1 (Bx⁻4-103 ∷ CCZ124 ∷ Toff124 ∷ Bx⁻4-103 ∷ Toff124 ∷ CCZ124 ∷ []) ∷
   rw 0 (q260 c4) ∷
   rw 1 (q46 c4) ∷
   rw 2 (q47 c4) ∷
   rw 3 (q260 c4) ∷
   rw 4 (q47 c4) ∷
   rw 5 (q46 c4) ∷
   re 0 6 (Bx⁻1-4302 ∷ []) ∷ []) Eq.refl

private
  q261 : WsL → Eqn
  q261 c4 = eqn (Sw23 ∷ Bx⁻1-4203 ∷ []) (Bx⁻1-4302 ∷ Sw23 ∷ []) (lem-nat-2-BOXd⟨1·4203⟩ c4)

-- nat 2 SBOXd(1;4;20;3): 7 steps
lem-nat-2-SBOXd⟨1·4·20·3⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-4-20-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-4-30-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·4·20·3⟩ c4 = derive (Sw23 ∷ Sb⁻1-4-20-3 ∷ []) (Sb⁻1-4-30-2 ∷ Sw23 ∷ [])
  (re 1 1 (Sb1-4-3-0 ∷ Toff302 ∷ Sb⁻1-4-3-0 ∷ Toff302 ∷ Bx⁻1-4203 ∷ []) ∷
   rw 0 (q51 c4) ∷
   rw 1 (q50 c4) ∷
   rw 2 (q52 c4) ∷
   rw 3 (q50 c4) ∷
   rw 4 (q261 c4) ∷
   re 0 5 (Sb⁻1-4-30-2 ∷ []) ∷ []) Eq.refl

private
  q262 : WsL → Eqn
  q262 c4 = eqn (Sw34 ∷ CZ24 ∷ []) (CZ23 ∷ Sw34 ∷ []) (lem-nat-3-CZ24 c4)

-- nat 3 BOXd(1;42): 3 steps
lem-nat-3-BOXd⟨1·42⟩ : WsL → ⟪ (Sw34 ∷ Bx⁻1-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx⁻1-32 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOXd⟨1·42⟩ c4 = derive (Sw34 ∷ Bx⁻1-42 ∷ []) (Bx⁻1-32 ∷ Sw34 ∷ [])
  (re 1 1 (CZ24 ∷ []) ∷
   rw 0 (q262 c4) ∷
   re 0 1 (Bx⁻1-32 ∷ []) ∷ []) Eq.refl
