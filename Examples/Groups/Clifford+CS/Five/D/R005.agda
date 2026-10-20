{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R005 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0013 ; wl0019 ; wl0021 ; wl0022 ; wl0023 ; wl0030 ; wl0032 ; wl0033 ; wl0037 ; wl0038 ; wl0044 ; wl0047 ; wl0048 ; wl0056 ; wl0057 ; wl0058 ; wl0059 ; wl0060 ; wl0061 ; wl0063 ; wl0065 ; wl0066 ; wl0067 ; wl0068 ; wl0070 ; wl0076 ; wl0078 ; wl0088 ; wl0090 ; wl0092 ; wl0093 ; wl0094 ; wl0095 ; wl0096 ; wl0097 ; wl0098 ; wl0099 ; wl0100 ; wl0101 ; wl0102)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF024 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ013 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-2-TOFF013 ; lem-nat-2-TOFF024 ; lem-nat-2-TOFF034 ; lem-nat-2-TOFF301 ; lem-nat-3-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF301 ; lem-nat-1-TOFF302 ; lem-nat-2-CCZ124 ; lem-nat-2-TOFF201 ; lem-nat-2-TOFF204 ; lem-nat-2-TOFF304 ; lem-nat-3-BOX⟨0·14⟩ ; lem-nat-3-CCZ013 ; lem-nat-3-CCZ023 ; lem-nat-3-TOFF203 ; lem-nat-3-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-CCZ014 ; lem-nat-0-TOFF014 ; lem-nat-0-TOFF104 ; lem-nat-1-TOFF104 ; lem-nat-1-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-BOX⟨0·43⟩ ; lem-nat-0-CZ04 ; lem-nat-0-CZ14 ; lem-nat-0-TOFF214 ; lem-nat-0-TOFF402 ; lem-nat-1-BOX⟨1·43⟩ ; lem-nat-1-TOFF013 ; lem-nat-2-BOX⟨2·43⟩)

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
  q16 c4 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wl0076 c4)
  q17 : WsL → Eqn
  q17 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q18 : WsL → Eqn
  q18 c4 = eqn (CX12 ∷ Sw01 ∷ []) (Sw01 ∷ CX02 ∷ []) (wl0060 c4)
  q19 : WsL → Eqn
  q19 c4 = eqn (Sw01 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q20 : WsL → Eqn
  q20 c4 = eqn (Sw01 ∷ Sw34 ∷ []) (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑))
  q21 : WsL → Eqn
  q21 c4 = eqn (CS13 ∷ Sw01 ∷ []) (Sw01 ∷ CS03 ∷ []) (wl0061 c4)
  q22 : WsL → Eqn
  q22 c4 = eqn (Sw01 ∷ ι ∷ []) (ι ∷ Sw01 ∷ []) (wl0030 c4)
  q23 : WsL → Eqn
  q23 c4 = eqn (K1 ∷ Sw34 ∷ []) (Sw34 ∷ K1 ∷ []) (c₂ (K ↑) (Swap ↑))
  q24 : WsL → Eqn
  q24 c4 = eqn (CX12 ∷ Sw34 ∷ []) (Sw34 ∷ CX12 ∷ []) (c₃ (CX₀₁ ↑) (Swap))
  q25 : WsL → Eqn
  q25 c4 = eqn (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wl0032 c4)

-- nat 0 TOFF024: 70 steps
lem-nat-0-TOFF024 : WsL → ⟪ (Sw01 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF024 c4 = derive (Sw01 ∷ Toff024 ∷ []) (Toff124 ∷ Sw01 ∷ [])
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
   rw⁻ 0 (q16 c4) ∷
   rw 1 (q17 c4) ∷
   rw⁻ 2 (q18 c4) ∷
   rw 3 (q19 c4) ∷
   rw⁻ 4 (q18 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q20 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   rw 7 (q20 c4) ∷
   re 5 3 (CS14 ∷ []) ∷
   rw⁻ 6 (q16 c4) ∷
   rw 7 (q22 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   rw⁻ 1 (q23 c4) ∷
   re 3 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 2 (q6 c4) ∷
   rw⁻ 3 (q24 c4) ∷
   re 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q24 c4) ∷
   re 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q23 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw 1 (q25 c4) ∷
   re 1 8 (Toff123 ∷ []) ∷
   re 0 3 (Toff124 ∷ []) ∷ []) Eq.refl

private
  q26 : WsL → Eqn
  q26 c4 = eqn (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ []) (wl0057 c4)
  q27 : WsL → Eqn
  q27 c4 = eqn (K4 ∷ Sw34 ∷ []) (Sw34 ∷ K3 ∷ []) (wl0067 c4)
  q28 : WsL → Eqn
  q28 c4 = eqn (Sw01 ∷ K4 ∷ []) (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑))
  q29 : WsL → Eqn
  q29 c4 = eqn (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) (wl0019 c4)
  q30 : WsL → Eqn
  q30 c4 = eqn (CX10 ∷ Sw01 ∷ []) (Sw01 ∷ CX01 ∷ []) (wl0070 c4)
  q31 : WsL → Eqn
  q31 c4 = eqn (CS03⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS13⁻ ∷ []) (wl0022 c4)
  q32 : WsL → Eqn
  q32 c4 = eqn (K3 ∷ Sw34 ∷ []) (Sw34 ∷ K4 ∷ []) (wl0068 c4)
  q33 : WsL → Eqn
  q33 c4 = eqn (CX10 ∷ Sw34 ∷ []) (Sw34 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Swap ↑))
  q34 : WsL → Eqn
  q34 c4 = eqn (K2 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ []) (wl0058 c4)
  q35 : WsL → Eqn
  q35 c4 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Swap))
  q36 : WsL → Eqn
  q36 c4 = eqn (K2 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (wl0094 c4)

-- nat 0 TOFF401: 75 steps
lem-nat-0-TOFF401 : WsL → ⟪ (Sw01 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF401 c4 = derive (Sw01 ∷ Toff401 ∷ []) (Toff401 ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) ∷
   re 2 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw⁻ 2 (q26 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 (q3 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q3 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 (q26 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw 10 (q2 c4) ∷
   rw⁻ 1 (q27 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (CS14 ∷ []) ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CS14⁻ ∷ []) ∷
   rw⁻ 5 (q7 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q27 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw 9 (q6 c4) ∷
   rw 0 (q28 c4) ∷
   re 2 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 1 (q20 c4) ∷
   rw⁻ 2 (q29 c4) ∷
   rw 3 (q20 c4) ∷
   re 1 3 (CS04 ∷ []) ∷
   rw⁻ 2 (q30 c4) ∷
   re 4 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 3 (q20 c4) ∷
   rw⁻ 4 (q31 c4) ∷
   rw 5 (q20 c4) ∷
   re 3 3 (CS04⁻ ∷ []) ∷
   rw⁻ 4 (q30 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q20 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   rw 7 (q20 c4) ∷
   re 5 3 (CS14 ∷ []) ∷
   rw 6 (q28 c4) ∷
   rw 7 (q22 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   rw⁻ 1 (q32 c4) ∷
   re 3 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 2 (q6 c4) ∷
   rw⁻ 3 (q33 c4) ∷
   re 5 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q33 c4) ∷
   re 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   rw⁻ 2 (q34 c4) ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 4 (q35 c4) ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 (q2 c4) ∷
   rw⁻ 6 (q35 c4) ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 (q2 c4) ∷
   rw⁻ 8 (q34 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw 2 (q36 c4) ∷
   re 2 8 (Toff201 ∷ []) ∷
   re 1 3 (Toff301 ∷ []) ∷
   re 0 3 (Toff401 ∷ []) ∷ []) Eq.refl

private
  q37 : WsL → Eqn
  q37 c4 = eqn (Sw01 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4)
  q38 : WsL → Eqn
  q38 c4 = eqn (Sw01 ∷ Toff401 ∷ []) (Toff401 ∷ Sw01 ∷ []) (lem-nat-0-TOFF401 c4)
  q39 : WsL → Eqn
  q39 c4 = eqn (Sw01 ∷ Bx0-43 ∷ []) (Bx1-43 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·43⟩ c4)

-- nat 0 BOX(4;013): 8 steps
lem-nat-0-BOX⟨4·013⟩ : WsL → ⟪ (Sw01 ∷ Bx4-013 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-103 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·013⟩ c4 = derive (Sw01 ∷ Bx4-013 ∷ []) (Bx4-103 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) ∷
   rw 0 (q37 c4) ∷
   rw 1 (q38 c4) ∷
   rw 2 (q39 c4) ∷
   rw 3 (q38 c4) ∷
   rw 4 (q37 c4) ∷
   rw 5 (q39 c4) ∷
   re 0 6 (Bx4-103 ∷ []) ∷ []) Eq.refl

private
  q40 : WsL → Eqn
  q40 c4 = eqn (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4)
  q41 : WsL → Eqn
  q41 c4 = eqn (Sw01 ∷ Toff024 ∷ []) (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4)
  q42 : WsL → Eqn
  q42 c4 = eqn (Sw01 ∷ Bx4-013 ∷ []) (Bx4-103 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·013⟩ c4)

-- nat 0 BOX(0;4213): 8 steps
lem-nat-0-BOX⟨0·4213⟩ : WsL → ⟪ (Sw01 ∷ Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4203 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·4213⟩ c4 = derive (Sw01 ∷ Bx0-4213 ∷ []) (Bx1-4203 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ Bx4-013 ∷ []) ∷
   rw 0 (q40 c4) ∷
   rw 1 (q41 c4) ∷
   rw 2 (q42 c4) ∷
   rw 3 (q41 c4) ∷
   rw 4 (q40 c4) ∷
   rw 5 (q42 c4) ∷
   re 0 6 (Bx1-4203 ∷ []) ∷ []) Eq.refl

-- nat 1 TOFF401: 2 steps
lem-nat-1-TOFF401 : WsL → ⟪ (Sw12 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF401 c4 = derive (Sw12 ∷ Toff401 ∷ []) (Toff402 ∷ Sw12 ∷ [])
  (rw⁻ 2 (q11 c4) ∷
   re 0 3 (Toff402 ∷ []) ∷ []) Eq.refl

private
  q43 : WsL → Eqn
  q43 c4 = eqn (Sw12 ∷ CCZ014 ∷ []) (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4)
  q44 : WsL → Eqn
  q44 c4 = eqn (Sw12 ∷ Toff401 ∷ []) (Toff402 ∷ Sw12 ∷ []) (lem-nat-1-TOFF401 c4)
  q45 : WsL → Eqn
  q45 c4 = eqn (Sw12 ∷ Bx1-43 ∷ []) (Bx2-43 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·43⟩ c4)

-- nat 1 BOX(4;103): 8 steps
lem-nat-1-BOX⟨4·103⟩ : WsL → ⟪ (Sw12 ∷ Bx4-103 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-203 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·103⟩ c4 = derive (Sw12 ∷ Bx4-103 ∷ []) (Bx4-203 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff401 ∷ Bx1-43 ∷ Toff401 ∷ CCZ014 ∷ Bx1-43 ∷ []) ∷
   rw 0 (q43 c4) ∷
   rw 1 (q44 c4) ∷
   rw 2 (q45 c4) ∷
   rw 3 (q44 c4) ∷
   rw 4 (q43 c4) ∷
   rw 5 (q45 c4) ∷
   re 0 6 (Bx4-203 ∷ []) ∷ []) Eq.refl

private
  q46 : WsL → Eqn
  q46 c4 = eqn (CCZ124 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ124 ∷ []) (wl0078 c4)
  q47 : WsL → Eqn
  q47 c4 = eqn (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) (wl0095 c4)
  q48 : WsL → Eqn
  q48 c4 = eqn (Sw12 ∷ Bx4-103 ∷ []) (Bx4-203 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·103⟩ c4)

-- nat 1 BOX(1;4203): 8 steps
lem-nat-1-BOX⟨1·4203⟩ : WsL → ⟪ (Sw12 ∷ Bx1-4203 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·4203⟩ c4 = derive (Sw12 ∷ Bx1-4203 ∷ []) (Bx2-4103 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-103 ∷ Toff124 ∷ CCZ124 ∷ Bx4-103 ∷ []) ∷
   rw⁻ 0 (q46 c4) ∷
   rw 1 (q47 c4) ∷
   rw 2 (q48 c4) ∷
   rw 3 (q47 c4) ∷
   rw⁻ 4 (q46 c4) ∷
   rw 5 (q48 c4) ∷
   re 0 6 (Bx2-4103 ∷ []) ∷ []) Eq.refl

-- nat 2 TOFF214: 2 steps
lem-nat-2-TOFF214 : WsL → ⟪ (Sw23 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF214 c4 = derive (Sw23 ∷ Toff214 ∷ []) (Toff314 ∷ Sw23 ∷ [])
  (rw⁻ 2 (q2 c4) ∷
   re 0 3 (Toff314 ∷ []) ∷ []) Eq.refl

-- nat 2 TOFF402: 2 steps
lem-nat-2-TOFF402 : WsL → ⟪ (Sw23 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF402 c4 = derive (Sw23 ∷ Toff402 ∷ []) (Toff403 ∷ Sw23 ∷ [])
  (rw⁻ 2 (q2 c4) ∷
   re 0 3 (Toff403 ∷ []) ∷ []) Eq.refl

private
  q49 : WsL → Eqn
  q49 c4 = eqn (Sw23 ∷ CCZ024 ∷ []) (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4)
  q50 : WsL → Eqn
  q50 c4 = eqn (Sw23 ∷ Toff402 ∷ []) (Toff403 ∷ Sw23 ∷ []) (lem-nat-2-TOFF402 c4)
  q51 : WsL → Eqn
  q51 c4 = eqn (Sw23 ∷ Bx2-43 ∷ []) (Bx3-42 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·43⟩ c4)

-- nat 2 BOX(4;203): 8 steps
lem-nat-2-BOX⟨4·203⟩ : WsL → ⟪ (Sw23 ∷ Bx4-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-302 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·203⟩ c4 = derive (Sw23 ∷ Bx4-203 ∷ []) (Bx4-302 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) ∷
   rw 0 (q49 c4) ∷
   rw 1 (q50 c4) ∷
   rw 2 (q51 c4) ∷
   rw 3 (q50 c4) ∷
   rw 4 (q49 c4) ∷
   rw 5 (q51 c4) ∷
   re 0 6 (Bx4-302 ∷ []) ∷ []) Eq.refl

private
  q52 : WsL → Eqn
  q52 c4 = eqn (Sw23 ∷ CCZ124 ∷ []) (CCZ134 ∷ Sw23 ∷ []) (lem-nat-2-CCZ124 c4)
  q53 : WsL → Eqn
  q53 c4 = eqn (Sw23 ∷ Toff214 ∷ []) (Toff314 ∷ Sw23 ∷ []) (lem-nat-2-TOFF214 c4)
  q54 : WsL → Eqn
  q54 c4 = eqn (Sw23 ∷ Bx4-203 ∷ []) (Bx4-302 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·203⟩ c4)

-- nat 2 BOX(2;4103): 8 steps
lem-nat-2-BOX⟨2·4103⟩ : WsL → ⟪ (Sw23 ∷ Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·4103⟩ c4 = derive (Sw23 ∷ Bx2-4103 ∷ []) (Bx3-4102 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff214 ∷ Bx4-203 ∷ Toff214 ∷ CCZ124 ∷ Bx4-203 ∷ []) ∷
   rw 0 (q52 c4) ∷
   rw 1 (q53 c4) ∷
   rw 2 (q54 c4) ∷
   rw 3 (q53 c4) ∷
   rw 4 (q52 c4) ∷
   rw 5 (q54 c4) ∷
   re 0 6 (Bx3-4102 ∷ []) ∷ []) Eq.refl

private
  q55 : WsL → Eqn
  q55 c4 = eqn (CZ03 ∷ Sw01 ∷ []) (Sw01 ∷ CZ13 ∷ []) (wl0088 c4)

-- nat 0 BOX(0;13): 3 steps
lem-nat-0-BOX⟨0·13⟩ : WsL → ⟪ (Sw01 ∷ Bx0-13 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-03 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·13⟩ c4 = derive (Sw01 ∷ Bx0-13 ∷ []) (Bx1-03 ∷ Sw01 ∷ [])
  (re 1 1 (CZ13 ∷ []) ∷
   rw⁻ 0 (q55 c4) ∷
   re 0 1 (Bx1-03 ∷ []) ∷ []) Eq.refl

private
  q56 : WsL → Eqn
  q56 c4 = eqn (CCZ012 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ012 ∷ []) (wl0096 c4)
  q57 : WsL → Eqn
  q57 c4 = eqn (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) (wl0097 c4)
  q58 : WsL → Eqn
  q58 c4 = eqn (Sw01 ∷ Bx0-13 ∷ []) (Bx1-03 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·13⟩ c4)

-- nat 0 BOX(1;023): 8 steps
lem-nat-0-BOX⟨1·023⟩ : WsL → ⟪ (Sw01 ∷ Bx1-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-123 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·023⟩ c4 = derive (Sw01 ∷ Bx1-023 ∷ []) (Bx0-123 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) ∷
   rw⁻ 0 (q56 c4) ∷
   rw 1 (q57 c4) ∷
   rw 2 (q58 c4) ∷
   rw 3 (q57 c4) ∷
   rw⁻ 4 (q56 c4) ∷
   rw 5 (q58 c4) ∷
   re 0 6 (Bx0-123 ∷ []) ∷ []) Eq.refl

private
  q59 : WsL → Eqn
  q59 c4 = eqn (Sw01 ∷ Toff014 ∷ []) (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4)
  q60 : WsL → Eqn
  q60 c4 = eqn (Sw01 ∷ Bx1-023 ∷ []) (Bx0-123 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·023⟩ c4)

-- nat 0 BOX(0;1423): 8 steps
lem-nat-0-BOX⟨0·1423⟩ : WsL → ⟪ (Sw01 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·1423⟩ c4 = derive (Sw01 ∷ Bx0-1423 ∷ []) (Bx1-0423 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) ∷
   rw 0 (q37 c4) ∷
   rw 1 (q59 c4) ∷
   rw 2 (q60 c4) ∷
   rw 3 (q59 c4) ∷
   rw 4 (q37 c4) ∷
   rw 5 (q60 c4) ∷
   re 0 6 (Bx1-0423 ∷ []) ∷ []) Eq.refl

private
  q61 : WsL → Eqn
  q61 c4 = eqn (CZ03 ∷ Sw12 ∷ []) (Sw12 ∷ CZ03 ∷ []) (wl0098 c4)

-- nat 1 BOX(1;03): 3 steps
lem-nat-1-BOX⟨1·03⟩ : WsL → ⟪ (Sw12 ∷ Bx1-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-03 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·03⟩ c4 = derive (Sw12 ∷ Bx1-03 ∷ []) (Bx2-03 ∷ Sw12 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw⁻ 0 (q61 c4) ∷
   re 0 1 (Bx2-03 ∷ []) ∷ []) Eq.refl

private
  q62 : WsL → Eqn
  q62 c4 = eqn (CCZ012 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ012 ∷ []) (wl0037 c4)
  q63 : WsL → Eqn
  q63 c4 = eqn (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) (wl0038 c4)
  q64 : WsL → Eqn
  q64 c4 = eqn (Sw12 ∷ Bx1-03 ∷ []) (Bx2-03 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·03⟩ c4)

-- nat 1 BOX(0;123): 8 steps
lem-nat-1-BOX⟨0·123⟩ : WsL → ⟪ (Sw12 ∷ Bx0-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-213 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·123⟩ c4 = derive (Sw12 ∷ Bx0-123 ∷ []) (Bx0-213 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-03 ∷ Toff012 ∷ CCZ012 ∷ Bx1-03 ∷ []) ∷
   rw⁻ 0 (q62 c4) ∷
   rw 1 (q63 c4) ∷
   rw 2 (q64 c4) ∷
   rw 3 (q63 c4) ∷
   rw⁻ 4 (q62 c4) ∷
   rw 5 (q64 c4) ∷
   re 0 6 (Bx0-213 ∷ []) ∷ []) Eq.refl

private
  q65 : WsL → Eqn
  q65 c4 = eqn (Sw12 ∷ Toff104 ∷ []) (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4)
  q66 : WsL → Eqn
  q66 c4 = eqn (Sw12 ∷ Bx0-123 ∷ []) (Bx0-213 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·123⟩ c4)

-- nat 1 BOX(1;0423): 8 steps
lem-nat-1-BOX⟨1·0423⟩ : WsL → ⟪ (Sw12 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·0423⟩ c4 = derive (Sw12 ∷ Bx1-0423 ∷ []) (Bx2-0413 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-123 ∷ Toff104 ∷ CCZ014 ∷ Bx0-123 ∷ []) ∷
   rw 0 (q43 c4) ∷
   rw 1 (q65 c4) ∷
   rw 2 (q66 c4) ∷
   rw 3 (q65 c4) ∷
   rw 4 (q43 c4) ∷
   rw 5 (q66 c4) ∷
   re 0 6 (Bx2-0413 ∷ []) ∷ []) Eq.refl

-- nat 2 CZ03: 2 steps
lem-nat-2-CZ03 : WsL → ⟪ (Sw23 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CZ03 c4 = derive (Sw23 ∷ CZ03 ∷ []) (CZ02 ∷ Sw23 ∷ [])
  (re 1 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ∷
   rw 0 (q2 c4) ∷ []) Eq.refl

private
  q67 : WsL → Eqn
  q67 c4 = eqn (Sw23 ∷ CZ03 ∷ []) (CZ02 ∷ Sw23 ∷ []) (lem-nat-2-CZ03 c4)

-- nat 2 BOX(2;03): 3 steps
lem-nat-2-BOX⟨2·03⟩ : WsL → ⟪ (Sw23 ∷ Bx2-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-02 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·03⟩ c4 = derive (Sw23 ∷ Bx2-03 ∷ []) (Bx3-02 ∷ Sw23 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw 0 (q67 c4) ∷
   re 0 1 (Bx3-02 ∷ []) ∷ []) Eq.refl

private
  q68 : WsL → Eqn
  q68 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4)
  q69 : WsL → Eqn
  q69 c4 = eqn (Sw23 ∷ Toff012 ∷ []) (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4)
  q70 : WsL → Eqn
  q70 c4 = eqn (Sw23 ∷ Bx2-03 ∷ []) (Bx3-02 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·03⟩ c4)

-- nat 2 BOX(0;213): 8 steps
lem-nat-2-BOX⟨0·213⟩ : WsL → ⟪ (Sw23 ∷ Bx0-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-312 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·213⟩ c4 = derive (Sw23 ∷ Bx0-213 ∷ []) (Bx0-312 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   rw 0 (q68 c4) ∷
   rw 1 (q69 c4) ∷
   rw 2 (q70 c4) ∷
   rw 3 (q69 c4) ∷
   rw 4 (q68 c4) ∷
   rw 5 (q70 c4) ∷
   re 0 6 (Bx0-312 ∷ []) ∷ []) Eq.refl

private
  q71 : WsL → Eqn
  q71 c4 = eqn (Sw23 ∷ Toff204 ∷ []) (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4)
  q72 : WsL → Eqn
  q72 c4 = eqn (Sw23 ∷ Bx0-213 ∷ []) (Bx0-312 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·213⟩ c4)

-- nat 2 BOX(2;0413): 8 steps
lem-nat-2-BOX⟨2·0413⟩ : WsL → ⟪ (Sw23 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·0413⟩ c4 = derive (Sw23 ∷ Bx2-0413 ∷ []) (Bx3-0412 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) ∷
   rw 0 (q49 c4) ∷
   rw 1 (q71 c4) ∷
   rw 2 (q72 c4) ∷
   rw 3 (q71 c4) ∷
   rw 4 (q49 c4) ∷
   rw 5 (q72 c4) ∷
   re 0 6 (Bx3-0412 ∷ []) ∷ []) Eq.refl

private
  q73 : WsL → Eqn
  q73 c4 = eqn (CZ13 ∷ Sw01 ∷ []) (Sw01 ∷ CZ03 ∷ []) (wl0092 c4)

-- nat 0 BOX(1;03): 3 steps
lem-nat-0-BOX⟨1·03⟩ : WsL → ⟪ (Sw01 ∷ Bx1-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-13 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·03⟩ c4 = derive (Sw01 ∷ Bx1-03 ∷ []) (Bx0-13 ∷ Sw01 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw⁻ 0 (q73 c4) ∷
   re 0 1 (Bx0-13 ∷ []) ∷ []) Eq.refl

private
  q74 : WsL → Eqn
  q74 c4 = eqn (Sw01 ∷ Toff012 ∷ []) (Toff102 ∷ Sw01 ∷ []) (wl0099 c4)
  q75 : WsL → Eqn
  q75 c4 = eqn (Sw01 ∷ Bx1-03 ∷ []) (Bx0-13 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·03⟩ c4)

-- nat 0 BOX(0;123): 8 steps
lem-nat-0-BOX⟨0·123⟩ : WsL → ⟪ (Sw01 ∷ Bx0-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-023 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·123⟩ c4 = derive (Sw01 ∷ Bx0-123 ∷ []) (Bx1-023 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-03 ∷ Toff012 ∷ CCZ012 ∷ Bx1-03 ∷ []) ∷
   rw⁻ 0 (q56 c4) ∷
   rw 1 (q74 c4) ∷
   rw 2 (q75 c4) ∷
   rw 3 (q74 c4) ∷
   rw⁻ 4 (q56 c4) ∷
   rw 5 (q75 c4) ∷
   re 0 6 (Bx1-023 ∷ []) ∷ []) Eq.refl

private
  q76 : WsL → Eqn
  q76 c4 = eqn (Sw01 ∷ Toff104 ∷ []) (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4)
  q77 : WsL → Eqn
  q77 c4 = eqn (Sw01 ∷ Bx0-123 ∷ []) (Bx1-023 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·123⟩ c4)

-- nat 0 BOX(1;0423): 8 steps
lem-nat-0-BOX⟨1·0423⟩ : WsL → ⟪ (Sw01 ∷ Bx1-0423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·0423⟩ c4 = derive (Sw01 ∷ Bx1-0423 ∷ []) (Bx0-1423 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-123 ∷ Toff104 ∷ CCZ014 ∷ Bx0-123 ∷ []) ∷
   rw 0 (q37 c4) ∷
   rw 1 (q76 c4) ∷
   rw 2 (q77 c4) ∷
   rw 3 (q76 c4) ∷
   rw 4 (q37 c4) ∷
   rw 5 (q77 c4) ∷
   re 0 6 (Bx0-1423 ∷ []) ∷ []) Eq.refl

-- nat 1 BOX(2;03): 3 steps
lem-nat-1-BOX⟨2·03⟩ : WsL → ⟪ (Sw12 ∷ Bx2-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-03 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·03⟩ c4 = derive (Sw12 ∷ Bx2-03 ∷ []) (Bx1-03 ∷ Sw12 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw⁻ 0 (q61 c4) ∷
   re 0 1 (Bx1-03 ∷ []) ∷ []) Eq.refl

private
  q78 : WsL → Eqn
  q78 c4 = eqn (Sw12 ∷ Bx2-03 ∷ []) (Bx1-03 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·03⟩ c4)

-- nat 1 BOX(0;213): 8 steps
lem-nat-1-BOX⟨0·213⟩ : WsL → ⟪ (Sw12 ∷ Bx0-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-123 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·213⟩ c4 = derive (Sw12 ∷ Bx0-213 ∷ []) (Bx0-123 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   rw⁻ 0 (q62 c4) ∷
   rw 1 (q63 c4) ∷
   rw 2 (q78 c4) ∷
   rw 3 (q63 c4) ∷
   rw⁻ 4 (q62 c4) ∷
   rw 5 (q78 c4) ∷
   re 0 6 (Bx0-123 ∷ []) ∷ []) Eq.refl

private
  q79 : WsL → Eqn
  q79 c4 = eqn (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4)
  q80 : WsL → Eqn
  q80 c4 = eqn (Sw12 ∷ Toff204 ∷ []) (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4)
  q81 : WsL → Eqn
  q81 c4 = eqn (Sw12 ∷ Bx0-213 ∷ []) (Bx0-123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·213⟩ c4)

-- nat 1 BOX(2;0413): 8 steps
lem-nat-1-BOX⟨2·0413⟩ : WsL → ⟪ (Sw12 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0423 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·0413⟩ c4 = derive (Sw12 ∷ Bx2-0413 ∷ []) (Bx1-0423 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) ∷
   rw 0 (q79 c4) ∷
   rw 1 (q80 c4) ∷
   rw 2 (q81 c4) ∷
   rw 3 (q80 c4) ∷
   rw 4 (q79 c4) ∷
   rw 5 (q81 c4) ∷
   re 0 6 (Bx1-0423 ∷ []) ∷ []) Eq.refl

-- nat 2 CZ02: 2 steps
lem-nat-2-CZ02 : WsL → ⟪ (Sw23 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CZ02 c4 = derive (Sw23 ∷ CZ02 ∷ []) (CZ03 ∷ Sw23 ∷ [])
  (rw⁻ 2 (q2 c4) ∷
   re 0 3 (CZ03 ∷ []) ∷ []) Eq.refl

private
  q82 : WsL → Eqn
  q82 c4 = eqn (Sw23 ∷ CZ02 ∷ []) (CZ03 ∷ Sw23 ∷ []) (lem-nat-2-CZ02 c4)

-- nat 2 BOX(3;02): 3 steps
lem-nat-2-BOX⟨3·02⟩ : WsL → ⟪ (Sw23 ∷ Bx3-02 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-03 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·02⟩ c4 = derive (Sw23 ∷ Bx3-02 ∷ []) (Bx2-03 ∷ Sw23 ∷ [])
  (re 1 1 (CZ02 ∷ []) ∷
   rw 0 (q82 c4) ∷
   re 0 1 (Bx2-03 ∷ []) ∷ []) Eq.refl

private
  q83 : WsL → Eqn
  q83 c4 = eqn (Sw23 ∷ CCZ013 ∷ []) (CCZ012 ∷ Sw23 ∷ []) (lem-nat-2-CCZ013 c4)
  q84 : WsL → Eqn
  q84 c4 = eqn (Sw23 ∷ Toff013 ∷ []) (Toff012 ∷ Sw23 ∷ []) (lem-nat-2-TOFF013 c4)
  q85 : WsL → Eqn
  q85 c4 = eqn (Sw23 ∷ Bx3-02 ∷ []) (Bx2-03 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·02⟩ c4)

-- nat 2 BOX(0;312): 8 steps
lem-nat-2-BOX⟨0·312⟩ : WsL → ⟪ (Sw23 ∷ Bx0-312 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-213 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·312⟩ c4 = derive (Sw23 ∷ Bx0-312 ∷ []) (Bx0-213 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ []) ∷
   rw 0 (q83 c4) ∷
   rw 1 (q84 c4) ∷
   rw 2 (q85 c4) ∷
   rw 3 (q84 c4) ∷
   rw 4 (q83 c4) ∷
   rw 5 (q85 c4) ∷
   re 0 6 (Bx0-213 ∷ []) ∷ []) Eq.refl

private
  q86 : WsL → Eqn
  q86 c4 = eqn (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4)
  q87 : WsL → Eqn
  q87 c4 = eqn (Sw23 ∷ Toff304 ∷ []) (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4)
  q88 : WsL → Eqn
  q88 c4 = eqn (Sw23 ∷ Bx0-312 ∷ []) (Bx0-213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·312⟩ c4)

-- nat 2 BOX(3;0412): 8 steps
lem-nat-2-BOX⟨3·0412⟩ : WsL → ⟪ (Sw23 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·0412⟩ c4 = derive (Sw23 ∷ Bx3-0412 ∷ []) (Bx2-0413 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ []) ∷
   rw 0 (q86 c4) ∷
   rw 1 (q87 c4) ∷
   rw 2 (q88 c4) ∷
   rw 3 (q87 c4) ∷
   rw 4 (q86 c4) ∷
   rw 5 (q88 c4) ∷
   re 0 6 (Bx2-0413 ∷ []) ∷ []) Eq.refl

private
  q89 : WsL → Eqn
  q89 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 c4)
  q90 : WsL → Eqn
  q90 c4 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wl0048 c4)

-- resp CCZ014 at 2: 58 steps
lem-resp-CCZ014-at-2 : WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CCZ124 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CCZ014-at-2 c4 = derive (CCZ014 ∷ []) (Sw12 ∷ Sw01 ∷ CCZ124 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q11 c4) ∷
   rw⁻ 0 (q11 c4) ∷
   re 1 3 (CCZ024 ∷ []) ∷
   rw⁻ 2 (q89 c4) ∷
   re 1 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 (q3 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q3 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 (q2 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (CS14 ∷ []) ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CS14⁻ ∷ []) ∷
   rw⁻ 5 (q7 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw 7 (q6 c4) ∷
   rw⁻ 1 (q10 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   re 2 3 (CX02 ∷ []) ∷
   rw⁻ 3 (q12 c4) ∷
   rw⁻ 6 (q11 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q13 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw 7 (q13 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw 6 (q11 c4) ∷
   re 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 7 (q20 c4) ∷
   rw 6 (q29 c4) ∷
   rw⁻ 5 (q20 c4) ∷
   re 6 3 (CS14 ∷ []) ∷
   rw 4 (q90 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw 2 (q90 c4) ∷
   rw⁻ 1 (q17 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   re 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q24 c4) ∷
   re 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q24 c4) ∷
   re 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 7 (q6 c4) ∷
   re 3 5 (CCZ123 ∷ []) ∷
   re 2 3 (CCZ124 ∷ []) ∷ []) Eq.refl

private
  q91 : WsL → Eqn
  q91 c4 = eqn (Sw01 ∷ Toff402 ∷ []) (Toff412 ∷ Sw01 ∷ []) (lem-nat-0-TOFF402 c4)
  q92 : WsL → Eqn
  q92 c4 = eqn (Sw01 ∷ Bx2-43 ∷ []) (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑))

-- nat 0 BOX(4;203): 8 steps
lem-nat-0-BOX⟨4·203⟩ : WsL → ⟪ (Sw01 ∷ Bx4-203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-213 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·203⟩ c4 = derive (Sw01 ∷ Bx4-203 ∷ []) (Bx4-213 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) ∷
   rw 0 (q40 c4) ∷
   rw 1 (q91 c4) ∷
   rw 2 (q92 c4) ∷
   rw 3 (q91 c4) ∷
   rw 4 (q40 c4) ∷
   rw 5 (q92 c4) ∷
   re 0 6 (Bx4-213 ∷ []) ∷ []) Eq.refl

private
  q93 : WsL → Eqn
  q93 c4 = eqn (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4)
  q94 : WsL → Eqn
  q94 c4 = eqn (Sw01 ∷ Toff214 ∷ []) (Toff204 ∷ Sw01 ∷ []) (lem-nat-0-TOFF214 c4)
  q95 : WsL → Eqn
  q95 c4 = eqn (Sw01 ∷ Bx4-203 ∷ []) (Bx4-213 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·203⟩ c4)

-- nat 0 BOX(2;4103): 8 steps
lem-nat-0-BOX⟨2·4103⟩ : WsL → ⟪ (Sw01 ∷ Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·4103⟩ c4 = derive (Sw01 ∷ Bx2-4103 ∷ []) (Bx2-4013 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff214 ∷ Bx4-203 ∷ Toff214 ∷ CCZ124 ∷ Bx4-203 ∷ []) ∷
   rw 0 (q93 c4) ∷
   rw 1 (q94 c4) ∷
   rw 2 (q95 c4) ∷
   rw 3 (q94 c4) ∷
   rw 4 (q93 c4) ∷
   rw 5 (q95 c4) ∷
   re 0 6 (Bx2-4013 ∷ []) ∷ []) Eq.refl

private
  q96 : WsL → Eqn
  q96 c4 = eqn (Sw01 ∷ CZ04 ∷ []) (CZ14 ∷ Sw01 ∷ []) (lem-nat-0-CZ04 c4)

-- nat 0 BOX(1;04): 3 steps
lem-nat-0-BOX⟨1·04⟩ : WsL → ⟪ (Sw01 ∷ Bx1-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-14 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·04⟩ c4 = derive (Sw01 ∷ Bx1-04 ∷ []) (Bx0-14 ∷ Sw01 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   rw 0 (q96 c4) ∷
   re 0 1 (Bx0-14 ∷ []) ∷ []) Eq.refl

private
  q97 : WsL → Eqn
  q97 c4 = eqn (CCZ013 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ013 ∷ []) (wl0100 c4)
  q98 : WsL → Eqn
  q98 c4 = eqn (Sw01 ∷ Toff013 ∷ []) (Toff103 ∷ Sw01 ∷ []) (wl0101 c4)
  q99 : WsL → Eqn
  q99 c4 = eqn (Sw01 ∷ Bx1-04 ∷ []) (Bx0-14 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·04⟩ c4)

-- nat 0 BOX(0;134): 8 steps
lem-nat-0-BOX⟨0·134⟩ : WsL → ⟪ (Sw01 ∷ Bx0-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-034 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·134⟩ c4 = derive (Sw01 ∷ Bx0-134 ∷ []) (Bx1-034 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-04 ∷ Toff013 ∷ CCZ013 ∷ Bx1-04 ∷ []) ∷
   rw⁻ 0 (q97 c4) ∷
   rw 1 (q98 c4) ∷
   rw 2 (q99 c4) ∷
   rw 3 (q98 c4) ∷
   rw⁻ 4 (q97 c4) ∷
   rw 5 (q99 c4) ∷
   re 0 6 (Bx1-034 ∷ []) ∷ []) Eq.refl

private
  q100 : WsL → Eqn
  q100 c4 = eqn (Sw01 ∷ Bx0-134 ∷ []) (Bx1-034 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·134⟩ c4)

-- nat 0 BOX(1;0234): 8 steps
lem-nat-0-BOX⟨1·0234⟩ : WsL → ⟪ (Sw01 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·0234⟩ c4 = derive (Sw01 ∷ Bx1-0234 ∷ []) (Bx0-1234 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-134 ∷ Toff102 ∷ CCZ012 ∷ Bx0-134 ∷ []) ∷
   rw⁻ 0 (q56 c4) ∷
   rw 1 (q57 c4) ∷
   rw 2 (q100 c4) ∷
   rw 3 (q57 c4) ∷
   rw⁻ 4 (q56 c4) ∷
   rw 5 (q100 c4) ∷
   re 0 6 (Bx0-1234 ∷ []) ∷ []) Eq.refl

-- nat 0 BOX(1;043): 8 steps
lem-nat-0-BOX⟨1·043⟩ : WsL → ⟪ (Sw01 ∷ Bx1-043 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-143 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·043⟩ c4 = derive (Sw01 ∷ Bx1-043 ∷ []) (Bx0-143 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ []) ∷
   rw 0 (q37 c4) ∷
   rw 1 (q76 c4) ∷
   rw 2 (q58 c4) ∷
   rw 3 (q76 c4) ∷
   rw 4 (q37 c4) ∷
   rw 5 (q58 c4) ∷
   re 0 6 (Bx0-143 ∷ []) ∷ []) Eq.refl

private
  q101 : WsL → Eqn
  q101 c4 = eqn (Sw01 ∷ Bx1-043 ∷ []) (Bx0-143 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·043⟩ c4)

-- nat 0 BOX(0;1243): 8 steps
lem-nat-0-BOX⟨0·1243⟩ : WsL → ⟪ (Sw01 ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·1243⟩ c4 = derive (Sw01 ∷ Bx0-1243 ∷ []) (Bx1-0243 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-043 ∷ Toff012 ∷ CCZ012 ∷ Bx1-043 ∷ []) ∷
   rw⁻ 0 (q56 c4) ∷
   rw 1 (q74 c4) ∷
   rw 2 (q101 c4) ∷
   rw 3 (q74 c4) ∷
   rw⁻ 4 (q56 c4) ∷
   rw 5 (q101 c4) ∷
   re 0 6 (Bx1-0243 ∷ []) ∷ []) Eq.refl

-- nat 1 TOFF023: 2 steps
lem-nat-1-TOFF023 : WsL → ⟪ (Sw12 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF023 c4 = derive (Sw12 ∷ Toff023 ∷ []) (Toff013 ∷ Sw12 ∷ [])
  (re 1 1 (Sw12 ∷ Toff013 ∷ Sw12 ∷ []) ∷
   rw 0 (q11 c4) ∷ []) Eq.refl

-- nat 1 CZ04: 5 steps
lem-nat-1-CZ04 : WsL → ⟪ (Sw12 ∷ CZ04 ∷ []) ⟫ʷ ≈ ⟪ (CZ04 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-CZ04 c4 = derive (Sw12 ∷ CZ04 ∷ []) (CZ04 ∷ Sw12 ∷ [])
  (re 1 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) ∷
   rw 0 (q13 c4) ∷
   rw⁻ 1 (q61 c4) ∷
   rw 2 (q13 c4) ∷
   re 0 3 (CZ04 ∷ []) ∷ []) Eq.refl

private
  q102 : WsL → Eqn
  q102 c4 = eqn (Sw12 ∷ CZ04 ∷ []) (CZ04 ∷ Sw12 ∷ []) (lem-nat-1-CZ04 c4)

-- nat 1 BOX(2;04): 3 steps
lem-nat-1-BOX⟨2·04⟩ : WsL → ⟪ (Sw12 ∷ Bx2-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-04 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·04⟩ c4 = derive (Sw12 ∷ Bx2-04 ∷ []) (Bx1-04 ∷ Sw12 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   rw 0 (q102 c4) ∷
   re 0 1 (Bx1-04 ∷ []) ∷ []) Eq.refl

private
  q103 : WsL → Eqn
  q103 c4 = eqn (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4)
  q104 : WsL → Eqn
  q104 c4 = eqn (Sw12 ∷ Toff023 ∷ []) (Toff013 ∷ Sw12 ∷ []) (lem-nat-1-TOFF023 c4)
  q105 : WsL → Eqn
  q105 c4 = eqn (Sw12 ∷ Bx2-04 ∷ []) (Bx1-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·04⟩ c4)

-- nat 1 BOX(0;234): 8 steps
lem-nat-1-BOX⟨0·234⟩ : WsL → ⟪ (Sw12 ∷ Bx0-234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-134 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·234⟩ c4 = derive (Sw12 ∷ Bx0-234 ∷ []) (Bx0-134 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) ∷
   rw 0 (q103 c4) ∷
   rw 1 (q104 c4) ∷
   rw 2 (q105 c4) ∷
   rw 3 (q104 c4) ∷
   rw 4 (q103 c4) ∷
   rw 5 (q105 c4) ∷
   re 0 6 (Bx0-134 ∷ []) ∷ []) Eq.refl

private
  q106 : WsL → Eqn
  q106 c4 = eqn (Sw12 ∷ Toff201 ∷ []) (Toff102 ∷ Sw12 ∷ []) (wl0044 c4)
  q107 : WsL → Eqn
  q107 c4 = eqn (Sw12 ∷ Bx0-234 ∷ []) (Bx0-134 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·234⟩ c4)

-- nat 1 BOX(2;0134): 8 steps
lem-nat-1-BOX⟨2·0134⟩ : WsL → ⟪ (Sw12 ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·0134⟩ c4 = derive (Sw12 ∷ Bx2-0134 ∷ []) (Bx1-0234 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ []) ∷
   rw⁻ 0 (q62 c4) ∷
   rw 1 (q106 c4) ∷
   rw 2 (q107 c4) ∷
   rw 3 (q106 c4) ∷
   rw⁻ 4 (q62 c4) ∷
   rw 5 (q107 c4) ∷
   re 0 6 (Bx1-0234 ∷ []) ∷ []) Eq.refl

private
  q108 : WsL → Eqn
  q108 c4 = eqn (Sw12 ∷ Toff014 ∷ []) (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4)

-- nat 1 BOX(0;143): 8 steps
lem-nat-1-BOX⟨0·143⟩ : WsL → ⟪ (Sw12 ∷ Bx0-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-243 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·143⟩ c4 = derive (Sw12 ∷ Bx0-143 ∷ []) (Bx0-243 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-03 ∷ Toff014 ∷ CCZ014 ∷ Bx1-03 ∷ []) ∷
   rw 0 (q43 c4) ∷
   rw 1 (q108 c4) ∷
   rw 2 (q64 c4) ∷
   rw 3 (q108 c4) ∷
   rw 4 (q43 c4) ∷
   rw 5 (q64 c4) ∷
   re 0 6 (Bx0-243 ∷ []) ∷ []) Eq.refl

private
  q109 : WsL → Eqn
  q109 c4 = eqn (Sw12 ∷ Toff102 ∷ []) (Toff201 ∷ Sw12 ∷ []) (wl0047 c4)
  q110 : WsL → Eqn
  q110 c4 = eqn (Sw12 ∷ Bx0-143 ∷ []) (Bx0-243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·143⟩ c4)

-- nat 1 BOX(1;0243): 8 steps
lem-nat-1-BOX⟨1·0243⟩ : WsL → ⟪ (Sw12 ∷ Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·0243⟩ c4 = derive (Sw12 ∷ Bx1-0243 ∷ []) (Bx2-0143 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-143 ∷ Toff102 ∷ CCZ012 ∷ Bx0-143 ∷ []) ∷
   rw⁻ 0 (q62 c4) ∷
   rw 1 (q109 c4) ∷
   rw 2 (q110 c4) ∷
   rw 3 (q109 c4) ∷
   rw⁻ 4 (q62 c4) ∷
   rw 5 (q110 c4) ∷
   re 0 6 (Bx2-0143 ∷ []) ∷ []) Eq.refl

private
  q111 : WsL → Eqn
  q111 c4 = eqn (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4)
  q112 : WsL → Eqn
  q112 c4 = eqn (CZ01 ∷ Sw34 ∷ []) (Sw34 ∷ CZ01 ∷ []) (c₂ (CZ) (Swap ↑))

-- nat 2 CZ04: 7 steps
lem-nat-2-CZ04 : WsL → ⟪ (Sw23 ∷ CZ04 ∷ []) ⟫ʷ ≈ ⟪ (CZ04 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CZ04 c4 = derive (Sw23 ∷ CZ04 ∷ []) (CZ04 ∷ Sw23 ∷ [])
  (re 1 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 0 (q111 c4) ∷
   rw⁻ 2 (q13 c4) ∷
   rw⁻ 3 (q112 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw⁻ 5 (q111 c4) ∷
   re 0 7 (CZ04 ∷ []) ∷ []) Eq.refl

private
  q113 : WsL → Eqn
  q113 c4 = eqn (Sw23 ∷ CZ04 ∷ []) (CZ04 ∷ Sw23 ∷ []) (lem-nat-2-CZ04 c4)

-- nat 2 BOX(3;04): 3 steps
lem-nat-2-BOX⟨3·04⟩ : WsL → ⟪ (Sw23 ∷ Bx3-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-04 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·04⟩ c4 = derive (Sw23 ∷ Bx3-04 ∷ []) (Bx2-04 ∷ Sw23 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   rw 0 (q113 c4) ∷
   re 0 1 (Bx2-04 ∷ []) ∷ []) Eq.refl

private
  q114 : WsL → Eqn
  q114 c4 = eqn (CCZ023 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ023 ∷ []) (wl0065 c4)
  q115 : WsL → Eqn
  q115 c4 = eqn (Sw23 ∷ Toff023 ∷ []) (Toff023 ∷ Sw23 ∷ []) (wl0093 c4)
  q116 : WsL → Eqn
  q116 c4 = eqn (Sw23 ∷ Bx3-04 ∷ []) (Bx2-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·04⟩ c4)

-- nat 2 BOX(0;324): 8 steps
lem-nat-2-BOX⟨0·324⟩ : WsL → ⟪ (Sw23 ∷ Bx0-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-234 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·324⟩ c4 = derive (Sw23 ∷ Bx0-324 ∷ []) (Bx0-234 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) ∷
   rw⁻ 0 (q114 c4) ∷
   rw 1 (q115 c4) ∷
   rw 2 (q116 c4) ∷
   rw 3 (q115 c4) ∷
   rw⁻ 4 (q114 c4) ∷
   rw 5 (q116 c4) ∷
   re 0 6 (Bx0-234 ∷ []) ∷ []) Eq.refl

private
  q117 : WsL → Eqn
  q117 c4 = eqn (Sw23 ∷ Toff301 ∷ []) (Toff201 ∷ Sw23 ∷ []) (lem-nat-2-TOFF301 c4)
  q118 : WsL → Eqn
  q118 c4 = eqn (Sw23 ∷ Bx0-324 ∷ []) (Bx0-234 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·324⟩ c4)

-- nat 2 BOX(3;0124): 8 steps
lem-nat-2-BOX⟨3·0124⟩ : WsL → ⟪ (Sw23 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·0124⟩ c4 = derive (Sw23 ∷ Bx3-0124 ∷ []) (Bx2-0134 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) ∷
   rw 0 (q83 c4) ∷
   rw 1 (q117 c4) ∷
   rw 2 (q118 c4) ∷
   rw 3 (q117 c4) ∷
   rw 4 (q83 c4) ∷
   rw 5 (q118 c4) ∷
   re 0 6 (Bx2-0134 ∷ []) ∷ []) Eq.refl

private
  q119 : WsL → Eqn
  q119 c4 = eqn (Sw23 ∷ Toff024 ∷ []) (Toff034 ∷ Sw23 ∷ []) (lem-nat-2-TOFF024 c4)

-- nat 2 BOX(0;243): 8 steps
lem-nat-2-BOX⟨0·243⟩ : WsL → ⟪ (Sw23 ∷ Bx0-243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-342 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·243⟩ c4 = derive (Sw23 ∷ Bx0-243 ∷ []) (Bx0-342 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) ∷
   rw 0 (q49 c4) ∷
   rw 1 (q119 c4) ∷
   rw 2 (q70 c4) ∷
   rw 3 (q119 c4) ∷
   rw 4 (q49 c4) ∷
   rw 5 (q70 c4) ∷
   re 0 6 (Bx0-342 ∷ []) ∷ []) Eq.refl

private
  q120 : WsL → Eqn
  q120 c4 = eqn (Sw23 ∷ Toff201 ∷ []) (Toff301 ∷ Sw23 ∷ []) (lem-nat-2-TOFF201 c4)
  q121 : WsL → Eqn
  q121 c4 = eqn (Sw23 ∷ Bx0-243 ∷ []) (Bx0-342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·243⟩ c4)

-- nat 2 BOX(2;0143): 8 steps
lem-nat-2-BOX⟨2·0143⟩ : WsL → ⟪ (Sw23 ∷ Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·0143⟩ c4 = derive (Sw23 ∷ Bx2-0143 ∷ []) (Bx3-0142 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ []) ∷
   rw 0 (q68 c4) ∷
   rw 1 (q120 c4) ∷
   rw 2 (q121 c4) ∷
   rw 3 (q120 c4) ∷
   rw 4 (q68 c4) ∷
   rw 5 (q121 c4) ∷
   re 0 6 (Bx3-0142 ∷ []) ∷ []) Eq.refl

-- nat 3 CCZ123: 2 steps
lem-nat-3-CCZ123 : WsL → ⟪ (Sw34 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CCZ123 c4 = derive (Sw34 ∷ CCZ123 ∷ []) (CCZ124 ∷ Sw34 ∷ [])
  (rw⁻ 2 (q6 c4) ∷
   re 0 3 (CCZ124 ∷ []) ∷ []) Eq.refl

-- nat 3 TOFF103: 2 steps
lem-nat-3-TOFF103 : WsL → ⟪ (Sw34 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF103 c4 = derive (Sw34 ∷ Toff103 ∷ []) (Toff104 ∷ Sw34 ∷ [])
  (rw⁻ 2 (q6 c4) ∷
   re 0 3 (Toff104 ∷ []) ∷ []) Eq.refl

private
  q122 : WsL → Eqn
  q122 c4 = eqn (Sw34 ∷ CCZ013 ∷ []) (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4)
  q123 : WsL → Eqn
  q123 c4 = eqn (Sw34 ∷ Toff103 ∷ []) (Toff104 ∷ Sw34 ∷ []) (lem-nat-3-TOFF103 c4)
  q124 : WsL → Eqn
  q124 c4 = eqn (Sw34 ∷ Bx0-14 ∷ []) (Bx0-13 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·14⟩ c4)

-- nat 3 BOX(1;034): 8 steps
lem-nat-3-BOX⟨1·034⟩ : WsL → ⟪ (Sw34 ∷ Bx1-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-043 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·034⟩ c4 = derive (Sw34 ∷ Bx1-034 ∷ []) (Bx1-043 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) ∷
   rw 0 (q122 c4) ∷
   rw 1 (q123 c4) ∷
   rw 2 (q124 c4) ∷
   rw 3 (q123 c4) ∷
   rw 4 (q122 c4) ∷
   rw 5 (q124 c4) ∷
   re 0 6 (Bx1-043 ∷ []) ∷ []) Eq.refl

private
  q125 : WsL → Eqn
  q125 c4 = eqn (CCZ012 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (Swap))
  q126 : WsL → Eqn
  q126 c4 = eqn (Toff012 ∷ Sw34 ∷ []) (Sw34 ∷ Toff012 ∷ []) (c₃ (Toff) (Swap))
  q127 : WsL → Eqn
  q127 c4 = eqn (Sw34 ∷ Bx1-034 ∷ []) (Bx1-043 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·034⟩ c4)

-- nat 3 BOX(0;1234): 8 steps
lem-nat-3-BOX⟨0·1234⟩ : WsL → ⟪ (Sw34 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·1234⟩ c4 = derive (Sw34 ∷ Bx0-1234 ∷ []) (Bx0-1243 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) ∷
   rw⁻ 0 (q125 c4) ∷
   rw⁻ 1 (q126 c4) ∷
   rw 2 (q127 c4) ∷
   rw⁻ 3 (q126 c4) ∷
   rw⁻ 4 (q125 c4) ∷
   rw 5 (q127 c4) ∷
   re 0 6 (Bx0-1243 ∷ []) ∷ []) Eq.refl

-- nat 3 CCZ124: 2 steps
lem-nat-3-CCZ124 : WsL → ⟪ (Sw34 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CCZ124 c4 = derive (Sw34 ∷ CCZ124 ∷ []) (CCZ123 ∷ Sw34 ∷ [])
  (re 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   rw 0 (q6 c4) ∷ []) Eq.refl

-- nat 0 BOX(0;143): 8 steps
lem-nat-0-BOX⟨0·143⟩ : WsL → ⟪ (Sw01 ∷ Bx0-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-043 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·143⟩ c4 = derive (Sw01 ∷ Bx0-143 ∷ []) (Bx1-043 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-03 ∷ Toff014 ∷ CCZ014 ∷ Bx1-03 ∷ []) ∷
   rw 0 (q37 c4) ∷
   rw 1 (q59 c4) ∷
   rw 2 (q75 c4) ∷
   rw 3 (q59 c4) ∷
   rw 4 (q37 c4) ∷
   rw 5 (q75 c4) ∷
   re 0 6 (Bx1-043 ∷ []) ∷ []) Eq.refl

private
  q128 : WsL → Eqn
  q128 c4 = eqn (Sw01 ∷ Bx0-143 ∷ []) (Bx1-043 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·143⟩ c4)

-- nat 0 BOX(1;0243): 8 steps
lem-nat-0-BOX⟨1·0243⟩ : WsL → ⟪ (Sw01 ∷ Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·0243⟩ c4 = derive (Sw01 ∷ Bx1-0243 ∷ []) (Bx0-1243 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-143 ∷ Toff102 ∷ CCZ012 ∷ Bx0-143 ∷ []) ∷
   rw⁻ 0 (q56 c4) ∷
   rw 1 (q57 c4) ∷
   rw 2 (q128 c4) ∷
   rw 3 (q57 c4) ∷
   rw⁻ 4 (q56 c4) ∷
   rw 5 (q128 c4) ∷
   re 0 6 (Bx0-1243 ∷ []) ∷ []) Eq.refl

private
  q129 : WsL → Eqn
  q129 c4 = eqn (Sw12 ∷ Toff024 ∷ []) (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4)

-- nat 1 BOX(0;243): 8 steps
lem-nat-1-BOX⟨0·243⟩ : WsL → ⟪ (Sw12 ∷ Bx0-243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-143 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·243⟩ c4 = derive (Sw12 ∷ Bx0-243 ∷ []) (Bx0-143 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) ∷
   rw 0 (q79 c4) ∷
   rw 1 (q129 c4) ∷
   rw 2 (q78 c4) ∷
   rw 3 (q129 c4) ∷
   rw 4 (q79 c4) ∷
   rw 5 (q78 c4) ∷
   re 0 6 (Bx0-143 ∷ []) ∷ []) Eq.refl

private
  q130 : WsL → Eqn
  q130 c4 = eqn (Sw12 ∷ Bx0-243 ∷ []) (Bx0-143 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·243⟩ c4)

-- nat 1 BOX(2;0143): 8 steps
lem-nat-1-BOX⟨2·0143⟩ : WsL → ⟪ (Sw12 ∷ Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0243 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·0143⟩ c4 = derive (Sw12 ∷ Bx2-0143 ∷ []) (Bx1-0243 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ []) ∷
   rw⁻ 0 (q62 c4) ∷
   rw 1 (q106 c4) ∷
   rw 2 (q130 c4) ∷
   rw 3 (q106 c4) ∷
   rw⁻ 4 (q62 c4) ∷
   rw 5 (q130 c4) ∷
   re 0 6 (Bx1-0243 ∷ []) ∷ []) Eq.refl

private
  q131 : WsL → Eqn
  q131 c4 = eqn (Sw23 ∷ Toff034 ∷ []) (Toff024 ∷ Sw23 ∷ []) (lem-nat-2-TOFF034 c4)

-- nat 2 BOX(0;342): 8 steps
lem-nat-2-BOX⟨0·342⟩ : WsL → ⟪ (Sw23 ∷ Bx0-342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-243 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·342⟩ c4 = derive (Sw23 ∷ Bx0-342 ∷ []) (Bx0-243 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) ∷
   rw 0 (q86 c4) ∷
   rw 1 (q131 c4) ∷
   rw 2 (q85 c4) ∷
   rw 3 (q131 c4) ∷
   rw 4 (q86 c4) ∷
   rw 5 (q85 c4) ∷
   re 0 6 (Bx0-243 ∷ []) ∷ []) Eq.refl

private
  q132 : WsL → Eqn
  q132 c4 = eqn (Sw23 ∷ Bx0-342 ∷ []) (Bx0-243 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·342⟩ c4)

-- nat 2 BOX(3;0142): 8 steps
lem-nat-2-BOX⟨3·0142⟩ : WsL → ⟪ (Sw23 ∷ Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·0142⟩ c4 = derive (Sw23 ∷ Bx3-0142 ∷ []) (Bx2-0143 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-342 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ []) ∷
   rw 0 (q83 c4) ∷
   rw 1 (q117 c4) ∷
   rw 2 (q132 c4) ∷
   rw 3 (q117 c4) ∷
   rw 4 (q83 c4) ∷
   rw 5 (q132 c4) ∷
   re 0 6 (Bx2-0143 ∷ []) ∷ []) Eq.refl

private
  q133 : WsL → Eqn
  q133 c4 = eqn (Sw01 ∷ CZ14 ∷ []) (CZ04 ∷ Sw01 ∷ []) (lem-nat-0-CZ14 c4)

-- nat 0 BOX(0;14): 3 steps
lem-nat-0-BOX⟨0·14⟩ : WsL → ⟪ (Sw01 ∷ Bx0-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-04 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·14⟩ c4 = derive (Sw01 ∷ Bx0-14 ∷ []) (Bx1-04 ∷ Sw01 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   rw 0 (q133 c4) ∷
   re 0 1 (Bx1-04 ∷ []) ∷ []) Eq.refl

private
  q134 : WsL → Eqn
  q134 c4 = eqn (Sw01 ∷ Toff103 ∷ []) (Toff013 ∷ Sw01 ∷ []) (wl0102 c4)
  q135 : WsL → Eqn
  q135 c4 = eqn (Sw01 ∷ Bx0-14 ∷ []) (Bx1-04 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·14⟩ c4)

-- nat 0 BOX(1;034): 8 steps
lem-nat-0-BOX⟨1·034⟩ : WsL → ⟪ (Sw01 ∷ Bx1-034 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-134 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·034⟩ c4 = derive (Sw01 ∷ Bx1-034 ∷ []) (Bx0-134 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-14 ∷ Toff103 ∷ CCZ013 ∷ Bx0-14 ∷ []) ∷
   rw⁻ 0 (q97 c4) ∷
   rw 1 (q134 c4) ∷
   rw 2 (q135 c4) ∷
   rw 3 (q134 c4) ∷
   rw⁻ 4 (q97 c4) ∷
   rw 5 (q135 c4) ∷
   re 0 6 (Bx0-134 ∷ []) ∷ []) Eq.refl

private
  q136 : WsL → Eqn
  q136 c4 = eqn (Sw01 ∷ Bx1-034 ∷ []) (Bx0-134 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·034⟩ c4)

-- nat 0 BOX(0;1234): 8 steps
lem-nat-0-BOX⟨0·1234⟩ : WsL → ⟪ (Sw01 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·1234⟩ c4 = derive (Sw01 ∷ Bx0-1234 ∷ []) (Bx1-0234 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-034 ∷ Toff012 ∷ CCZ012 ∷ Bx1-034 ∷ []) ∷
   rw⁻ 0 (q56 c4) ∷
   rw 1 (q74 c4) ∷
   rw 2 (q136 c4) ∷
   rw 3 (q74 c4) ∷
   rw⁻ 4 (q56 c4) ∷
   rw 5 (q136 c4) ∷
   re 0 6 (Bx1-0234 ∷ []) ∷ []) Eq.refl

-- nat 1 BOX(1;04): 3 steps
lem-nat-1-BOX⟨1·04⟩ : WsL → ⟪ (Sw12 ∷ Bx1-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-04 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·04⟩ c4 = derive (Sw12 ∷ Bx1-04 ∷ []) (Bx2-04 ∷ Sw12 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   rw 0 (q102 c4) ∷
   re 0 1 (Bx2-04 ∷ []) ∷ []) Eq.refl

private
  q137 : WsL → Eqn
  q137 c4 = eqn (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4)
  q138 : WsL → Eqn
  q138 c4 = eqn (Sw12 ∷ Toff013 ∷ []) (Toff023 ∷ Sw12 ∷ []) (lem-nat-1-TOFF013 c4)
  q139 : WsL → Eqn
  q139 c4 = eqn (Sw12 ∷ Bx1-04 ∷ []) (Bx2-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·04⟩ c4)

-- nat 1 BOX(0;134): 8 steps
lem-nat-1-BOX⟨0·134⟩ : WsL → ⟪ (Sw12 ∷ Bx0-134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-234 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·134⟩ c4 = derive (Sw12 ∷ Bx0-134 ∷ []) (Bx0-234 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx1-04 ∷ Toff013 ∷ CCZ013 ∷ Bx1-04 ∷ []) ∷
   rw 0 (q137 c4) ∷
   rw 1 (q138 c4) ∷
   rw 2 (q139 c4) ∷
   rw 3 (q138 c4) ∷
   rw 4 (q137 c4) ∷
   rw 5 (q139 c4) ∷
   re 0 6 (Bx0-234 ∷ []) ∷ []) Eq.refl

private
  q140 : WsL → Eqn
  q140 c4 = eqn (Sw12 ∷ Bx0-134 ∷ []) (Bx0-234 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·134⟩ c4)

-- nat 1 BOX(1;0234): 8 steps
lem-nat-1-BOX⟨1·0234⟩ : WsL → ⟪ (Sw12 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·0234⟩ c4 = derive (Sw12 ∷ Bx1-0234 ∷ []) (Bx2-0134 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-134 ∷ Toff102 ∷ CCZ012 ∷ Bx0-134 ∷ []) ∷
   rw⁻ 0 (q62 c4) ∷
   rw 1 (q109 c4) ∷
   rw 2 (q140 c4) ∷
   rw 3 (q109 c4) ∷
   rw⁻ 4 (q62 c4) ∷
   rw 5 (q140 c4) ∷
   re 0 6 (Bx2-0134 ∷ []) ∷ []) Eq.refl

-- nat 2 BOX(2;04): 3 steps
lem-nat-2-BOX⟨2·04⟩ : WsL → ⟪ (Sw23 ∷ Bx2-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-04 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·04⟩ c4 = derive (Sw23 ∷ Bx2-04 ∷ []) (Bx3-04 ∷ Sw23 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   rw 0 (q113 c4) ∷
   re 0 1 (Bx3-04 ∷ []) ∷ []) Eq.refl

private
  q141 : WsL → Eqn
  q141 c4 = eqn (Sw23 ∷ Bx2-04 ∷ []) (Bx3-04 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·04⟩ c4)

-- nat 2 BOX(0;234): 8 steps
lem-nat-2-BOX⟨0·234⟩ : WsL → ⟪ (Sw23 ∷ Bx0-234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-324 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·234⟩ c4 = derive (Sw23 ∷ Bx0-234 ∷ []) (Bx0-324 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) ∷
   rw⁻ 0 (q114 c4) ∷
   rw 1 (q115 c4) ∷
   rw 2 (q141 c4) ∷
   rw 3 (q115 c4) ∷
   rw⁻ 4 (q114 c4) ∷
   rw 5 (q141 c4) ∷
   re 0 6 (Bx0-324 ∷ []) ∷ []) Eq.refl

private
  q142 : WsL → Eqn
  q142 c4 = eqn (Sw23 ∷ Bx0-234 ∷ []) (Bx0-324 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·234⟩ c4)

-- nat 2 BOX(2;0134): 8 steps
lem-nat-2-BOX⟨2·0134⟩ : WsL → ⟪ (Sw23 ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·0134⟩ c4 = derive (Sw23 ∷ Bx2-0134 ∷ []) (Bx3-0124 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ []) ∷
   rw 0 (q68 c4) ∷
   rw 1 (q120 c4) ∷
   rw 2 (q142 c4) ∷
   rw 3 (q120 c4) ∷
   rw 4 (q68 c4) ∷
   rw 5 (q142 c4) ∷
   re 0 6 (Bx3-0124 ∷ []) ∷ []) Eq.refl

private
  q143 : WsL → Eqn
  q143 c4 = eqn (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) (wl0063 c4)
  q144 : WsL → Eqn
  q144 c4 = eqn (Sw01 ∷ Toff324 ∷ []) (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))

-- resp TOFF314 at 2: 4 steps
lem-resp-TOFF314-at-2 : WsL → ⟪ (Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ Toff324 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-TOFF314-at-2 c4 = derive (Toff314 ∷ []) (Sw12 ∷ Sw01 ∷ Toff324 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q11 c4) ∷
   rw⁻ 0 (q143 c4) ∷
   rw⁻ 2 (q89 c4) ∷
   rw⁻ 1 (q144 c4) ∷ []) Eq.refl

-- resp CS03 at 2: 4 steps
lem-resp-CS03-at-2 : WsL → ⟪ (CS03 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CS03-at-2 c4 = derive (CS03 ∷ []) (Sw12 ∷ Sw01 ∷ CS13 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q11 c4) ∷
   rw 0 (q14 c4) ∷
   rw⁻ 2 (q89 c4) ∷
   rw 1 (q29 c4) ∷ []) Eq.refl

private
  q145 : WsL → Eqn
  q145 c4 = eqn (CS03⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS03⁻ ∷ []) (wl0023 c4)

-- resp CSd03 at 2: 4 steps
lem-resp-CSd03-at-2 : WsL → ⟪ (CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CSd03-at-2 c4 = derive (CS03⁻ ∷ []) (Sw12 ∷ Sw01 ∷ CS13⁻ ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q11 c4) ∷
   rw 0 (q145 c4) ∷
   rw⁻ 2 (q89 c4) ∷
   rw 1 (q31 c4) ∷ []) Eq.refl

-- nat 1 BOX(3;04): 3 steps
lem-nat-1-BOX⟨3·04⟩ : WsL → ⟪ (Sw12 ∷ Bx3-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-04 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·04⟩ c4 = derive (Sw12 ∷ Bx3-04 ∷ []) (Bx3-04 ∷ Sw12 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   rw 0 (q102 c4) ∷
   re 0 1 (Bx3-04 ∷ []) ∷ []) Eq.refl

private
  q146 : WsL → Eqn
  q146 c4 = eqn (Sw12 ∷ Bx3-04 ∷ []) (Bx3-04 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·04⟩ c4)

-- nat 1 BOX(0;314): 8 steps
lem-nat-1-BOX⟨0·314⟩ : WsL → ⟪ (Sw12 ∷ Bx0-314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-324 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·314⟩ c4 = derive (Sw12 ∷ Bx0-314 ∷ []) (Bx0-324 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) ∷
   rw 0 (q137 c4) ∷
   rw 1 (q138 c4) ∷
   rw 2 (q146 c4) ∷
   rw 3 (q138 c4) ∷
   rw 4 (q137 c4) ∷
   rw 5 (q146 c4) ∷
   re 0 6 (Bx0-324 ∷ []) ∷ []) Eq.refl

private
  q147 : WsL → Eqn
  q147 c4 = eqn (Sw12 ∷ Toff302 ∷ []) (Toff301 ∷ Sw12 ∷ []) (lem-nat-1-TOFF302 c4)
  q148 : WsL → Eqn
  q148 c4 = eqn (Sw12 ∷ Bx0-314 ∷ []) (Bx0-324 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·314⟩ c4)

-- nat 1 BOX(3;0214): 8 steps
lem-nat-1-BOX⟨3·0214⟩ : WsL → ⟪ (Sw12 ∷ Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·0214⟩ c4 = derive (Sw12 ∷ Bx3-0214 ∷ []) (Bx3-0124 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ []) ∷
   rw 0 (q103 c4) ∷
   rw 1 (q147 c4) ∷
   rw 2 (q148 c4) ∷
   rw 3 (q147 c4) ∷
   rw 4 (q103 c4) ∷
   rw 5 (q148 c4) ∷
   re 0 6 (Bx3-0124 ∷ []) ∷ []) Eq.refl

-- nat 1 BOX(0;324): 8 steps
lem-nat-1-BOX⟨0·324⟩ : WsL → ⟪ (Sw12 ∷ Bx0-324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-314 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·324⟩ c4 = derive (Sw12 ∷ Bx0-324 ∷ []) (Bx0-314 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) ∷
   rw 0 (q103 c4) ∷
   rw 1 (q104 c4) ∷
   rw 2 (q146 c4) ∷
   rw 3 (q104 c4) ∷
   rw 4 (q103 c4) ∷
   rw 5 (q146 c4) ∷
   re 0 6 (Bx0-314 ∷ []) ∷ []) Eq.refl

private
  q149 : WsL → Eqn
  q149 c4 = eqn (Sw12 ∷ Toff301 ∷ []) (Toff302 ∷ Sw12 ∷ []) (lem-nat-1-TOFF301 c4)
  q150 : WsL → Eqn
  q150 c4 = eqn (Sw12 ∷ Bx0-324 ∷ []) (Bx0-314 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·324⟩ c4)

-- nat 1 BOX(3;0124): 8 steps
lem-nat-1-BOX⟨3·0124⟩ : WsL → ⟪ (Sw12 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·0124⟩ c4 = derive (Sw12 ∷ Bx3-0124 ∷ []) (Bx3-0214 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) ∷
   rw 0 (q137 c4) ∷
   rw 1 (q149 c4) ∷
   rw 2 (q150 c4) ∷
   rw 3 (q149 c4) ∷
   rw 4 (q137 c4) ∷
   rw 5 (q150 c4) ∷
   re 0 6 (Bx3-0214 ∷ []) ∷ []) Eq.refl

-- nat 2 BOX(0;214): 8 steps
lem-nat-2-BOX⟨0·214⟩ : WsL → ⟪ (Sw23 ∷ Bx0-214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-314 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·214⟩ c4 = derive (Sw23 ∷ Bx0-214 ∷ []) (Bx0-314 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) ∷
   rw 0 (q68 c4) ∷
   rw 1 (q69 c4) ∷
   rw 2 (q141 c4) ∷
   rw 3 (q69 c4) ∷
   rw 4 (q68 c4) ∷
   rw 5 (q141 c4) ∷
   re 0 6 (Bx0-314 ∷ []) ∷ []) Eq.refl

private
  q151 : WsL → Eqn
  q151 c4 = eqn (Sw23 ∷ Toff203 ∷ []) (Toff302 ∷ Sw23 ∷ []) (wl0090 c4)
  q152 : WsL → Eqn
  q152 c4 = eqn (Sw23 ∷ Bx0-214 ∷ []) (Bx0-314 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·214⟩ c4)

-- nat 2 BOX(2;0314): 8 steps
lem-nat-2-BOX⟨2·0314⟩ : WsL → ⟪ (Sw23 ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·0314⟩ c4 = derive (Sw23 ∷ Bx2-0314 ∷ []) (Bx3-0214 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ []) ∷
   rw⁻ 0 (q114 c4) ∷
   rw 1 (q151 c4) ∷
   rw 2 (q152 c4) ∷
   rw 3 (q151 c4) ∷
   rw⁻ 4 (q114 c4) ∷
   rw 5 (q152 c4) ∷
   re 0 6 (Bx3-0214 ∷ []) ∷ []) Eq.refl

-- nat 2 BOX(0;314): 8 steps
lem-nat-2-BOX⟨0·314⟩ : WsL → ⟪ (Sw23 ∷ Bx0-314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-214 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·314⟩ c4 = derive (Sw23 ∷ Bx0-314 ∷ []) (Bx0-214 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) ∷
   rw 0 (q83 c4) ∷
   rw 1 (q84 c4) ∷
   rw 2 (q116 c4) ∷
   rw 3 (q84 c4) ∷
   rw 4 (q83 c4) ∷
   rw 5 (q116 c4) ∷
   re 0 6 (Bx0-214 ∷ []) ∷ []) Eq.refl

private
  q153 : WsL → Eqn
  q153 c4 = eqn (Sw23 ∷ Toff302 ∷ []) (Toff203 ∷ Sw23 ∷ []) (wl0066 c4)
  q154 : WsL → Eqn
  q154 c4 = eqn (Sw23 ∷ Bx0-314 ∷ []) (Bx0-214 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·314⟩ c4)

-- nat 2 BOX(3;0214): 8 steps
lem-nat-2-BOX⟨3·0214⟩ : WsL → ⟪ (Sw23 ∷ Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·0214⟩ c4 = derive (Sw23 ∷ Bx3-0214 ∷ []) (Bx2-0314 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ []) ∷
   rw⁻ 0 (q114 c4) ∷
   rw 1 (q153 c4) ∷
   rw 2 (q154 c4) ∷
   rw 3 (q153 c4) ∷
   rw⁻ 4 (q114 c4) ∷
   rw 5 (q154 c4) ∷
   re 0 6 (Bx2-0314 ∷ []) ∷ []) Eq.refl

-- nat 3 CZ03: 2 steps
lem-nat-3-CZ03 : WsL → ⟪ (Sw34 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (CZ04 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CZ03 c4 = derive (Sw34 ∷ CZ03 ∷ []) (CZ04 ∷ Sw34 ∷ [])
  (rw⁻ 2 (q6 c4) ∷
   re 0 3 (CZ04 ∷ []) ∷ []) Eq.refl

private
  q155 : WsL → Eqn
  q155 c4 = eqn (Sw34 ∷ CZ03 ∷ []) (CZ04 ∷ Sw34 ∷ []) (lem-nat-3-CZ03 c4)

-- nat 3 BOX(2;03): 3 steps
lem-nat-3-BOX⟨2·03⟩ : WsL → ⟪ (Sw34 ∷ Bx2-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-04 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·03⟩ c4 = derive (Sw34 ∷ Bx2-03 ∷ []) (Bx2-04 ∷ Sw34 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw 0 (q155 c4) ∷
   re 0 1 (Bx2-04 ∷ []) ∷ []) Eq.refl

private
  q156 : WsL → Eqn
  q156 c4 = eqn (Sw34 ∷ Bx2-03 ∷ []) (Bx2-04 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·03⟩ c4)

-- nat 3 BOX(0;213): 8 steps
lem-nat-3-BOX⟨0·213⟩ : WsL → ⟪ (Sw34 ∷ Bx0-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-214 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·213⟩ c4 = derive (Sw34 ∷ Bx0-213 ∷ []) (Bx0-214 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   rw⁻ 0 (q125 c4) ∷
   rw⁻ 1 (q126 c4) ∷
   rw 2 (q156 c4) ∷
   rw⁻ 3 (q126 c4) ∷
   rw⁻ 4 (q125 c4) ∷
   rw 5 (q156 c4) ∷
   re 0 6 (Bx0-214 ∷ []) ∷ []) Eq.refl

private
  q157 : WsL → Eqn
  q157 c4 = eqn (Sw34 ∷ CCZ024 ∷ []) (CCZ023 ∷ Sw34 ∷ []) (lem-nat-3-CCZ024 c4)
  q158 : WsL → Eqn
  q158 c4 = eqn (Sw34 ∷ Toff204 ∷ []) (Toff203 ∷ Sw34 ∷ []) (lem-nat-3-TOFF204 c4)
  q159 : WsL → Eqn
  q159 c4 = eqn (Sw34 ∷ Bx0-213 ∷ []) (Bx0-214 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·213⟩ c4)

-- nat 3 BOX(2;0413): 8 steps
lem-nat-3-BOX⟨2·0413⟩ : WsL → ⟪ (Sw34 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·0413⟩ c4 = derive (Sw34 ∷ Bx2-0413 ∷ []) (Bx2-0314 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) ∷
   rw 0 (q157 c4) ∷
   rw 1 (q158 c4) ∷
   rw 2 (q159 c4) ∷
   rw 3 (q158 c4) ∷
   rw 4 (q157 c4) ∷
   rw 5 (q159 c4) ∷
   re 0 6 (Bx2-0314 ∷ []) ∷ []) Eq.refl

-- nat 3 CZ04: 2 steps
lem-nat-3-CZ04 : WsL → ⟪ (Sw34 ∷ CZ04 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CZ04 c4 = derive (Sw34 ∷ CZ04 ∷ []) (CZ03 ∷ Sw34 ∷ [])
  (re 1 1 (Sw34 ∷ CZ03 ∷ Sw34 ∷ []) ∷
   rw 0 (q6 c4) ∷ []) Eq.refl

private
  q160 : WsL → Eqn
  q160 c4 = eqn (Sw34 ∷ CZ04 ∷ []) (CZ03 ∷ Sw34 ∷ []) (lem-nat-3-CZ04 c4)

-- nat 3 BOX(2;04): 3 steps
lem-nat-3-BOX⟨2·04⟩ : WsL → ⟪ (Sw34 ∷ Bx2-04 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-03 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·04⟩ c4 = derive (Sw34 ∷ Bx2-04 ∷ []) (Bx2-03 ∷ Sw34 ∷ [])
  (re 1 1 (CZ04 ∷ []) ∷
   rw 0 (q160 c4) ∷
   re 0 1 (Bx2-03 ∷ []) ∷ []) Eq.refl

private
  q161 : WsL → Eqn
  q161 c4 = eqn (Sw34 ∷ Bx2-04 ∷ []) (Bx2-03 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·04⟩ c4)

-- nat 3 BOX(0;214): 8 steps
lem-nat-3-BOX⟨0·214⟩ : WsL → ⟪ (Sw34 ∷ Bx0-214 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-213 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·214⟩ c4 = derive (Sw34 ∷ Bx0-214 ∷ []) (Bx0-213 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) ∷
   rw⁻ 0 (q125 c4) ∷
   rw⁻ 1 (q126 c4) ∷
   rw 2 (q161 c4) ∷
   rw⁻ 3 (q126 c4) ∷
   rw⁻ 4 (q125 c4) ∷
   rw 5 (q161 c4) ∷
   re 0 6 (Bx0-213 ∷ []) ∷ []) Eq.refl

private
  q162 : WsL → Eqn
  q162 c4 = eqn (Sw34 ∷ CCZ023 ∷ []) (CCZ024 ∷ Sw34 ∷ []) (lem-nat-3-CCZ023 c4)
  q163 : WsL → Eqn
  q163 c4 = eqn (Sw34 ∷ Toff203 ∷ []) (Toff204 ∷ Sw34 ∷ []) (lem-nat-3-TOFF203 c4)
  q164 : WsL → Eqn
  q164 c4 = eqn (Sw34 ∷ Bx0-214 ∷ []) (Bx0-213 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·214⟩ c4)

-- nat 3 BOX(2;0314): 8 steps
lem-nat-3-BOX⟨2·0314⟩ : WsL → ⟪ (Sw34 ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·0314⟩ c4 = derive (Sw34 ∷ Bx2-0314 ∷ []) (Bx2-0413 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ []) ∷
   rw 0 (q162 c4) ∷
   rw 1 (q163 c4) ∷
   rw 2 (q164 c4) ∷
   rw 3 (q163 c4) ∷
   rw 4 (q162 c4) ∷
   rw 5 (q164 c4) ∷
   re 0 6 (Bx2-0413 ∷ []) ∷ []) Eq.refl

private
  q165 : WsL → Eqn
  q165 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl0021 c4)
  q166 : WsL → Eqn
  q166 c4 = eqn (CS14⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS14⁻ ∷ []) (wl0033 c4)
  q167 : WsL → Eqn
  q167 c4 = eqn (CS01 ∷ Sw34 ∷ []) (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑))

-- nat 2 CCZ014: 53 steps
lem-nat-2-CCZ014 : WsL → ⟪ (Sw23 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-CCZ014 c4 = derive (Sw23 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw23 ∷ [])
  (re 1 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw⁻ 4 (q2 c4) ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 (q3 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 (q2 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   re 1 3 (CS14 ∷ []) ∷
   rw⁻ 2 (q7 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (CS14⁻ ∷ []) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 0 (q165 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw⁻ 2 (q166 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   re 5 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 4 (q111 c4) ∷
   rw⁻ 6 (q13 c4) ∷
   rw⁻ 7 (q167 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw⁻ 9 (q111 c4) ∷
   re 4 7 (CS04 ∷ []) ∷
   rw⁻ 0 (q6 c4) ∷
   re 2 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 1 (q6 c4) ∷
   rw⁻ 2 (q7 c4) ∷
   re 4 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 (q2 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 (q2 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 (q2 c4) ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   re 0 3 (CCZ014 ∷ []) ∷ []) Eq.refl

-- resp CCZ014 at 3: 112 steps
lem-resp-CCZ014-at-3 : WsL → ⟪ (CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ124 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CCZ014-at-3 c4 = derive (CCZ014 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CCZ124 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q2 c4) ∷
   re 0 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw⁻ 3 (q2 c4) ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 (q3 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 (q2 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   re 0 3 (CS14 ∷ []) ∷
   rw⁻ 1 (q7 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (CS14⁻ ∷ []) ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CS04 ∷ []) ∷
   rw 5 (q6 c4) ∷
   re 4 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 9 (q111 c4) ∷
   rw 8 (q13 c4) ∷
   rw 7 (q167 c4) ∷
   rw 6 (q13 c4) ∷
   rw⁻ 4 (q111 c4) ∷
   re 5 7 (CS04 ∷ []) ∷
   rw 3 (q3 c4) ∷
   rw 2 (q166 c4) ∷
   rw 1 (q3 c4) ∷
   rw 0 (q165 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   re 3 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 2 (q6 c4) ∷
   rw⁻ 3 (q7 c4) ∷
   re 5 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 (q2 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 (q2 c4) ∷
   re 3 5 (CCZ012 ∷ []) ∷
   re 2 3 (CCZ013 ∷ []) ∷
   re 1 3 (CCZ014 ∷ []) ∷
   rw⁻ 2 (q11 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   re 2 3 (CCZ024 ∷ []) ∷
   rw⁻ 3 (q89 c4) ∷
   re 2 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   re 3 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q3 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q3 c4) ∷
   rw⁻ 10 (q2 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 (q2 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q7 c4) ∷
   rw⁻ 9 (q6 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw 8 (q6 c4) ∷
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
   rw 7 (q11 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q20 c4) ∷
   rw 7 (q29 c4) ∷
   rw⁻ 6 (q20 c4) ∷
   re 7 3 (CS14 ∷ []) ∷
   rw 5 (q90 c4) ∷
   rw⁻ 4 (q19 c4) ∷
   rw 3 (q90 c4) ∷
   rw⁻ 2 (q17 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   re 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q24 c4) ∷
   re 7 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q24 c4) ∷
   re 9 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 8 (q6 c4) ∷
   re 4 5 (CCZ123 ∷ []) ∷
   re 3 3 (CCZ124 ∷ []) ∷ []) Eq.refl

-- resp TOFF214 at 3: 7 steps
lem-resp-TOFF214-at-3 : WsL → ⟪ (Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff324 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF214-at-3 c4 = derive (Toff214 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff324 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q2 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   re 1 3 (Toff314 ∷ []) ∷
   rw⁻ 2 (q11 c4) ∷
   rw⁻ 1 (q143 c4) ∷
   rw⁻ 3 (q89 c4) ∷
   rw⁻ 2 (q144 c4) ∷ []) Eq.refl

private
  q168 : WsL → Eqn
  q168 c4 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (c₂ (K ↑) (Swap))
  q169 : WsL → Eqn
  q169 c4 = eqn (K2 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ []) (wl0056 c4)
  q170 : WsL → Eqn
  q170 c4 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (c₂ (Swap) (K))
  q171 : WsL → Eqn
  q171 c4 = eqn (K2 ∷ Sw34 ∷ []) (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap))
  q172 : WsL → Eqn
  q172 c4 = eqn (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (wl0059 c4)

-- resp TOFF204 at 1: 71 steps
lem-resp-TOFF204-at-1 : WsL → ⟪ (Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff214 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF204-at-1 c4 = derive (Toff204 ∷ []) (Sw01 ∷ Toff214 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q89 c4) ∷
   re 0 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) ∷
   re 1 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) ∷
   re 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 (q168 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 (q3 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q3 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 (q168 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw 10 (q2 c4) ∷
   rw⁻ 1 (q23 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (CS14 ∷ []) ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CS14⁻ ∷ []) ∷
   rw⁻ 5 (q7 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q23 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw 9 (q6 c4) ∷
   rw⁻ 0 (q169 c4) ∷
   rw⁻ 1 (q10 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   re 2 3 (CX02 ∷ []) ∷
   rw⁻ 3 (q12 c4) ∷
   rw⁻ 6 (q11 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q13 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw 7 (q13 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw⁻ 6 (q169 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw 8 (q11 c4) ∷
   rw⁻ 7 (q22 c4) ∷
   rw⁻ 6 (q170 c4) ∷
   re 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 7 (q20 c4) ∷
   rw 6 (q29 c4) ∷
   rw⁻ 5 (q20 c4) ∷
   re 6 3 (CS14 ∷ []) ∷
   rw 4 (q90 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw 2 (q90 c4) ∷
   rw⁻ 1 (q17 c4) ∷
   rw⁻ 0 (q170 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw⁻ 2 (q171 c4) ∷
   re 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q24 c4) ∷
   re 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q24 c4) ∷
   re 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 7 (q6 c4) ∷
   rw⁻ 8 (q171 c4) ∷
   rw⁻ 9 (q8 c4) ∷
   rw 2 (q172 c4) ∷
   re 2 8 (Toff213 ∷ []) ∷
   re 1 3 (Toff214 ∷ []) ∷ []) Eq.refl

private
  q173 : WsL → Eqn
  q173 c4 = eqn (Sw01 ∷ Bx1-24 ∷ []) (Bx1-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑))

-- nat 0 BOX(1;24): 2 steps
lem-nat-0-BOX⟨1·24⟩ : WsL → ⟪ (Sw01 ∷ Bx1-24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-24 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·24⟩ c4 = derive (Sw01 ∷ Bx1-24 ∷ []) (Bx0-24 ∷ Sw01 ∷ [])
  (rw 0 (q173 c4) ∷
   re 0 1 (Bx0-24 ∷ []) ∷ []) Eq.refl
