{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R003 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0015 ; wl0016 ; wl0017 ; wl0018 ; wl0019 ; wl0020 ; wl0021 ; wl0022 ; wl0028 ; wl0030 ; wl0031 ; wl0037 ; wl0038 ; wl0039 ; wl0040 ; wl0048 ; wl0056 ; wl0057 ; wl0058 ; wl0059 ; wl0061 ; wl0062 ; wl0067 ; wl0068 ; wl0070 ; wl0071 ; wl0072 ; wl0073 ; wl0074 ; wl0075 ; wl0076 ; wl0077 ; wl0078 ; wl0079 ; wl0080 ; wl0081 ; wl0082 ; wl0083)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ024 ; lem-nat-2-CCZ012 ; lem-nat-2-CCZ024 ; lem-nat-2-CCZ034 ; lem-nat-2-TOFF012 ; lem-nat-3-CCZ014 ; lem-nat-3-CCZ034 ; lem-nat-3-TOFF013 ; lem-nat-3-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ124 ; lem-nat-1-BOX⟨0·13⟩ ; lem-nat-1-CCZ014 ; lem-nat-2-BOX⟨0·23⟩ ; lem-nat-2-CCZ134 ; lem-nat-2-TOFF204 ; lem-nat-2-TOFF304 ; lem-nat-3-BOX⟨4·023⟩ ; lem-nat-3-CCZ013)

private
  q1 : WsL → Eqn
  q1 c4 = eqn (Sw34 ∷ CCZ014 ∷ []) (CCZ013 ∷ Sw34 ∷ []) (lem-nat-3-CCZ014 c4)
  q2 : WsL → Eqn
  q2 c4 = eqn (Sw34 ∷ Toff014 ∷ []) (Toff013 ∷ Sw34 ∷ []) (lem-nat-3-TOFF014 c4)
  q3 : WsL → Eqn
  q3 c4 = eqn (Sw34 ∷ Bx4-023 ∷ []) (Bx3-024 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨4·023⟩ c4)

-- nat 3 BOX(0;4123): 8 steps
lem-nat-3-BOX⟨0·4123⟩ : WsL → ⟪ (Sw34 ∷ Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·4123⟩ c4 = derive (Sw34 ∷ Bx0-4123 ∷ []) (Bx0-3124 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) ∷
   rw 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 3 (q2 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q3 c4) ∷
   re 0 6 (Bx0-3124 ∷ []) ∷ []) Eq.refl

private
  q4 : WsL → Eqn
  q4 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 c4)
  q5 : WsL → Eqn
  q5 c4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap))
  q6 : WsL → Eqn
  q6 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 c4)
  q7 : WsL → Eqn
  q7 c4 = eqn (CX01 ∷ Sw34 ∷ []) (Sw34 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap ↑))
  q8 : WsL → Eqn
  q8 c4 = eqn (Sw01 ∷ Sw34 ∷ []) (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑))
  q9 : WsL → Eqn
  q9 c4 = eqn (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) (wl0019 c4)
  q10 : WsL → Eqn
  q10 c4 = eqn (CX10 ∷ Sw01 ∷ []) (Sw01 ∷ CX01 ∷ []) (wl0070 c4)
  q11 : WsL → Eqn
  q11 c4 = eqn (CS03⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS13⁻ ∷ []) (wl0022 c4)
  q12 : WsL → Eqn
  q12 c4 = eqn (CS13 ∷ Sw01 ∷ []) (Sw01 ∷ CS03 ∷ []) (wl0061 c4)
  q13 : WsL → Eqn
  q13 c4 = eqn (CX10 ∷ Sw34 ∷ []) (Sw34 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Swap ↑))
  q14 : WsL → Eqn
  q14 c4 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Swap))
  q15 : WsL → Eqn
  q15 c4 = eqn (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0071 c4)

-- nat 0 CCZ014: 60 steps
lem-nat-0-CCZ014 : WsL → ⟪ (Sw01 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CCZ014 c4 = derive (Sw01 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw⁻ 4 (q4 c4) ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 (q5 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 (q5 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 (q4 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   re 1 3 (CS14 ∷ []) ∷
   rw⁻ 2 (q7 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (CS14⁻ ∷ []) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw 6 (q6 c4) ∷
   re 1 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 0 (q8 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   rw 2 (q8 c4) ∷
   re 0 3 (CS04 ∷ []) ∷
   rw⁻ 1 (q10 c4) ∷
   re 3 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 2 (q8 c4) ∷
   rw⁻ 3 (q11 c4) ∷
   rw 4 (q8 c4) ∷
   re 2 3 (CS04⁻ ∷ []) ∷
   rw⁻ 3 (q10 c4) ∷
   re 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 4 (q8 c4) ∷
   rw⁻ 5 (q12 c4) ∷
   rw 6 (q8 c4) ∷
   re 4 3 (CS14 ∷ []) ∷
   rw⁻ 0 (q6 c4) ∷
   re 2 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 1 (q6 c4) ∷
   rw⁻ 2 (q13 c4) ∷
   re 4 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   re 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 1 (q4 c4) ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 (q4 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   re 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 (q4 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 (q4 c4) ∷
   rw 2 (q15 c4) ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   re 0 3 (CCZ014 ∷ []) ∷ []) Eq.refl

private
  q16 : WsL → Eqn
  q16 c4 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (c₂ (K ↑) (Swap))
  q17 : WsL → Eqn
  q17 c4 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (c₁ (iI) (Swap ↑))
  q18 : WsL → Eqn
  q18 c4 = eqn (K1 ∷ Sw34 ∷ []) (Sw34 ∷ K1 ∷ []) (c₂ (K ↑) (Swap ↑))
  q19 : WsL → Eqn
  q19 c4 = eqn (ι ∷ Sw34 ∷ []) (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑))
  q20 : WsL → Eqn
  q20 c4 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wl0031 c4)
  q21 : WsL → Eqn
  q21 c4 = eqn (Sw01 ∷ ι ∷ []) (ι ∷ Sw01 ∷ []) (wl0030 c4)
  q22 : WsL → Eqn
  q22 c4 = eqn (K0 ∷ Sw34 ∷ []) (Sw34 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑))
  q23 : WsL → Eqn
  q23 c4 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (c₁ (K) (Swap ↑))
  q24 : WsL → Eqn
  q24 c4 = eqn (K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wl0072 c4)

-- nat 0 TOFF104: 75 steps
lem-nat-0-TOFF104 : WsL → ⟪ (Sw01 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF104 c4 = derive (Sw01 ∷ Toff104 ∷ []) (Toff014 ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) ∷
   re 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 (q16 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 (q5 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q5 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 (q16 c4) ∷
   rw⁻ 9 (q17 c4) ∷
   rw 10 (q4 c4) ∷
   rw⁻ 1 (q18 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (CS14 ∷ []) ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CS14⁻ ∷ []) ∷
   rw⁻ 5 (q7 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q18 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw 9 (q6 c4) ∷
   rw⁻ 0 (q20 c4) ∷
   re 2 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 1 (q8 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw 3 (q8 c4) ∷
   re 1 3 (CS04 ∷ []) ∷
   rw⁻ 2 (q10 c4) ∷
   re 4 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 3 (q8 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   rw 5 (q8 c4) ∷
   re 3 3 (CS04⁻ ∷ []) ∷
   rw⁻ 4 (q10 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q8 c4) ∷
   rw⁻ 6 (q12 c4) ∷
   rw 7 (q8 c4) ∷
   re 5 3 (CS14 ∷ []) ∷
   rw⁻ 6 (q20 c4) ∷
   rw 7 (q21 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   rw⁻ 1 (q22 c4) ∷
   re 3 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 2 (q6 c4) ∷
   rw⁻ 3 (q13 c4) ∷
   re 5 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q13 c4) ∷
   re 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q22 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw⁻ 1 (q4 c4) ∷
   rw⁻ 2 (q23 c4) ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 (q4 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 (q4 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 (q4 c4) ∷
   rw⁻ 8 (q23 c4) ∷
   rw⁻ 9 (q17 c4) ∷
   rw 2 (q24 c4) ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   re 0 3 (Toff014 ∷ []) ∷ []) Eq.refl

private
  q25 : WsL → Eqn
  q25 c4 = eqn (K4 ∷ Sw34 ∷ []) (Sw34 ∷ K3 ∷ []) (wl0067 c4)
  q26 : WsL → Eqn
  q26 c4 = eqn (CX12 ∷ Sw34 ∷ []) (Sw34 ∷ CX12 ∷ []) (c₃ (CX₀₁ ↑) (Swap))
  q27 : WsL → Eqn
  q27 c4 = eqn (ι1 ∷ Sw34 ∷ []) (Sw34 ∷ ι1 ∷ []) (c₂ (iI ↑) (Swap ↑))
  q28 : WsL → Eqn
  q28 c4 = eqn (Sw01 ∷ K4 ∷ []) (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑))
  q29 : WsL → Eqn
  q29 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q30 : WsL → Eqn
  q30 c4 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wl0048 c4)
  q31 : WsL → Eqn
  q31 c4 = eqn (Sw01 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q32 : WsL → Eqn
  q32 c4 = eqn (Sw01 ∷ ι1 ∷ []) (ι1 ∷ Sw01 ∷ []) (wl0073 c4)
  q33 : WsL → Eqn
  q33 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 c4)
  q34 : WsL → Eqn
  q34 c4 = eqn (Sw12 ∷ K4 ∷ []) (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑))
  q35 : WsL → Eqn
  q35 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl0017 c4)
  q36 : WsL → Eqn
  q36 c4 = eqn (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ []) (wl0018 c4)
  q37 : WsL → Eqn
  q37 c4 = eqn (Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap))
  q38 : WsL → Eqn
  q38 c4 = eqn (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) (wl0010 c4)
  q39 : WsL → Eqn
  q39 c4 = eqn (Sw12 ∷ ι1 ∷ []) (ι1 ∷ Sw12 ∷ []) (wl0074 c4)
  q40 : WsL → Eqn
  q40 c4 = eqn (K3 ∷ Sw34 ∷ []) (Sw34 ∷ K4 ∷ []) (wl0068 c4)
  q41 : WsL → Eqn
  q41 c4 = eqn (K2 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ []) (wl0058 c4)
  q42 : WsL → Eqn
  q42 c4 = eqn (ι1 ∷ Sw23 ∷ []) (Sw23 ∷ ι1 ∷ []) (c₂ (iI ↑) (Swap))
  q43 : WsL → Eqn
  q43 c4 = eqn (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι1 ∷ []) (wl0075 c4)

-- nat 0 TOFF412: 70 steps
lem-nat-0-TOFF412 : WsL → ⟪ (Sw01 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF412 c4 = derive (Sw01 ∷ Toff412 ∷ []) (Toff402 ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) ∷
   re 2 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw⁻ 1 (q25 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (CS24 ∷ []) ∷
   rw⁻ 3 (q26 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CS24⁻ ∷ []) ∷
   rw⁻ 5 (q26 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 6 3 (CS14 ∷ []) ∷
   rw⁻ 7 (q25 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw 9 (q6 c4) ∷
   rw 0 (q28 c4) ∷
   rw 1 (q29 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw 3 (q31 c4) ∷
   rw⁻ 4 (q30 c4) ∷
   re 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 5 (q8 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   rw 7 (q8 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw 6 (q28 c4) ∷
   rw 7 (q32 c4) ∷
   rw⁻ 0 (q33 c4) ∷
   rw 1 (q34 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 3 (q33 c4) ∷
   rw⁻ 4 (q36 c4) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 (q33 c4) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q37 c4) ∷
   rw⁻ 7 (q38 c4) ∷
   rw 8 (q37 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw 7 (q34 c4) ∷
   rw 8 (q39 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw⁻ 2 (q40 c4) ∷
   re 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   re 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q6 c4) ∷
   rw⁻ 8 (q40 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw⁻ 2 (q4 c4) ∷
   rw⁻ 3 (q41 c4) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 (q4 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q4 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 (q4 c4) ∷
   rw⁻ 9 (q41 c4) ∷
   rw⁻ 10 (q42 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   re 3 8 (Toff201 ∷ []) ∷
   re 2 3 (Toff301 ∷ []) ∷
   re 1 3 (Toff401 ∷ []) ∷
   re 0 3 (Toff402 ∷ []) ∷ []) Eq.refl

private
  q44 : WsL → Eqn
  q44 c4 = eqn (Sw01 ∷ Bx1-43 ∷ []) (Bx1-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑))

-- nat 0 BOX(1;43): 2 steps
lem-nat-0-BOX⟨1·43⟩ : WsL → ⟪ (Sw01 ∷ Bx1-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-43 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·43⟩ c4 = derive (Sw01 ∷ Bx1-43 ∷ []) (Bx0-43 ∷ Sw01 ∷ [])
  (rw 0 (q44 c4) ∷
   re 0 1 (Bx0-43 ∷ []) ∷ []) Eq.refl

private
  q45 : WsL → Eqn
  q45 c4 = eqn (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4)
  q46 : WsL → Eqn
  q46 c4 = eqn (Sw01 ∷ Toff412 ∷ []) (Toff402 ∷ Sw01 ∷ []) (lem-nat-0-TOFF412 c4)
  q47 : WsL → Eqn
  q47 c4 = eqn (Sw01 ∷ Bx1-43 ∷ []) (Bx0-43 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·43⟩ c4)

-- nat 0 BOX(4;123): 8 steps
lem-nat-0-BOX⟨4·123⟩ : WsL → ⟪ (Sw01 ∷ Bx4-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-023 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·123⟩ c4 = derive (Sw01 ∷ Bx4-123 ∷ []) (Bx4-023 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-43 ∷ Toff412 ∷ CCZ124 ∷ Bx1-43 ∷ []) ∷
   rw 0 (q45 c4) ∷
   rw 1 (q46 c4) ∷
   rw 2 (q47 c4) ∷
   rw 3 (q46 c4) ∷
   rw 4 (q45 c4) ∷
   rw 5 (q47 c4) ∷
   re 0 6 (Bx4-023 ∷ []) ∷ []) Eq.refl

private
  q48 : WsL → Eqn
  q48 c4 = eqn (Sw01 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw01 ∷ []) (lem-nat-0-CCZ014 c4)
  q49 : WsL → Eqn
  q49 c4 = eqn (Sw01 ∷ Toff104 ∷ []) (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4)
  q50 : WsL → Eqn
  q50 c4 = eqn (Sw01 ∷ Bx4-123 ∷ []) (Bx4-023 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·123⟩ c4)

-- nat 0 BOX(1;4023): 8 steps
lem-nat-0-BOX⟨1·4023⟩ : WsL → ⟪ (Sw01 ∷ Bx1-4023 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·4023⟩ c4 = derive (Sw01 ∷ Bx1-4023 ∷ []) (Bx0-4123 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff104 ∷ Bx4-123 ∷ Toff104 ∷ CCZ014 ∷ Bx4-123 ∷ []) ∷
   rw 0 (q48 c4) ∷
   rw 1 (q49 c4) ∷
   rw 2 (q50 c4) ∷
   rw 3 (q49 c4) ∷
   rw 4 (q48 c4) ∷
   rw 5 (q50 c4) ∷
   re 0 6 (Bx0-4123 ∷ []) ∷ []) Eq.refl

private
  q51 : WsL → Eqn
  q51 c4 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wl0076 c4)
  q52 : WsL → Eqn
  q52 c4 = eqn (K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wl0077 c4)

-- nat 0 TOFF014: 75 steps
lem-nat-0-TOFF014 : WsL → ⟪ (Sw01 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF014 c4 = derive (Sw01 ∷ Toff014 ∷ []) (Toff104 ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   re 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 (q23 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 (q5 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q5 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 (q23 c4) ∷
   rw⁻ 9 (q17 c4) ∷
   rw 10 (q4 c4) ∷
   rw⁻ 1 (q22 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (CS14 ∷ []) ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CS14⁻ ∷ []) ∷
   rw⁻ 5 (q7 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q22 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw 9 (q6 c4) ∷
   rw⁻ 0 (q51 c4) ∷
   re 2 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 1 (q8 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw 3 (q8 c4) ∷
   re 1 3 (CS04 ∷ []) ∷
   rw⁻ 2 (q10 c4) ∷
   re 4 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 3 (q8 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   rw 5 (q8 c4) ∷
   re 3 3 (CS04⁻ ∷ []) ∷
   rw⁻ 4 (q10 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q8 c4) ∷
   rw⁻ 6 (q12 c4) ∷
   rw 7 (q8 c4) ∷
   re 5 3 (CS14 ∷ []) ∷
   rw⁻ 6 (q51 c4) ∷
   rw 7 (q21 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   rw⁻ 1 (q18 c4) ∷
   re 3 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 2 (q6 c4) ∷
   rw⁻ 3 (q13 c4) ∷
   re 5 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q13 c4) ∷
   re 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q18 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw⁻ 1 (q4 c4) ∷
   rw⁻ 2 (q16 c4) ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 (q4 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 (q4 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 (q4 c4) ∷
   rw⁻ 8 (q16 c4) ∷
   rw⁻ 9 (q17 c4) ∷
   rw 2 (q52 c4) ∷
   re 2 8 (Toff102 ∷ []) ∷
   re 1 3 (Toff103 ∷ []) ∷
   re 0 3 (Toff104 ∷ []) ∷ []) Eq.refl

-- nat 1 TOFF204: 2 steps
lem-nat-1-TOFF204 : WsL → ⟪ (Sw12 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF204 c4 = derive (Sw12 ∷ Toff204 ∷ []) (Toff104 ∷ Sw12 ∷ [])
  (re 1 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) ∷
   rw 0 (q33 c4) ∷ []) Eq.refl

private
  q53 : WsL → Eqn
  q53 c4 = eqn (Sw12 ∷ Bx2-43 ∷ []) (Bx2-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ))

-- nat 1 BOX(2;43): 2 steps
lem-nat-1-BOX⟨2·43⟩ : WsL → ⟪ (Sw12 ∷ Bx2-43 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-43 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·43⟩ c4 = derive (Sw12 ∷ Bx2-43 ∷ []) (Bx1-43 ∷ Sw12 ∷ [])
  (rw 0 (q53 c4) ∷
   re 0 1 (Bx1-43 ∷ []) ∷ []) Eq.refl

private
  q54 : WsL → Eqn
  q54 c4 = eqn (CCZ124 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ124 ∷ []) (wl0078 c4)
  q55 : WsL → Eqn
  q55 c4 = eqn (Sw12 ∷ Toff412 ∷ []) (Toff412 ∷ Sw12 ∷ []) (wl0079 c4)
  q56 : WsL → Eqn
  q56 c4 = eqn (Sw12 ∷ Bx2-43 ∷ []) (Bx1-43 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·43⟩ c4)

-- nat 1 BOX(4;213): 8 steps
lem-nat-1-BOX⟨4·213⟩ : WsL → ⟪ (Sw12 ∷ Bx4-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-123 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨4·213⟩ c4 = derive (Sw12 ∷ Bx4-213 ∷ []) (Bx4-123 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) ∷
   rw⁻ 0 (q54 c4) ∷
   rw 1 (q55 c4) ∷
   rw 2 (q56 c4) ∷
   rw 3 (q55 c4) ∷
   rw⁻ 4 (q54 c4) ∷
   rw 5 (q56 c4) ∷
   re 0 6 (Bx4-123 ∷ []) ∷ []) Eq.refl

private
  q57 : WsL → Eqn
  q57 c4 = eqn (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4)
  q58 : WsL → Eqn
  q58 c4 = eqn (Sw12 ∷ Toff204 ∷ []) (Toff104 ∷ Sw12 ∷ []) (lem-nat-1-TOFF204 c4)
  q59 : WsL → Eqn
  q59 c4 = eqn (Sw12 ∷ Bx4-213 ∷ []) (Bx4-123 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨4·213⟩ c4)

-- nat 1 BOX(2;4013): 8 steps
lem-nat-1-BOX⟨2·4013⟩ : WsL → ⟪ (Sw12 ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-4023 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·4013⟩ c4 = derive (Sw12 ∷ Bx2-4013 ∷ []) (Bx1-4023 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ []) ∷
   rw 0 (q57 c4) ∷
   rw 1 (q58 c4) ∷
   rw 2 (q59 c4) ∷
   rw 3 (q58 c4) ∷
   rw 4 (q57 c4) ∷
   rw 5 (q59 c4) ∷
   re 0 6 (Bx1-4023 ∷ []) ∷ []) Eq.refl

-- nat 1 TOFF104: 2 steps
lem-nat-1-TOFF104 : WsL → ⟪ (Sw12 ∷ Toff104 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-TOFF104 c4 = derive (Sw12 ∷ Toff104 ∷ []) (Toff204 ∷ Sw12 ∷ [])
  (rw⁻ 2 (q33 c4) ∷
   re 0 3 (Toff204 ∷ []) ∷ []) Eq.refl

-- nat 2 TOFF413: 2 steps
lem-nat-2-TOFF413 : WsL → ⟪ (Sw23 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-TOFF413 c4 = derive (Sw23 ∷ Toff413 ∷ []) (Toff412 ∷ Sw23 ∷ [])
  (re 1 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 0 (q4 c4) ∷ []) Eq.refl

private
  q60 : WsL → Eqn
  q60 c4 = eqn (CZ34 ∷ Sw23 ∷ []) (Sw23 ∷ CZ24 ∷ []) (wl0028 c4)

-- nat 2 BOX(3;42): 3 steps
lem-nat-2-BOX⟨3·42⟩ : WsL → ⟪ (Sw23 ∷ Bx3-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-43 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·42⟩ c4 = derive (Sw23 ∷ Bx3-42 ∷ []) (Bx2-43 ∷ Sw23 ∷ [])
  (re 1 1 (CZ24 ∷ []) ∷
   rw⁻ 0 (q60 c4) ∷
   re 0 1 (Bx2-43 ∷ []) ∷ []) Eq.refl

private
  q61 : WsL → Eqn
  q61 c4 = eqn (Sw23 ∷ CCZ134 ∷ []) (CCZ124 ∷ Sw23 ∷ []) (lem-nat-2-CCZ134 c4)
  q62 : WsL → Eqn
  q62 c4 = eqn (Sw23 ∷ Toff413 ∷ []) (Toff412 ∷ Sw23 ∷ []) (lem-nat-2-TOFF413 c4)
  q63 : WsL → Eqn
  q63 c4 = eqn (Sw23 ∷ Bx3-42 ∷ []) (Bx2-43 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨3·42⟩ c4)

-- nat 2 BOX(4;312): 8 steps
lem-nat-2-BOX⟨4·312⟩ : WsL → ⟪ (Sw23 ∷ Bx4-312 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-213 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨4·312⟩ c4 = derive (Sw23 ∷ Bx4-312 ∷ []) (Bx4-213 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) ∷
   rw 0 (q61 c4) ∷
   rw 1 (q62 c4) ∷
   rw 2 (q63 c4) ∷
   rw 3 (q62 c4) ∷
   rw 4 (q61 c4) ∷
   rw 5 (q63 c4) ∷
   re 0 6 (Bx4-213 ∷ []) ∷ []) Eq.refl

private
  q64 : WsL → Eqn
  q64 c4 = eqn (Sw23 ∷ CCZ034 ∷ []) (CCZ024 ∷ Sw23 ∷ []) (lem-nat-2-CCZ034 c4)
  q65 : WsL → Eqn
  q65 c4 = eqn (Sw23 ∷ Toff304 ∷ []) (Toff204 ∷ Sw23 ∷ []) (lem-nat-2-TOFF304 c4)
  q66 : WsL → Eqn
  q66 c4 = eqn (Sw23 ∷ Bx4-312 ∷ []) (Bx4-213 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨4·312⟩ c4)

-- nat 2 BOX(3;4012): 8 steps
lem-nat-2-BOX⟨3·4012⟩ : WsL → ⟪ (Sw23 ∷ Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨3·4012⟩ c4 = derive (Sw23 ∷ Bx3-4012 ∷ []) (Bx2-4013 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ []) ∷
   rw 0 (q64 c4) ∷
   rw 1 (q65 c4) ∷
   rw 2 (q66 c4) ∷
   rw 3 (q65 c4) ∷
   rw 4 (q64 c4) ∷
   rw 5 (q66 c4) ∷
   re 0 6 (Bx2-4013 ∷ []) ∷ []) Eq.refl

private
  q67 : WsL → Eqn
  q67 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl0011 c4)
  q68 : WsL → Eqn
  q68 c4 = eqn (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) (wl0012 c4)
  q69 : WsL → Eqn
  q69 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl0021 c4)
  q70 : WsL → Eqn
  q70 c4 = eqn (Sw01 ∷ CS34 ∷ []) (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))
  q71 : WsL → Eqn
  q71 c4 = eqn (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) (wl0020 c4)
  q72 : WsL → Eqn
  q72 c4 = eqn (Sw01 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑))
  q73 : WsL → Eqn
  q73 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl0015 c4)
  q74 : WsL → Eqn
  q74 c4 = eqn (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) (wl0016 c4)
  q75 : WsL → Eqn
  q75 c4 = eqn (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4)
  q76 : WsL → Eqn
  q76 c4 = eqn (CS01 ∷ Sw34 ∷ []) (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑))

-- nat 0 CCZ134: 78 steps
lem-nat-0-CCZ134 : WsL → ⟪ (Sw01 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CCZ134 c4 = derive (Sw01 ∷ CCZ134 ∷ []) (CCZ034 ∷ Sw01 ∷ [])
  (re 1 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   re 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (CS24 ∷ []) ∷
   rw⁻ 3 (q26 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CS24⁻ ∷ []) ∷
   rw⁻ 5 (q26 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 6 3 (CS14 ∷ []) ∷
   rw 7 (q6 c4) ∷
   rw⁻ 1 (q67 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   re 2 3 (CX13 ∷ []) ∷
   rw⁻ 3 (q68 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   re 4 3 (CX13 ∷ []) ∷
   rw⁻ 5 (q69 c4) ∷
   rw 6 (q4 c4) ∷
   rw 0 (q70 c4) ∷
   rw⁻ 1 (q71 c4) ∷
   rw 2 (q72 c4) ∷
   rw⁻ 3 (q71 c4) ∷
   re 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 4 (q8 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   rw 6 (q8 c4) ∷
   re 4 3 (CS04 ∷ []) ∷
   rw⁻ 0 (q4 c4) ∷
   rw⁻ 1 (q73 c4) ∷
   re 3 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 2 (q4 c4) ∷
   rw⁻ 3 (q74 c4) ∷
   re 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 4 (q4 c4) ∷
   re 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q75 c4) ∷
   rw⁻ 7 (q37 c4) ∷
   rw⁻ 8 (q76 c4) ∷
   rw⁻ 9 (q37 c4) ∷
   rw⁻ 10 (q75 c4) ∷
   re 5 7 (CS04 ∷ []) ∷
   rw⁻ 1 (q33 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 3 (q33 c4) ∷
   rw⁻ 4 (q36 c4) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 (q33 c4) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q37 c4) ∷
   rw⁻ 7 (q38 c4) ∷
   rw 8 (q37 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 2 (q6 c4) ∷
   re 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   re 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q6 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 (q4 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q4 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 (q4 c4) ∷
   re 4 5 (CCZ012 ∷ []) ∷
   re 3 3 (CCZ013 ∷ []) ∷
   re 2 3 (CCZ014 ∷ []) ∷
   re 1 3 (CCZ024 ∷ []) ∷
   re 0 3 (CCZ034 ∷ []) ∷ []) Eq.refl

private
  q77 : WsL → Eqn
  q77 c4 = eqn (K2 ∷ Sw34 ∷ []) (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap))
  q78 : WsL → Eqn
  q78 c4 = eqn (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ []) (wl0057 c4)
  q79 : WsL → Eqn
  q79 c4 = eqn (Sw01 ∷ K3 ∷ []) (K3 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑))
  q80 : WsL → Eqn
  q80 c4 = eqn (K1 ∷ Sw12 ∷ []) (Sw12 ∷ K2 ∷ []) (wl0062 c4)
  q81 : WsL → Eqn
  q81 c4 = eqn (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι1 ∷ []) (wl0080 c4)

-- nat 0 TOFF314: 100 steps
lem-nat-0-TOFF314 : WsL → ⟪ (Sw01 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF314 c4 = derive (Sw01 ∷ Toff314 ∷ []) (Toff304 ∷ Sw01 ∷ [])
  (re 1 1 (Sw23 ∷ Toff214 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) ∷
   re 3 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw⁻ 2 (q77 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (CS24 ∷ []) ∷
   rw⁻ 4 (q26 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (CS24⁻ ∷ []) ∷
   rw⁻ 6 (q26 c4) ∷
   rw⁻ 9 (q6 c4) ∷
   re 7 3 (CS14 ∷ []) ∷
   rw⁻ 8 (q77 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw 10 (q6 c4) ∷
   rw⁻ 1 (q78 c4) ∷
   rw⁻ 2 (q67 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 3 3 (CX13 ∷ []) ∷
   rw⁻ 4 (q68 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   re 5 3 (CX13 ∷ []) ∷
   rw⁻ 6 (q69 c4) ∷
   rw⁻ 7 (q78 c4) ∷
   rw⁻ 8 (q42 c4) ∷
   rw 9 (q4 c4) ∷
   rw 0 (q79 c4) ∷
   rw 1 (q70 c4) ∷
   rw⁻ 2 (q71 c4) ∷
   rw 3 (q72 c4) ∷
   rw⁻ 4 (q71 c4) ∷
   re 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 5 (q8 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   rw 7 (q8 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw 6 (q79 c4) ∷
   rw 7 (q32 c4) ∷
   rw⁻ 0 (q4 c4) ∷
   rw⁻ 1 (q41 c4) ∷
   rw⁻ 2 (q73 c4) ∷
   re 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 3 (q4 c4) ∷
   rw⁻ 4 (q74 c4) ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 5 (q4 c4) ∷
   re 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 6 (q75 c4) ∷
   rw⁻ 8 (q37 c4) ∷
   rw⁻ 9 (q76 c4) ∷
   rw⁻ 10 (q37 c4) ∷
   rw⁻ 11 (q75 c4) ∷
   re 6 7 (CS04 ∷ []) ∷
   rw⁻ 7 (q41 c4) ∷
   rw⁻ 8 (q42 c4) ∷
   rw⁻ 1 (q33 c4) ∷
   rw⁻ 2 (q80 c4) ∷
   rw⁻ 3 (q35 c4) ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 (q33 c4) ∷
   rw⁻ 5 (q36 c4) ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 (q33 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q37 c4) ∷
   rw⁻ 8 (q38 c4) ∷
   rw 9 (q37 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q80 c4) ∷
   rw 9 (q39 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw⁻ 3 (q18 c4) ∷
   re 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   re 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 8 (q6 c4) ∷
   rw⁻ 9 (q18 c4) ∷
   rw⁻ 10 (q27 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 4 (q16 c4) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 (q4 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 (q4 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 (q4 c4) ∷
   rw⁻ 10 (q16 c4) ∷
   rw⁻ 11 (q42 c4) ∷
   rw⁻ 4 (q81 c4) ∷
   re 4 8 (Toff102 ∷ []) ∷
   re 3 3 (Toff103 ∷ []) ∷
   re 2 3 (Toff104 ∷ []) ∷
   re 1 3 (Toff204 ∷ []) ∷
   re 0 3 (Toff304 ∷ []) ∷ []) Eq.refl

private
  q82 : WsL → Eqn
  q82 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0008 c4)
  q83 : WsL → Eqn
  q83 c4 = eqn (CS24⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS14⁻ ∷ []) (wl0009 c4)
  q84 : WsL → Eqn
  q84 c4 = eqn (CX13 ∷ Sw01 ∷ []) (Sw01 ∷ CX03 ∷ []) (wl0081 c4)

-- nat 0 CCZ034: 78 steps
lem-nat-0-CCZ034 : WsL → ⟪ (Sw01 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-CCZ034 c4 = derive (Sw01 ∷ CCZ034 ∷ []) (CCZ134 ∷ Sw01 ∷ [])
  (re 1 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   re 3 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw⁻ 6 (q4 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q5 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 (q4 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q7 c4) ∷
   rw⁻ 9 (q6 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw 8 (q6 c4) ∷
   rw⁻ 2 (q82 c4) ∷
   rw⁻ 5 (q33 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q83 c4) ∷
   rw⁻ 7 (q33 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q37 c4) ∷
   rw⁻ 7 (q38 c4) ∷
   rw 8 (q37 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw 7 (q33 c4) ∷
   rw⁻ 1 (q67 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   re 2 3 (CX03 ∷ []) ∷
   rw⁻ 3 (q68 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   re 4 3 (CX03 ∷ []) ∷
   re 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q75 c4) ∷
   rw⁻ 7 (q37 c4) ∷
   rw⁻ 8 (q76 c4) ∷
   rw⁻ 9 (q37 c4) ∷
   rw⁻ 10 (q75 c4) ∷
   re 5 7 (CS04 ∷ []) ∷
   rw 6 (q4 c4) ∷
   rw 0 (q70 c4) ∷
   rw⁻ 1 (q84 c4) ∷
   rw 2 (q72 c4) ∷
   rw⁻ 3 (q84 c4) ∷
   re 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 4 (q8 c4) ∷
   rw⁻ 5 (q12 c4) ∷
   rw 6 (q8 c4) ∷
   re 4 3 (CS14 ∷ []) ∷
   rw⁻ 0 (q4 c4) ∷
   rw⁻ 1 (q73 c4) ∷
   re 3 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 2 (q4 c4) ∷
   rw⁻ 3 (q74 c4) ∷
   re 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 4 (q4 c4) ∷
   rw⁻ 5 (q69 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   re 3 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 2 (q6 c4) ∷
   rw⁻ 3 (q26 c4) ∷
   re 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q26 c4) ∷
   re 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   re 2 5 (CCZ123 ∷ []) ∷
   re 1 3 (CCZ124 ∷ []) ∷
   re 0 3 (CCZ134 ∷ []) ∷ []) Eq.refl

private
  q85 : WsL → Eqn
  q85 c4 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap))
  q86 : WsL → Eqn
  q86 c4 = eqn (Sw23 ∷ K4 ∷ []) (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K))
  q87 : WsL → Eqn
  q87 c4 = eqn (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (wl0082 c4)

-- nat 0 TOFF403: 100 steps
lem-nat-0-TOFF403 : WsL → ⟪ (Sw01 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF403 c4 = derive (Sw01 ∷ Toff403 ∷ []) (Toff413 ∷ Sw01 ∷ [])
  (re 1 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) ∷
   re 3 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) ∷
   re 4 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 5 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw⁻ 4 (q78 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 (q5 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 (q78 c4) ∷
   rw⁻ 11 (q17 c4) ∷
   rw 12 (q4 c4) ∷
   rw⁻ 3 (q25 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CS14 ∷ []) ∷
   rw⁻ 5 (q7 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 6 3 (CS14⁻ ∷ []) ∷
   rw⁻ 7 (q7 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   re 8 3 (CS04 ∷ []) ∷
   rw⁻ 9 (q25 c4) ∷
   rw⁻ 10 (q19 c4) ∷
   rw 11 (q6 c4) ∷
   rw 2 (q34 c4) ∷
   rw⁻ 3 (q82 c4) ∷
   rw⁻ 6 (q33 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw⁻ 5 (q83 c4) ∷
   rw⁻ 8 (q33 c4) ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q37 c4) ∷
   rw⁻ 8 (q38 c4) ∷
   rw 9 (q37 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw 8 (q34 c4) ∷
   rw⁻ 9 (q85 c4) ∷
   rw 10 (q33 c4) ∷
   rw 1 (q86 c4) ∷
   rw⁻ 2 (q67 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 3 3 (CX03 ∷ []) ∷
   rw⁻ 4 (q68 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   re 5 3 (CX03 ∷ []) ∷
   re 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 6 (q75 c4) ∷
   rw⁻ 8 (q37 c4) ∷
   rw⁻ 9 (q76 c4) ∷
   rw⁻ 10 (q37 c4) ∷
   rw⁻ 11 (q75 c4) ∷
   re 6 7 (CS04 ∷ []) ∷
   rw 7 (q86 c4) ∷
   rw⁻ 8 (q17 c4) ∷
   rw 9 (q4 c4) ∷
   rw 0 (q28 c4) ∷
   rw 1 (q70 c4) ∷
   rw⁻ 2 (q84 c4) ∷
   rw 3 (q72 c4) ∷
   rw⁻ 4 (q84 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q8 c4) ∷
   rw⁻ 6 (q12 c4) ∷
   rw 7 (q8 c4) ∷
   re 5 3 (CS14 ∷ []) ∷
   rw 6 (q28 c4) ∷
   rw 7 (q21 c4) ∷
   rw⁻ 0 (q4 c4) ∷
   rw 1 (q86 c4) ∷
   rw⁻ 2 (q73 c4) ∷
   re 4 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 3 (q4 c4) ∷
   rw⁻ 4 (q74 c4) ∷
   re 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 5 (q4 c4) ∷
   rw⁻ 6 (q69 c4) ∷
   rw 7 (q86 c4) ∷
   rw⁻ 8 (q17 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw⁻ 2 (q40 c4) ∷
   re 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q26 c4) ∷
   re 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q26 c4) ∷
   re 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 7 (q6 c4) ∷
   rw⁻ 8 (q40 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw 2 (q87 c4) ∷
   re 2 8 (Toff312 ∷ []) ∷
   re 1 3 (Toff412 ∷ []) ∷
   re 0 3 (Toff413 ∷ []) ∷ []) Eq.refl

private
  q88 : WsL → Eqn
  q88 c4 = eqn (Sw01 ∷ CCZ034 ∷ []) (CCZ134 ∷ Sw01 ∷ []) (lem-nat-0-CCZ034 c4)
  q89 : WsL → Eqn
  q89 c4 = eqn (Sw01 ∷ Toff403 ∷ []) (Toff413 ∷ Sw01 ∷ []) (lem-nat-0-TOFF403 c4)
  q90 : WsL → Eqn
  q90 c4 = eqn (Sw01 ∷ Bx3-42 ∷ []) (Bx3-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑))

-- nat 0 BOX(4;302): 8 steps
lem-nat-0-BOX⟨4·302⟩ : WsL → ⟪ (Sw01 ∷ Bx4-302 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-312 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·302⟩ c4 = derive (Sw01 ∷ Bx4-302 ∷ []) (Bx4-312 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) ∷
   rw 0 (q88 c4) ∷
   rw 1 (q89 c4) ∷
   rw 2 (q90 c4) ∷
   rw 3 (q89 c4) ∷
   rw 4 (q88 c4) ∷
   rw 5 (q90 c4) ∷
   re 0 6 (Bx4-312 ∷ []) ∷ []) Eq.refl

private
  q91 : WsL → Eqn
  q91 c4 = eqn (Sw01 ∷ CCZ134 ∷ []) (CCZ034 ∷ Sw01 ∷ []) (lem-nat-0-CCZ134 c4)
  q92 : WsL → Eqn
  q92 c4 = eqn (Sw01 ∷ Toff314 ∷ []) (Toff304 ∷ Sw01 ∷ []) (lem-nat-0-TOFF314 c4)
  q93 : WsL → Eqn
  q93 c4 = eqn (Sw01 ∷ Bx4-302 ∷ []) (Bx4-312 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨4·302⟩ c4)

-- nat 0 BOX(3;4102): 8 steps
lem-nat-0-BOX⟨3·4102⟩ : WsL → ⟪ (Sw01 ∷ Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·4102⟩ c4 = derive (Sw01 ∷ Bx3-4102 ∷ []) (Bx3-4012 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff314 ∷ Bx4-302 ∷ Toff314 ∷ CCZ134 ∷ Bx4-302 ∷ []) ∷
   rw 0 (q91 c4) ∷
   rw 1 (q92 c4) ∷
   rw 2 (q93 c4) ∷
   rw 3 (q92 c4) ∷
   rw 4 (q91 c4) ∷
   rw 5 (q93 c4) ∷
   re 0 6 (Bx3-4012 ∷ []) ∷ []) Eq.refl

private
  q94 : WsL → Eqn
  q94 c4 = eqn (K2 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ []) (wl0056 c4)
  q95 : WsL → Eqn
  q95 c4 = eqn (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (wl0059 c4)

-- nat 0 TOFF304: 100 steps
lem-nat-0-TOFF304 : WsL → ⟪ (Sw01 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF304 c4 = derive (Sw01 ∷ Toff304 ∷ []) (Toff314 ∷ Sw01 ∷ [])
  (re 1 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) ∷
   re 3 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) ∷
   re 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 4 (q16 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 (q5 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 (q16 c4) ∷
   rw⁻ 11 (q17 c4) ∷
   rw 12 (q4 c4) ∷
   rw⁻ 3 (q18 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CS14 ∷ []) ∷
   rw⁻ 5 (q7 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 6 3 (CS14⁻ ∷ []) ∷
   rw⁻ 7 (q7 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   re 8 3 (CS04 ∷ []) ∷
   rw⁻ 9 (q18 c4) ∷
   rw⁻ 10 (q19 c4) ∷
   rw 11 (q6 c4) ∷
   rw⁻ 2 (q94 c4) ∷
   rw⁻ 3 (q82 c4) ∷
   rw⁻ 6 (q33 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw⁻ 5 (q83 c4) ∷
   rw⁻ 8 (q33 c4) ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q37 c4) ∷
   rw⁻ 8 (q38 c4) ∷
   rw 9 (q37 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q94 c4) ∷
   rw⁻ 9 (q85 c4) ∷
   rw 10 (q33 c4) ∷
   rw⁻ 1 (q78 c4) ∷
   rw⁻ 2 (q67 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 3 3 (CX03 ∷ []) ∷
   rw⁻ 4 (q68 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   re 5 3 (CX03 ∷ []) ∷
   re 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 6 (q75 c4) ∷
   rw⁻ 8 (q37 c4) ∷
   rw⁻ 9 (q76 c4) ∷
   rw⁻ 10 (q37 c4) ∷
   rw⁻ 11 (q75 c4) ∷
   re 6 7 (CS04 ∷ []) ∷
   rw⁻ 7 (q78 c4) ∷
   rw⁻ 8 (q17 c4) ∷
   rw 9 (q4 c4) ∷
   rw 0 (q79 c4) ∷
   rw 1 (q70 c4) ∷
   rw⁻ 2 (q84 c4) ∷
   rw 3 (q72 c4) ∷
   rw⁻ 4 (q84 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q8 c4) ∷
   rw⁻ 6 (q12 c4) ∷
   rw 7 (q8 c4) ∷
   re 5 3 (CS14 ∷ []) ∷
   rw 6 (q79 c4) ∷
   rw 7 (q21 c4) ∷
   rw⁻ 0 (q4 c4) ∷
   rw⁻ 1 (q41 c4) ∷
   rw⁻ 2 (q73 c4) ∷
   re 4 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 3 (q4 c4) ∷
   rw⁻ 4 (q74 c4) ∷
   re 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 5 (q4 c4) ∷
   rw⁻ 6 (q69 c4) ∷
   rw⁻ 7 (q41 c4) ∷
   rw⁻ 8 (q17 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw⁻ 2 (q77 c4) ∷
   re 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q26 c4) ∷
   re 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q26 c4) ∷
   re 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 7 (q6 c4) ∷
   rw⁻ 8 (q77 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw 2 (q95 c4) ∷
   re 2 8 (Toff213 ∷ []) ∷
   re 1 3 (Toff214 ∷ []) ∷
   re 0 3 (Toff314 ∷ []) ∷ []) Eq.refl

private
  q96 : WsL → Eqn
  q96 c4 = eqn (Sw12 ∷ CCZ014 ∷ []) (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4)
  q97 : WsL → Eqn
  q97 c4 = eqn (Sw12 ∷ Toff104 ∷ []) (Toff204 ∷ Sw12 ∷ []) (lem-nat-1-TOFF104 c4)
  q98 : WsL → Eqn
  q98 c4 = eqn (Sw12 ∷ Bx0-13 ∷ []) (Bx0-23 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·13⟩ c4)

-- nat 1 BOX(1;043): 8 steps
lem-nat-1-BOX⟨1·043⟩ : WsL → ⟪ (Sw12 ∷ Bx1-043 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-043 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·043⟩ c4 = derive (Sw12 ∷ Bx1-043 ∷ []) (Bx2-043 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff104 ∷ Bx0-13 ∷ Toff104 ∷ CCZ014 ∷ Bx0-13 ∷ []) ∷
   rw 0 (q96 c4) ∷
   rw 1 (q97 c4) ∷
   rw 2 (q98 c4) ∷
   rw 3 (q97 c4) ∷
   rw 4 (q96 c4) ∷
   rw 5 (q98 c4) ∷
   re 0 6 (Bx2-043 ∷ []) ∷ []) Eq.refl

private
  q99 : WsL → Eqn
  q99 c4 = eqn (CCZ012 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ012 ∷ []) (wl0037 c4)
  q100 : WsL → Eqn
  q100 c4 = eqn (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) (wl0038 c4)
  q101 : WsL → Eqn
  q101 c4 = eqn (Sw12 ∷ Bx1-043 ∷ []) (Bx2-043 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·043⟩ c4)

-- nat 1 BOX(0;1243): 8 steps
lem-nat-1-BOX⟨0·1243⟩ : WsL → ⟪ (Sw12 ∷ Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·1243⟩ c4 = derive (Sw12 ∷ Bx0-1243 ∷ []) (Bx0-2143 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-043 ∷ Toff012 ∷ CCZ012 ∷ Bx1-043 ∷ []) ∷
   rw⁻ 0 (q99 c4) ∷
   rw 1 (q100 c4) ∷
   rw 2 (q101 c4) ∷
   rw 3 (q100 c4) ∷
   rw⁻ 4 (q99 c4) ∷
   rw 5 (q101 c4) ∷
   re 0 6 (Bx0-2143 ∷ []) ∷ []) Eq.refl

private
  q102 : WsL → Eqn
  q102 c4 = eqn (Sw23 ∷ CCZ024 ∷ []) (CCZ034 ∷ Sw23 ∷ []) (lem-nat-2-CCZ024 c4)
  q103 : WsL → Eqn
  q103 c4 = eqn (Sw23 ∷ Toff204 ∷ []) (Toff304 ∷ Sw23 ∷ []) (lem-nat-2-TOFF204 c4)
  q104 : WsL → Eqn
  q104 c4 = eqn (Sw23 ∷ Bx0-23 ∷ []) (Bx0-32 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·23⟩ c4)

-- nat 2 BOX(2;043): 8 steps
lem-nat-2-BOX⟨2·043⟩ : WsL → ⟪ (Sw23 ∷ Bx2-043 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-042 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨2·043⟩ c4 = derive (Sw23 ∷ Bx2-043 ∷ []) (Bx3-042 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ []) ∷
   rw 0 (q102 c4) ∷
   rw 1 (q103 c4) ∷
   rw 2 (q104 c4) ∷
   rw 3 (q103 c4) ∷
   rw 4 (q102 c4) ∷
   rw 5 (q104 c4) ∷
   re 0 6 (Bx3-042 ∷ []) ∷ []) Eq.refl

private
  q105 : WsL → Eqn
  q105 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4)
  q106 : WsL → Eqn
  q106 c4 = eqn (Sw23 ∷ Toff012 ∷ []) (Toff013 ∷ Sw23 ∷ []) (lem-nat-2-TOFF012 c4)
  q107 : WsL → Eqn
  q107 c4 = eqn (Sw23 ∷ Bx2-043 ∷ []) (Bx3-042 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨2·043⟩ c4)

-- nat 2 BOX(0;2143): 8 steps
lem-nat-2-BOX⟨0·2143⟩ : WsL → ⟪ (Sw23 ∷ Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·2143⟩ c4 = derive (Sw23 ∷ Bx0-2143 ∷ []) (Bx0-3142 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-043 ∷ Toff012 ∷ CCZ012 ∷ Bx2-043 ∷ []) ∷
   rw 0 (q105 c4) ∷
   rw 1 (q106 c4) ∷
   rw 2 (q107 c4) ∷
   rw 3 (q106 c4) ∷
   rw 4 (q105 c4) ∷
   rw 5 (q107 c4) ∷
   re 0 6 (Bx0-3142 ∷ []) ∷ []) Eq.refl

private
  q108 : WsL → Eqn
  q108 c4 = eqn (CS34 ∷ Sw34 ∷ []) (Sw34 ∷ CS34 ∷ []) (wl0039 c4)
  q109 : WsL → Eqn
  q109 c4 = eqn (CS34⁻ ∷ Sw34 ∷ []) (Sw34 ∷ CS34⁻ ∷ []) (wl0040 c4)
  q110 : WsL → Eqn
  q110 c4 = eqn (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) (wl0014 c4)
  q111 : WsL → Eqn
  q111 c4 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (c₂ (CS) (Swap))
  q112 : WsL → Eqn
  q112 c4 = eqn (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K2 ∷ ι ∷ []) (wl0083 c4)

-- nat 3 TOFF304: 144 steps
lem-nat-3-TOFF304 : WsL → ⟪ (Sw34 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF304 c4 = derive (Sw34 ∷ Toff304 ∷ []) (Toff403 ∷ Sw34 ∷ [])
  (re 1 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) ∷
   re 3 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) ∷
   re 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 4 (q16 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 (q5 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 (q5 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 (q16 c4) ∷
   rw⁻ 11 (q17 c4) ∷
   rw 12 (q4 c4) ∷
   rw⁻ 3 (q18 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CS14 ∷ []) ∷
   rw⁻ 5 (q7 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 6 3 (CS14⁻ ∷ []) ∷
   rw⁻ 7 (q7 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   re 8 3 (CS04 ∷ []) ∷
   rw⁻ 9 (q18 c4) ∷
   rw⁻ 10 (q19 c4) ∷
   rw 11 (q6 c4) ∷
   rw⁻ 2 (q94 c4) ∷
   rw⁻ 3 (q82 c4) ∷
   rw⁻ 6 (q33 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw⁻ 5 (q83 c4) ∷
   rw⁻ 8 (q33 c4) ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q37 c4) ∷
   rw⁻ 8 (q38 c4) ∷
   rw 9 (q37 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q94 c4) ∷
   rw⁻ 9 (q85 c4) ∷
   rw 10 (q33 c4) ∷
   rw⁻ 1 (q78 c4) ∷
   rw⁻ 2 (q67 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 3 3 (CX03 ∷ []) ∷
   rw⁻ 4 (q68 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   re 5 3 (CX03 ∷ []) ∷
   re 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 6 (q75 c4) ∷
   rw⁻ 8 (q37 c4) ∷
   rw⁻ 9 (q76 c4) ∷
   rw⁻ 10 (q37 c4) ∷
   rw⁻ 11 (q75 c4) ∷
   re 6 7 (CS04 ∷ []) ∷
   rw⁻ 7 (q78 c4) ∷
   rw⁻ 8 (q17 c4) ∷
   rw 9 (q4 c4) ∷
   rw⁻ 0 (q25 c4) ∷
   rw⁻ 1 (q108 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (CX04 ∷ []) ∷
   rw⁻ 3 (q109 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CX04 ∷ []) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q25 c4) ∷
   rw⁻ 7 (q19 c4) ∷
   rw⁻ 0 (q4 c4) ∷
   rw 1 (q86 c4) ∷
   rw⁻ 2 (q73 c4) ∷
   re 4 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 3 (q75 c4) ∷
   rw⁻ 5 (q37 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   rw⁻ 7 (q37 c4) ∷
   rw⁻ 8 (q75 c4) ∷
   re 3 7 (CX04 ∷ []) ∷
   rw⁻ 4 (q74 c4) ∷
   re 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q75 c4) ∷
   rw⁻ 7 (q37 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   rw⁻ 9 (q37 c4) ∷
   rw⁻ 10 (q75 c4) ∷
   re 5 7 (CX04 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 (q4 c4) ∷
   rw 7 (q86 c4) ∷
   rw⁻ 8 (q17 c4) ∷
   rw⁻ 1 (q33 c4) ∷
   rw 2 (q34 c4) ∷
   rw⁻ 3 (q35 c4) ∷
   re 5 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 4 (q37 c4) ∷
   rw⁻ 5 (q110 c4) ∷
   rw 6 (q37 c4) ∷
   re 4 3 (CX04 ∷ []) ∷
   rw⁻ 5 (q36 c4) ∷
   re 7 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 6 (q37 c4) ∷
   rw⁻ 7 (q110 c4) ∷
   rw 8 (q37 c4) ∷
   re 6 3 (CX04 ∷ []) ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 7 (q33 c4) ∷
   rw 8 (q34 c4) ∷
   rw⁻ 9 (q85 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw⁻ 3 (q40 c4) ∷
   re 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 4 (q6 c4) ∷
   re 6 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   re 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   re 8 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 7 (q6 c4) ∷
   rw⁻ 8 (q76 c4) ∷
   rw⁻ 9 (q40 c4) ∷
   rw⁻ 10 (q19 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 4 (q41 c4) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 (q4 c4) ∷
   re 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 6 (q4 c4) ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 (q4 c4) ∷
   re 9 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 8 (q4 c4) ∷
   rw⁻ 9 (q111 c4) ∷
   rw⁻ 10 (q41 c4) ∷
   rw⁻ 11 (q17 c4) ∷
   rw⁻ 4 (q112 c4) ∷
   re 4 8 (Toff201 ∷ []) ∷
   re 3 3 (Toff301 ∷ []) ∷
   re 2 3 (Toff401 ∷ []) ∷
   re 1 3 (Toff402 ∷ []) ∷
   re 0 3 (Toff403 ∷ []) ∷ []) Eq.refl

-- nat 3 CZ23: 2 steps
lem-nat-3-CZ23 : WsL → ⟪ (Sw34 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ24 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-CZ23 c4 = derive (Sw34 ∷ CZ23 ∷ []) (CZ24 ∷ Sw34 ∷ [])
  (rw⁻ 2 (q6 c4) ∷
   re 0 3 (CZ24 ∷ []) ∷ []) Eq.refl

private
  q113 : WsL → Eqn
  q113 c4 = eqn (Sw34 ∷ CZ23 ∷ []) (CZ24 ∷ Sw34 ∷ []) (lem-nat-3-CZ23 c4)

-- nat 3 BOX(0;32): 3 steps
lem-nat-3-BOX⟨0·32⟩ : WsL → ⟪ (Sw34 ∷ Bx0-32 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-42 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·32⟩ c4 = derive (Sw34 ∷ Bx0-32 ∷ []) (Bx0-42 ∷ Sw34 ∷ [])
  (re 1 1 (CZ23 ∷ []) ∷
   rw 0 (q113 c4) ∷
   re 0 1 (Bx0-42 ∷ []) ∷ []) Eq.refl

private
  q114 : WsL → Eqn
  q114 c4 = eqn (Sw34 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw34 ∷ []) (lem-nat-3-CCZ034 c4)
  q115 : WsL → Eqn
  q115 c4 = eqn (Sw34 ∷ Toff304 ∷ []) (Toff403 ∷ Sw34 ∷ []) (lem-nat-3-TOFF304 c4)
  q116 : WsL → Eqn
  q116 c4 = eqn (Sw34 ∷ Bx0-32 ∷ []) (Bx0-42 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨0·32⟩ c4)

-- nat 3 BOX(3;042): 8 steps
lem-nat-3-BOX⟨3·042⟩ : WsL → ⟪ (Sw34 ∷ Bx3-042 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-032 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨3·042⟩ c4 = derive (Sw34 ∷ Bx3-042 ∷ []) (Bx4-032 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) ∷
   rw 0 (q114 c4) ∷
   rw 1 (q115 c4) ∷
   rw 2 (q116 c4) ∷
   rw 3 (q115 c4) ∷
   rw 4 (q114 c4) ∷
   rw 5 (q116 c4) ∷
   re 0 6 (Bx4-032 ∷ []) ∷ []) Eq.refl

private
  q117 : WsL → Eqn
  q117 c4 = eqn (Sw34 ∷ CCZ013 ∷ []) (CCZ014 ∷ Sw34 ∷ []) (lem-nat-3-CCZ013 c4)
  q118 : WsL → Eqn
  q118 c4 = eqn (Sw34 ∷ Toff013 ∷ []) (Toff014 ∷ Sw34 ∷ []) (lem-nat-3-TOFF013 c4)
  q119 : WsL → Eqn
  q119 c4 = eqn (Sw34 ∷ Bx3-042 ∷ []) (Bx4-032 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨3·042⟩ c4)

-- nat 3 BOX(0;3142): 8 steps
lem-nat-3-BOX⟨0·3142⟩ : WsL → ⟪ (Sw34 ∷ Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨0·3142⟩ c4 = derive (Sw34 ∷ Bx0-3142 ∷ []) (Bx0-4132 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) ∷
   rw 0 (q117 c4) ∷
   rw 1 (q118 c4) ∷
   rw 2 (q119 c4) ∷
   rw 3 (q118 c4) ∷
   rw 4 (q117 c4) ∷
   rw 5 (q119 c4) ∷
   re 0 6 (Bx0-4132 ∷ []) ∷ []) Eq.refl

private
  q120 : WsL → Eqn
  q120 c4 = eqn (Sw01 ∷ Bx0-42 ∷ []) (Bx0-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑))

-- nat 0 BOX(0;42): 2 steps
lem-nat-0-BOX⟨0·42⟩ : WsL → ⟪ (Sw01 ∷ Bx0-42 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-42 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·42⟩ c4 = derive (Sw01 ∷ Bx0-42 ∷ []) (Bx1-42 ∷ Sw01 ∷ [])
  (rw 0 (q120 c4) ∷
   re 0 1 (Bx1-42 ∷ []) ∷ []) Eq.refl

private
  q121 : WsL → Eqn
  q121 c4 = eqn (Sw01 ∷ Bx0-42 ∷ []) (Bx1-42 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·42⟩ c4)

-- nat 0 BOX(4;032): 8 steps
lem-nat-0-BOX⟨4·032⟩ : WsL → ⟪ (Sw01 ∷ Bx4-032 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-132 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨4·032⟩ c4 = derive (Sw01 ∷ Bx4-032 ∷ []) (Bx4-132 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) ∷
   rw 0 (q88 c4) ∷
   rw 1 (q89 c4) ∷
   rw 2 (q121 c4) ∷
   rw 3 (q89 c4) ∷
   rw 4 (q88 c4) ∷
   rw 5 (q121 c4) ∷
   re 0 6 (Bx4-132 ∷ []) ∷ []) Eq.refl
