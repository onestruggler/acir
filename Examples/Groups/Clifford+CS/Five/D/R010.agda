{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R010 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0002 ; wl0003 ; wl0004 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0010 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0015 ; wl0016 ; wl0017 ; wl0018 ; wl0019 ; wl0020 ; wl0021 ; wl0022 ; wl0023 ; wl0030 ; wl0031 ; wl0034 ; wl0035 ; wl0036 ; wl0039 ; wl0040 ; wl0048 ; wl0056 ; wl0057 ; wl0058 ; wl0059 ; wl0061 ; wl0062 ; wl0063 ; wl0064 ; wl0067 ; wl0068 ; wl0073 ; wl0074 ; wl0082 ; wl0084 ; wl0088 ; wl0092 ; wl0098 ; wl0103 ; wl0104 ; wl0105 ; wl0108 ; wl0110 ; wl0111 ; wl0112 ; wl0121 ; wl0127 ; wl0131 ; wl0134 ; wl0135 ; wl0136 ; wl0138 ; wl0139 ; wl0140 ; wl0144 ; wl0145 ; wl0146)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-nat-1-CCZ023 ; lem-nat-1-CCZ024 ; lem-nat-1-TOFF014 ; lem-nat-1-TOFF024 ; lem-nat-1-TOFF203 ; lem-nat-2-CCZ012 ; lem-nat-2-TOFF102)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-nat-0-CCZ024 ; lem-nat-0-CCZ124 ; lem-nat-1-CCZ013 ; lem-nat-1-CCZ014 ; lem-nat-1-TOFF103)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-nat-0-TOFF014 ; lem-nat-0-TOFF104)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-nat-0-TOFF204 ; lem-nat-3-TOFF214)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-nat-0-TOFF024 ; lem-nat-1-BOX⟨2·0143⟩ ; lem-nat-2-CCZ014 ; lem-nat-2-CZ03 ; lem-nat-3-CCZ123 ; lem-nat-3-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-nat-1-BOX⟨0·12⟩ ; lem-nat-1-BOX⟨0·21⟩)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-TOFF134 ; lem-nat-2-BOX⟨0·1432⟩ ; lem-nat-2-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-0-BOX⟨1·20⟩ ; lem-nat-0-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-nat-1-BOX⟨3·124⟩ ; lem-nat-2-BOX⟨0·1423⟩ ; lem-nat-2-CS03 ; lem-nat-2-CSd03 ; lem-nat-2-SBOX⟨0·1·2·3⟩ ; lem-nat-2-SBOX⟨0·1·3·2⟩ ; lem-nat-2-SBOXd⟨0·1·2·3⟩ ; lem-nat-2-SBOXd⟨0·1·3·2⟩)

private
  q1 : WsL → Eqn
  q1 c4 = eqn (Sw12 ∷ CCZ013 ∷ []) (CCZ023 ∷ Sw12 ∷ []) (lem-nat-1-CCZ013 c4)
  q2 : WsL → Eqn
  q2 c4 = eqn (Sw12 ∷ Toff103 ∷ []) (Toff203 ∷ Sw12 ∷ []) (lem-nat-1-TOFF103 c4)
  q3 : WsL → Eqn
  q3 c4 = eqn (Sw12 ∷ Bx3-124 ∷ []) (Bx3-214 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·124⟩ c4)

-- nat 1 BOX(1;3024): 8 steps
lem-nat-1-BOX⟨1·3024⟩ : WsL → ⟪ (Sw12 ∷ Bx1-3024 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·3024⟩ c4 = derive (Sw12 ∷ Bx1-3024 ∷ []) (Bx2-3014 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff103 ∷ Bx3-124 ∷ Toff103 ∷ CCZ013 ∷ Bx3-124 ∷ []) ∷
   rw 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 3 (q2 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q3 c4) ∷
   re 0 6 (Bx2-3014 ∷ []) ∷ []) Eq.refl

private
  q4 : WsL → Eqn
  q4 c4 = eqn (CCZ023 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ123 ∷ []) (wl0003 c4)
  q5 : WsL → Eqn
  q5 c4 = eqn (Sw01 ∷ Toff312 ∷ []) (Toff302 ∷ Sw01 ∷ []) (wl0110 c4)
  q6 : WsL → Eqn
  q6 c4 = eqn (Sw01 ∷ Bx2-34 ∷ []) (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑))

-- nat 0 BOX(3;214): 8 steps
lem-nat-0-BOX⟨3·214⟩ : WsL → ⟪ (Sw01 ∷ Bx3-214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-204 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·214⟩ c4 = derive (Sw01 ∷ Bx3-214 ∷ []) (Bx3-204 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) ∷
   rw⁻ 0 (q4 c4) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   rw 3 (q5 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw 5 (q6 c4) ∷
   re 0 6 (Bx3-204 ∷ []) ∷ []) Eq.refl

private
  q7 : WsL → Eqn
  q7 c4 = eqn (CCZ123 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ023 ∷ []) (wl0103 c4)
  q8 : WsL → Eqn
  q8 c4 = eqn (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) (wl0104 c4)
  q9 : WsL → Eqn
  q9 c4 = eqn (Sw01 ∷ Bx3-214 ∷ []) (Bx3-204 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·214⟩ c4)

-- nat 0 BOX(2;3014): 8 steps
lem-nat-0-BOX⟨2·3014⟩ : WsL → ⟪ (Sw01 ∷ Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·3014⟩ c4 = derive (Sw01 ∷ Bx2-3014 ∷ []) (Bx2-3104 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-214 ∷ Toff203 ∷ CCZ023 ∷ Bx3-214 ∷ []) ∷
   rw⁻ 0 (q7 c4) ∷
   rw 1 (q8 c4) ∷
   rw 2 (q9 c4) ∷
   rw 3 (q8 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw 5 (q9 c4) ∷
   re 0 6 (Bx2-3104 ∷ []) ∷ []) Eq.refl

private
  q10 : WsL → Eqn
  q10 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 c4)
  q11 : WsL → Eqn
  q11 c4 = eqn (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ []) (wl0057 c4)
  q12 : WsL → Eqn
  q12 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0006 c4)
  q13 : WsL → Eqn
  q13 c4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap))
  q14 : WsL → Eqn
  q14 c4 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (c₁ (iI) (Swap ↑))
  q15 : WsL → Eqn
  q15 c4 = eqn (K4 ∷ Sw34 ∷ []) (Sw34 ∷ K3 ∷ []) (wl0067 c4)
  q16 : WsL → Eqn
  q16 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 c4)
  q17 : WsL → Eqn
  q17 c4 = eqn (CX01 ∷ Sw34 ∷ []) (Sw34 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap ↑))
  q18 : WsL → Eqn
  q18 c4 = eqn (ι ∷ Sw34 ∷ []) (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑))
  q19 : WsL → Eqn
  q19 c4 = eqn (Sw12 ∷ K4 ∷ []) (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑))
  q20 : WsL → Eqn
  q20 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0008 c4)
  q21 : WsL → Eqn
  q21 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 c4)
  q22 : WsL → Eqn
  q22 c4 = eqn (CS24⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS14⁻ ∷ []) (wl0009 c4)
  q23 : WsL → Eqn
  q23 c4 = eqn (Sw12 ∷ Sw34 ∷ []) (Sw34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (Swap))
  q24 : WsL → Eqn
  q24 c4 = eqn (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) (wl0010 c4)
  q25 : WsL → Eqn
  q25 c4 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap))
  q26 : WsL → Eqn
  q26 c4 = eqn (Sw23 ∷ K4 ∷ []) (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K))
  q27 : WsL → Eqn
  q27 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl0011 c4)
  q28 : WsL → Eqn
  q28 c4 = eqn (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) (wl0012 c4)
  q29 : WsL → Eqn
  q29 c4 = eqn (Sw23 ∷ Sw34 ∷ Sw23 ∷ []) (Sw34 ∷ Sw23 ∷ Sw34 ∷ []) (wl0013 c4)
  q30 : WsL → Eqn
  q30 c4 = eqn (CS01 ∷ Sw34 ∷ []) (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑))
  q31 : WsL → Eqn
  q31 c4 = eqn (Sw01 ∷ ι ∷ []) (ι ∷ Sw01 ∷ []) (wl0030 c4)
  q32 : WsL → Eqn
  q32 c4 = eqn (Sw01 ∷ K4 ∷ []) (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑))
  q33 : WsL → Eqn
  q33 c4 = eqn (Sw01 ∷ Sw34 ∷ []) (Sw34 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑))
  q34 : WsL → Eqn
  q34 c4 = eqn (CS03 ∷ Sw01 ∷ []) (Sw01 ∷ CS13 ∷ []) (wl0019 c4)
  q35 : WsL → Eqn
  q35 c4 = eqn (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) (wl0020 c4)
  q36 : WsL → Eqn
  q36 c4 = eqn (Sw01 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑))
  q37 : WsL → Eqn
  q37 c4 = eqn (Sw01 ∷ CS34 ∷ []) (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))
  q38 : WsL → Eqn
  q38 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl0015 c4)
  q39 : WsL → Eqn
  q39 c4 = eqn (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) (wl0016 c4)
  q40 : WsL → Eqn
  q40 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl0021 c4)
  q41 : WsL → Eqn
  q41 c4 = eqn (K3 ∷ Sw34 ∷ []) (Sw34 ∷ K4 ∷ []) (wl0068 c4)
  q42 : WsL → Eqn
  q42 c4 = eqn (CX12 ∷ Sw34 ∷ []) (Sw34 ∷ CX12 ∷ []) (c₃ (CX₀₁ ↑) (Swap))
  q43 : WsL → Eqn
  q43 c4 = eqn (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (wl0082 c4)

-- resp TOFF403 at 1: 101 steps
lem-resp-TOFF403-at-1 : WsL → ⟪ (Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff413 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-TOFF403-at-1 c4 = derive (Toff403 ∷ []) (Sw01 ∷ Toff413 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q10 c4) ∷
   re 0 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) ∷
   re 1 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 4 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw⁻ 3 (q11 c4) ∷
   rw⁻ 6 (q12 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q13 c4) ∷
   rw⁻ 8 (q12 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q13 c4) ∷
   rw⁻ 10 (q12 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 (q11 c4) ∷
   rw⁻ 10 (q14 c4) ∷
   rw 11 (q12 c4) ∷
   rw⁻ 2 (q15 c4) ∷
   rw⁻ 5 (q16 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q17 c4) ∷
   rw⁻ 7 (q16 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q17 c4) ∷
   rw⁻ 9 (q16 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q15 c4) ∷
   rw⁻ 9 (q18 c4) ∷
   rw 10 (q16 c4) ∷
   rw 1 (q19 c4) ∷
   rw⁻ 2 (q20 c4) ∷
   rw⁻ 5 (q21 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q22 c4) ∷
   rw⁻ 7 (q21 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q23 c4) ∷
   rw⁻ 7 (q24 c4) ∷
   rw 8 (q23 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw 7 (q19 c4) ∷
   rw⁻ 8 (q25 c4) ∷
   rw 9 (q21 c4) ∷
   rw 0 (q26 c4) ∷
   rw⁻ 1 (q27 c4) ∷
   rw⁻ 4 (q12 c4) ∷
   re 2 3 (CX03 ∷ []) ∷
   rw⁻ 3 (q28 c4) ∷
   rw⁻ 6 (q12 c4) ∷
   re 4 3 (CX03 ∷ []) ∷
   re 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q29 c4) ∷
   rw⁻ 7 (q23 c4) ∷
   rw⁻ 8 (q30 c4) ∷
   rw⁻ 9 (q23 c4) ∷
   rw⁻ 10 (q29 c4) ∷
   re 5 7 (CS04 ∷ []) ∷
   rw 6 (q26 c4) ∷
   rw⁻ 7 (q14 c4) ∷
   rw 8 (q12 c4) ∷
   rw⁻ 7 (q31 c4) ∷
   rw⁻ 6 (q32 c4) ∷
   re 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 7 (q33 c4) ∷
   rw 6 (q34 c4) ∷
   rw⁻ 5 (q33 c4) ∷
   re 6 3 (CS14 ∷ []) ∷
   rw 4 (q35 c4) ∷
   rw⁻ 3 (q36 c4) ∷
   rw 2 (q35 c4) ∷
   rw⁻ 1 (q37 c4) ∷
   rw⁻ 0 (q32 c4) ∷
   rw⁻ 1 (q12 c4) ∷
   rw 2 (q26 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   re 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 4 (q12 c4) ∷
   rw⁻ 5 (q39 c4) ∷
   re 7 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 6 (q12 c4) ∷
   rw⁻ 7 (q40 c4) ∷
   rw 8 (q26 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw⁻ 2 (q16 c4) ∷
   rw⁻ 3 (q41 c4) ∷
   re 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 4 (q16 c4) ∷
   rw⁻ 5 (q42 c4) ∷
   re 7 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q16 c4) ∷
   rw⁻ 7 (q42 c4) ∷
   re 9 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 8 (q16 c4) ∷
   rw⁻ 9 (q41 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   rw 3 (q43 c4) ∷
   re 3 8 (Toff312 ∷ []) ∷
   re 2 3 (Toff412 ∷ []) ∷
   re 1 3 (Toff413 ∷ []) ∷ []) Eq.refl

private
  q44 : WsL → Eqn
  q44 c4 = eqn (CZ02 ∷ Sw01 ∷ []) (Sw01 ∷ CZ12 ∷ []) (wl0105 c4)

-- nat 0 BOX(0;21): 3 steps
lem-nat-0-BOX⟨0·21⟩ : WsL → ⟪ (Sw01 ∷ Bx0-21 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-20 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·21⟩ c4 = derive (Sw01 ∷ Bx0-21 ∷ []) (Bx1-20 ∷ Sw01 ∷ [])
  (re 1 1 (CZ12 ∷ []) ∷
   rw⁻ 0 (q44 c4) ∷
   re 0 1 (Bx1-20 ∷ []) ∷ []) Eq.refl

private
  q45 : WsL → Eqn
  q45 c4 = eqn (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ []) (lem-nat-0-CCZ024 c4)
  q46 : WsL → Eqn
  q46 c4 = eqn (Sw01 ∷ Toff204 ∷ []) (Toff214 ∷ Sw01 ∷ []) (lem-nat-0-TOFF204 c4)
  q47 : WsL → Eqn
  q47 c4 = eqn (Sw01 ∷ Bx0-21 ∷ []) (Bx1-20 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·21⟩ c4)

-- nat 0 BOX(2;041): 8 steps
lem-nat-0-BOX⟨2·041⟩ : WsL → ⟪ (Sw01 ∷ Bx2-041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-140 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·041⟩ c4 = derive (Sw01 ∷ Bx2-041 ∷ []) (Bx2-140 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) ∷
   rw 0 (q45 c4) ∷
   rw 1 (q46 c4) ∷
   rw 2 (q47 c4) ∷
   rw 3 (q46 c4) ∷
   rw 4 (q45 c4) ∷
   rw 5 (q47 c4) ∷
   re 0 6 (Bx2-140 ∷ []) ∷ []) Eq.refl

private
  q48 : WsL → Eqn
  q48 c4 = eqn (Sw01 ∷ Toff023 ∷ []) (Toff123 ∷ Sw01 ∷ []) (wl0108 c4)
  q49 : WsL → Eqn
  q49 c4 = eqn (Sw01 ∷ Bx2-041 ∷ []) (Bx2-140 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·041⟩ c4)

-- nat 0 BOX(0;2341): 8 steps
lem-nat-0-BOX⟨0·2341⟩ : WsL → ⟪ (Sw01 ∷ Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2340 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·2341⟩ c4 = derive (Sw01 ∷ Bx0-2341 ∷ []) (Bx1-2340 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) ∷
   rw⁻ 0 (q7 c4) ∷
   rw 1 (q48 c4) ∷
   rw 2 (q49 c4) ∷
   rw 3 (q48 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw 5 (q49 c4) ∷
   re 0 6 (Bx1-2340 ∷ []) ∷ []) Eq.refl

private
  q50 : WsL → Eqn
  q50 c4 = eqn (Sw23 ∷ CZ03 ∷ []) (CZ02 ∷ Sw23 ∷ []) (lem-nat-2-CZ03 c4)

-- nat 2 BOX(1;03): 3 steps
lem-nat-2-BOX⟨1·03⟩ : WsL → ⟪ (Sw23 ∷ Bx1-03 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-02 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·03⟩ c4 = derive (Sw23 ∷ Bx1-03 ∷ []) (Bx1-02 ∷ Sw23 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw 0 (q50 c4) ∷
   re 0 1 (Bx1-02 ∷ []) ∷ []) Eq.refl

private
  q51 : WsL → Eqn
  q51 c4 = eqn (Sw23 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw23 ∷ []) (lem-nat-2-CCZ014 c4)
  q52 : WsL → Eqn
  q52 c4 = eqn (Sw23 ∷ Toff014 ∷ []) (Toff014 ∷ Sw23 ∷ []) (lem-nat-2-TOFF014 c4)
  q53 : WsL → Eqn
  q53 c4 = eqn (Sw23 ∷ Bx1-03 ∷ []) (Bx1-02 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·03⟩ c4)

-- nat 2 BOX(0;143): 8 steps
lem-nat-2-BOX⟨0·143⟩ : WsL → ⟪ (Sw23 ∷ Bx0-143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-142 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨0·143⟩ c4 = derive (Sw23 ∷ Bx0-143 ∷ []) (Bx0-142 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-03 ∷ Toff014 ∷ CCZ014 ∷ Bx1-03 ∷ []) ∷
   rw 0 (q51 c4) ∷
   rw 1 (q52 c4) ∷
   rw 2 (q53 c4) ∷
   rw 3 (q52 c4) ∷
   rw 4 (q51 c4) ∷
   rw 5 (q53 c4) ∷
   re 0 6 (Bx0-142 ∷ []) ∷ []) Eq.refl

private
  q54 : WsL → Eqn
  q54 c4 = eqn (Sw23 ∷ CCZ012 ∷ []) (CCZ013 ∷ Sw23 ∷ []) (lem-nat-2-CCZ012 c4)
  q55 : WsL → Eqn
  q55 c4 = eqn (Sw23 ∷ Toff102 ∷ []) (Toff103 ∷ Sw23 ∷ []) (lem-nat-2-TOFF102 c4)
  q56 : WsL → Eqn
  q56 c4 = eqn (Sw23 ∷ Bx0-143 ∷ []) (Bx0-142 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·143⟩ c4)

-- nat 2 BOX(1;0243): 8 steps
lem-nat-2-BOX⟨1·0243⟩ : WsL → ⟪ (Sw23 ∷ Bx1-0243 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0342 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-BOX⟨1·0243⟩ c4 = derive (Sw23 ∷ Bx1-0243 ∷ []) (Bx1-0342 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-143 ∷ Toff102 ∷ CCZ012 ∷ Bx0-143 ∷ []) ∷
   rw 0 (q54 c4) ∷
   rw 1 (q55 c4) ∷
   rw 2 (q56 c4) ∷
   rw 3 (q55 c4) ∷
   rw 4 (q54 c4) ∷
   rw 5 (q56 c4) ∷
   re 0 6 (Bx1-0342 ∷ []) ∷ []) Eq.refl

private
  q57 : WsL → Eqn
  q57 c4 = eqn (Sw23 ∷ CS03 ∷ []) (CS02 ∷ Sw23 ∷ []) (lem-nat-2-CS03 c4)

-- nat 2 SBOX(1;0;3;4): 3 steps
lem-nat-2-SBOX⟨1·0·3·4⟩ : WsL → ⟪ (Sw23 ∷ Sb1-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-2-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·0·3·4⟩ c4 = derive (Sw23 ∷ Sb1-0-3-4 ∷ []) (Sb1-0-2-4 ∷ Sw23 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   rw 0 (q57 c4) ∷
   re 0 1 (Sb1-0-2-4 ∷ []) ∷ []) Eq.refl

private
  q58 : WsL → Eqn
  q58 c4 = eqn (Sw23 ∷ CS03⁻ ∷ []) (CS02⁻ ∷ Sw23 ∷ []) (lem-nat-2-CSd03 c4)

-- nat 2 SBOXd(1;0;3;4): 3 steps
lem-nat-2-SBOXd⟨1·0·3·4⟩ : WsL → ⟪ (Sw23 ∷ Sb⁻1-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-2-4 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOXd⟨1·0·3·4⟩ c4 = derive (Sw23 ∷ Sb⁻1-0-3-4 ∷ []) (Sb⁻1-0-2-4 ∷ Sw23 ∷ [])
  (re 1 1 (CS03⁻ ∷ []) ∷
   rw 0 (q58 c4) ∷
   re 0 1 (Sb⁻1-0-2-4 ∷ []) ∷ []) Eq.refl

private
  q59 : WsL → Eqn
  q59 c4 = eqn (Sw23 ∷ Bx1-0243 ∷ []) (Bx1-0342 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨1·0243⟩ c4)
  q60 : WsL → Eqn
  q60 c4 = eqn (Sw23 ∷ Toff324 ∷ []) (Toff234 ∷ Sw23 ∷ []) (wl0144 c4)
  q61 : WsL → Eqn
  q61 c4 = eqn (Sw23 ∷ Sb1-0-3-4 ∷ []) (Sb1-0-2-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨1·0·3·4⟩ c4)
  q62 : WsL → Eqn
  q62 c4 = eqn (Sw23 ∷ Sb⁻1-0-3-4 ∷ []) (Sb⁻1-0-2-4 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨1·0·3·4⟩ c4)

-- nat 2 SBOX(1;0;24;3): 7 steps
lem-nat-2-SBOX⟨1·0·24·3⟩ : WsL → ⟪ (Sw23 ∷ Sb1-0-24-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-34-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨1·0·24·3⟩ c4 = derive (Sw23 ∷ Sb1-0-24-3 ∷ []) (Sb1-0-34-2 ∷ Sw23 ∷ [])
  (re 1 1 (Bx1-0243 ∷ Toff324 ∷ Sb1-0-3-4 ∷ Toff324 ∷ Sb⁻1-0-3-4 ∷ []) ∷
   rw 0 (q59 c4) ∷
   rw 1 (q60 c4) ∷
   rw 2 (q61 c4) ∷
   rw 3 (q60 c4) ∷
   rw 4 (q62 c4) ∷
   re 0 5 (Sb1-0-34-2 ∷ []) ∷ []) Eq.refl

-- nat 1 SBOX(2;0;3;4): 3 steps
lem-nat-1-SBOX⟨2·0·3·4⟩ : WsL → ⟪ (Sw12 ∷ Sb2-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-3-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·0·3·4⟩ c4 = derive (Sw12 ∷ Sb2-0-3-4 ∷ []) (Sb1-0-3-4 ∷ Sw12 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   rw⁻ 0 (q24 c4) ∷
   re 0 1 (Sb1-0-3-4 ∷ []) ∷ []) Eq.refl

private
  q63 : WsL → Eqn
  q63 c4 = eqn (CS03⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS03⁻ ∷ []) (wl0023 c4)

-- nat 1 SBOXd(2;0;3;4): 3 steps
lem-nat-1-SBOXd⟨2·0·3·4⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻2-0-3-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-0-3-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨2·0·3·4⟩ c4 = derive (Sw12 ∷ Sb⁻2-0-3-4 ∷ []) (Sb⁻1-0-3-4 ∷ Sw12 ∷ [])
  (re 1 1 (CS03⁻ ∷ []) ∷
   rw⁻ 0 (q63 c4) ∷
   re 0 1 (Sb⁻1-0-3-4 ∷ []) ∷ []) Eq.refl

private
  q64 : WsL → Eqn
  q64 c4 = eqn (Sw12 ∷ Bx2-0143 ∷ []) (Bx1-0243 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·0143⟩ c4)
  q65 : WsL → Eqn
  q65 c4 = eqn (Sw12 ∷ Toff314 ∷ []) (Toff324 ∷ Sw12 ∷ []) (wl0064 c4)
  q66 : WsL → Eqn
  q66 c4 = eqn (Sw12 ∷ Sb2-0-3-4 ∷ []) (Sb1-0-3-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·3·4⟩ c4)
  q67 : WsL → Eqn
  q67 c4 = eqn (Sw12 ∷ Sb⁻2-0-3-4 ∷ []) (Sb⁻1-0-3-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨2·0·3·4⟩ c4)

-- nat 1 SBOX(2;0;14;3): 7 steps
lem-nat-1-SBOX⟨2·0·14·3⟩ : WsL → ⟪ (Sw12 ∷ Sb2-0-14-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-0-24-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·0·14·3⟩ c4 = derive (Sw12 ∷ Sb2-0-14-3 ∷ []) (Sb1-0-24-3 ∷ Sw12 ∷ [])
  (re 1 1 (Bx2-0143 ∷ Toff314 ∷ Sb2-0-3-4 ∷ Toff314 ∷ Sb⁻2-0-3-4 ∷ []) ∷
   rw 0 (q64 c4) ∷
   rw 1 (q65 c4) ∷
   rw 2 (q66 c4) ∷
   rw 3 (q65 c4) ∷
   rw 4 (q67 c4) ∷
   re 0 5 (Sb1-0-24-3 ∷ []) ∷ []) Eq.refl

private
  q68 : WsL → Eqn
  q68 c4 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (c₂ (K ↑) (Swap))
  q69 : WsL → Eqn
  q69 c4 = eqn (K1 ∷ Sw34 ∷ []) (Sw34 ∷ K1 ∷ []) (c₂ (K ↑) (Swap ↑))
  q70 : WsL → Eqn
  q70 c4 = eqn (K2 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ []) (wl0056 c4)
  q71 : WsL → Eqn
  q71 c4 = eqn (Sw12 ∷ K3 ∷ []) (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K))
  q72 : WsL → Eqn
  q72 c4 = eqn (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) (wl0014 c4)
  q73 : WsL → Eqn
  q73 c4 = eqn (Sw12 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS))
  q74 : WsL → Eqn
  q74 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q75 : WsL → Eqn
  q75 c4 = eqn (K2 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ []) (wl0058 c4)
  q76 : WsL → Eqn
  q76 c4 = eqn (K1 ∷ Sw12 ∷ []) (Sw12 ∷ K2 ∷ []) (wl0062 c4)
  q77 : WsL → Eqn
  q77 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl0017 c4)
  q78 : WsL → Eqn
  q78 c4 = eqn (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ []) (wl0018 c4)
  q79 : WsL → Eqn
  q79 c4 = eqn (Sw01 ∷ K3 ∷ []) (K3 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑))
  q80 : WsL → Eqn
  q80 c4 = eqn (K2 ∷ Sw34 ∷ []) (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap))
  q81 : WsL → Eqn
  q81 c4 = eqn (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (wl0059 c4)

-- resp TOFF204 at 3: 239 steps
lem-resp-TOFF204-at-3 : WsL → ⟪ (Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff314 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-TOFF204-at-3 c4 = derive (Toff204 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ Toff314 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q12 c4) ∷
   rw⁻ 0 (q12 c4) ∷
   re 1 3 (Toff304 ∷ []) ∷
   rw⁻ 2 (q21 c4) ∷
   re 1 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) ∷
   re 3 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) ∷
   re 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 4 (q68 c4) ∷
   rw⁻ 7 (q12 c4) ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 (q13 c4) ∷
   rw⁻ 9 (q12 c4) ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 (q13 c4) ∷
   rw⁻ 11 (q12 c4) ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 (q68 c4) ∷
   rw⁻ 11 (q14 c4) ∷
   rw 12 (q12 c4) ∷
   rw⁻ 3 (q69 c4) ∷
   rw⁻ 6 (q16 c4) ∷
   re 4 3 (CS14 ∷ []) ∷
   rw⁻ 5 (q17 c4) ∷
   rw⁻ 8 (q16 c4) ∷
   re 6 3 (CS14⁻ ∷ []) ∷
   rw⁻ 7 (q17 c4) ∷
   rw⁻ 10 (q16 c4) ∷
   re 8 3 (CS04 ∷ []) ∷
   rw⁻ 9 (q69 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   rw 11 (q16 c4) ∷
   rw⁻ 2 (q70 c4) ∷
   rw⁻ 3 (q20 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw⁻ 5 (q22 c4) ∷
   rw⁻ 8 (q21 c4) ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q23 c4) ∷
   rw⁻ 8 (q24 c4) ∷
   rw 9 (q23 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q70 c4) ∷
   rw⁻ 9 (q25 c4) ∷
   rw 10 (q21 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   rw⁻ 2 (q27 c4) ∷
   rw⁻ 5 (q12 c4) ∷
   re 3 3 (CX03 ∷ []) ∷
   rw⁻ 4 (q28 c4) ∷
   rw⁻ 7 (q12 c4) ∷
   re 5 3 (CX03 ∷ []) ∷
   re 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 6 (q29 c4) ∷
   rw⁻ 8 (q23 c4) ∷
   rw⁻ 9 (q30 c4) ∷
   rw⁻ 10 (q23 c4) ∷
   rw⁻ 11 (q29 c4) ∷
   re 6 7 (CS04 ∷ []) ∷
   rw⁻ 7 (q11 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw 9 (q12 c4) ∷
   rw 8 (q25 c4) ∷
   rw⁻ 7 (q71 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q23 c4) ∷
   rw 7 (q24 c4) ∷
   rw⁻ 6 (q23 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw 5 (q72 c4) ∷
   rw⁻ 4 (q73 c4) ∷
   rw 3 (q72 c4) ∷
   rw⁻ 2 (q74 c4) ∷
   rw⁻ 1 (q71 c4) ∷
   rw⁻ 2 (q12 c4) ∷
   rw⁻ 3 (q75 c4) ∷
   rw⁻ 4 (q38 c4) ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 5 (q12 c4) ∷
   rw⁻ 6 (q39 c4) ∷
   re 8 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 7 (q12 c4) ∷
   re 9 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 8 (q29 c4) ∷
   rw⁻ 10 (q23 c4) ∷
   rw⁻ 11 (q30 c4) ∷
   rw⁻ 12 (q23 c4) ∷
   rw⁻ 13 (q29 c4) ∷
   re 8 7 (CS04 ∷ []) ∷
   rw⁻ 9 (q75 c4) ∷
   rw⁻ 10 (q14 c4) ∷
   rw⁻ 3 (q21 c4) ∷
   rw⁻ 4 (q76 c4) ∷
   rw⁻ 5 (q77 c4) ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 (q21 c4) ∷
   rw⁻ 7 (q78 c4) ∷
   re 9 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 8 (q21 c4) ∷
   re 10 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 9 (q23 c4) ∷
   rw⁻ 10 (q24 c4) ∷
   rw 11 (q23 c4) ∷
   re 9 3 (CS04 ∷ []) ∷
   rw⁻ 10 (q76 c4) ∷
   rw⁻ 11 (q25 c4) ∷
   rw⁻ 4 (q16 c4) ∷
   rw⁻ 5 (q69 c4) ∷
   re 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 6 (q16 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   re 9 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 8 (q16 c4) ∷
   rw⁻ 9 (q17 c4) ∷
   re 11 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 10 (q16 c4) ∷
   rw⁻ 11 (q69 c4) ∷
   rw⁻ 12 (q18 c4) ∷
   rw⁻ 5 (q12 c4) ∷
   rw⁻ 6 (q68 c4) ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 (q12 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 (q12 c4) ∷
   rw⁻ 10 (q13 c4) ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 (q12 c4) ∷
   rw⁻ 12 (q68 c4) ∷
   rw⁻ 13 (q14 c4) ∷
   re 6 8 (Toff102 ∷ []) ∷
   re 5 3 (Toff103 ∷ []) ∷
   re 4 3 (Toff104 ∷ []) ∷
   re 3 3 (Toff204 ∷ []) ∷
   re 2 3 (Toff304 ∷ []) ∷
   rw⁻ 3 (q10 c4) ∷
   re 2 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) ∷
   re 3 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) ∷
   re 4 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) ∷
   re 5 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 6 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 5 (q68 c4) ∷
   rw⁻ 8 (q12 c4) ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 (q13 c4) ∷
   rw⁻ 10 (q12 c4) ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 (q13 c4) ∷
   rw⁻ 12 (q12 c4) ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 (q68 c4) ∷
   rw⁻ 12 (q14 c4) ∷
   rw 13 (q12 c4) ∷
   rw⁻ 4 (q69 c4) ∷
   rw⁻ 7 (q16 c4) ∷
   re 5 3 (CS14 ∷ []) ∷
   rw⁻ 6 (q17 c4) ∷
   rw⁻ 9 (q16 c4) ∷
   re 7 3 (CS14⁻ ∷ []) ∷
   rw⁻ 8 (q17 c4) ∷
   rw⁻ 11 (q16 c4) ∷
   re 9 3 (CS04 ∷ []) ∷
   rw⁻ 10 (q69 c4) ∷
   rw⁻ 11 (q18 c4) ∷
   rw 12 (q16 c4) ∷
   rw⁻ 3 (q70 c4) ∷
   rw⁻ 4 (q20 c4) ∷
   rw⁻ 7 (q21 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   rw⁻ 6 (q22 c4) ∷
   rw⁻ 9 (q21 c4) ∷
   re 7 3 (CX02 ∷ []) ∷
   re 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 8 (q23 c4) ∷
   rw⁻ 9 (q24 c4) ∷
   rw 10 (q23 c4) ∷
   re 8 3 (CS04 ∷ []) ∷
   rw⁻ 9 (q70 c4) ∷
   rw⁻ 10 (q25 c4) ∷
   rw 11 (q21 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw⁻ 3 (q27 c4) ∷
   rw⁻ 6 (q12 c4) ∷
   re 4 3 (CX03 ∷ []) ∷
   rw⁻ 5 (q28 c4) ∷
   rw⁻ 8 (q12 c4) ∷
   re 6 3 (CX03 ∷ []) ∷
   re 8 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 7 (q29 c4) ∷
   rw⁻ 9 (q23 c4) ∷
   rw⁻ 10 (q30 c4) ∷
   rw⁻ 11 (q23 c4) ∷
   rw⁻ 12 (q29 c4) ∷
   re 7 7 (CS04 ∷ []) ∷
   rw⁻ 8 (q11 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw 10 (q12 c4) ∷
   rw⁻ 9 (q31 c4) ∷
   rw⁻ 8 (q79 c4) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw⁻ 9 (q33 c4) ∷
   rw 8 (q34 c4) ∷
   rw⁻ 7 (q33 c4) ∷
   re 8 3 (CS14 ∷ []) ∷
   rw 6 (q35 c4) ∷
   rw⁻ 5 (q36 c4) ∷
   rw 4 (q35 c4) ∷
   rw⁻ 3 (q37 c4) ∷
   rw⁻ 2 (q79 c4) ∷
   rw⁻ 3 (q12 c4) ∷
   rw⁻ 4 (q75 c4) ∷
   rw⁻ 5 (q38 c4) ∷
   re 7 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 6 (q12 c4) ∷
   rw⁻ 7 (q39 c4) ∷
   re 9 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 8 (q12 c4) ∷
   rw⁻ 9 (q40 c4) ∷
   rw⁻ 10 (q75 c4) ∷
   rw⁻ 11 (q14 c4) ∷
   rw⁻ 4 (q16 c4) ∷
   rw⁻ 5 (q80 c4) ∷
   re 7 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 6 (q16 c4) ∷
   rw⁻ 7 (q42 c4) ∷
   re 9 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 8 (q16 c4) ∷
   rw⁻ 9 (q42 c4) ∷
   re 11 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 10 (q16 c4) ∷
   rw⁻ 11 (q80 c4) ∷
   rw⁻ 12 (q18 c4) ∷
   rw 5 (q81 c4) ∷
   re 5 8 (Toff213 ∷ []) ∷
   re 4 3 (Toff214 ∷ []) ∷
   re 3 3 (Toff314 ∷ []) ∷ []) Eq.refl

private
  q82 : WsL → Eqn
  q82 c4 = eqn (Sw23 ∷ Bx0-1423 ∷ []) (Bx0-1432 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1423⟩ c4)
  q83 : WsL → Eqn
  q83 c4 = eqn (Sw23 ∷ Sb0-1-3-2 ∷ []) (Sb0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·3·2⟩ c4)
  q84 : WsL → Eqn
  q84 c4 = eqn (Sw23 ∷ Sb⁻0-1-3-2 ∷ []) (Sb⁻0-1-2-3 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·3·2⟩ c4)

-- nat 2 SBOX(0;1;42;3): 7 steps
lem-nat-2-SBOX⟨0·1·42·3⟩ : WsL → ⟪ (Sw23 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·1·42·3⟩ c4 = derive (Sw23 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-43-2 ∷ Sw23 ∷ [])
  (re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   rw 0 (q82 c4) ∷
   rw 1 (q60 c4) ∷
   rw 2 (q83 c4) ∷
   rw 3 (q60 c4) ∷
   rw 4 (q84 c4) ∷
   re 0 5 (Sb0-1-43-2 ∷ []) ∷ []) Eq.refl

private
  q85 : WsL → Eqn
  q85 c4 = eqn (Sw23 ∷ Bx0-1432 ∷ []) (Bx0-1423 ∷ Sw23 ∷ []) (lem-nat-2-BOX⟨0·1432⟩ c4)
  q86 : WsL → Eqn
  q86 c4 = eqn (Sw23 ∷ Toff234 ∷ []) (Toff324 ∷ Sw23 ∷ []) (wl0127 c4)
  q87 : WsL → Eqn
  q87 c4 = eqn (Sw23 ∷ Sb0-1-2-3 ∷ []) (Sb0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOX⟨0·1·2·3⟩ c4)
  q88 : WsL → Eqn
  q88 c4 = eqn (Sw23 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-1-3-2 ∷ Sw23 ∷ []) (lem-nat-2-SBOXd⟨0·1·2·3⟩ c4)

-- nat 2 SBOX(0;1;43;2): 7 steps
lem-nat-2-SBOX⟨0·1·43·2⟩ : WsL → ⟪ (Sw23 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-nat-2-SBOX⟨0·1·43·2⟩ c4 = derive (Sw23 ∷ Sb0-1-43-2 ∷ []) (Sb0-1-42-3 ∷ Sw23 ∷ [])
  (re 1 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) ∷
   rw 0 (q85 c4) ∷
   rw 1 (q86 c4) ∷
   rw 2 (q87 c4) ∷
   rw 3 (q86 c4) ∷
   rw 4 (q88 c4) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

-- nat 3 TOFF124: 2 steps
lem-nat-3-TOFF124 : WsL → ⟪ (Sw34 ∷ Toff124 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF124 c4 = derive (Sw34 ∷ Toff124 ∷ []) (Toff123 ∷ Sw34 ∷ [])
  (re 1 1 (Sw34 ∷ Toff123 ∷ Sw34 ∷ []) ∷
   rw 0 (q16 c4) ∷ []) Eq.refl

-- nat 3 TOFF213: 2 steps
lem-nat-3-TOFF213 : WsL → ⟪ (Sw34 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF213 c4 = derive (Sw34 ∷ Toff213 ∷ []) (Toff214 ∷ Sw34 ∷ [])
  (rw⁻ 2 (q16 c4) ∷
   re 0 3 (Toff214 ∷ []) ∷ []) Eq.refl

private
  q89 : WsL → Eqn
  q89 c4 = eqn (Sw34 ∷ CCZ123 ∷ []) (CCZ124 ∷ Sw34 ∷ []) (lem-nat-3-CCZ123 c4)
  q90 : WsL → Eqn
  q90 c4 = eqn (Sw34 ∷ Toff213 ∷ []) (Toff214 ∷ Sw34 ∷ []) (lem-nat-3-TOFF213 c4)
  q91 : WsL → Eqn
  q91 c4 = eqn (Bx1-20 ∷ Sw34 ∷ []) (Sw34 ∷ Bx1-20 ∷ []) (c₃ (Swap ↑ • CZ • Swap ↑) (Swap))

-- nat 3 BOX(2;130): 8 steps
lem-nat-3-BOX⟨2·130⟩ : WsL → ⟪ (Sw34 ∷ Bx2-130 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-140 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·130⟩ c4 = derive (Sw34 ∷ Bx2-130 ∷ []) (Bx2-140 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-20 ∷ Toff213 ∷ CCZ123 ∷ Bx1-20 ∷ []) ∷
   rw 0 (q89 c4) ∷
   rw 1 (q90 c4) ∷
   rw⁻ 2 (q91 c4) ∷
   rw 3 (q90 c4) ∷
   rw 4 (q89 c4) ∷
   rw⁻ 5 (q91 c4) ∷
   re 0 6 (Bx2-140 ∷ []) ∷ []) Eq.refl

private
  q92 : WsL → Eqn
  q92 c4 = eqn (Sw34 ∷ CCZ124 ∷ []) (CCZ123 ∷ Sw34 ∷ []) (lem-nat-3-CCZ124 c4)
  q93 : WsL → Eqn
  q93 c4 = eqn (Sw34 ∷ Toff124 ∷ []) (Toff123 ∷ Sw34 ∷ []) (lem-nat-3-TOFF124 c4)
  q94 : WsL → Eqn
  q94 c4 = eqn (Sw34 ∷ Bx2-130 ∷ []) (Bx2-140 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·130⟩ c4)

-- nat 3 BOX(1;2430): 8 steps
lem-nat-3-BOX⟨1·2430⟩ : WsL → ⟪ (Sw34 ∷ Bx1-2430 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2340 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·2430⟩ c4 = derive (Sw34 ∷ Bx1-2430 ∷ []) (Bx1-2340 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-130 ∷ Toff124 ∷ CCZ124 ∷ Bx2-130 ∷ []) ∷
   rw 0 (q92 c4) ∷
   rw 1 (q93 c4) ∷
   rw 2 (q94 c4) ∷
   rw 3 (q93 c4) ∷
   rw 4 (q92 c4) ∷
   rw 5 (q94 c4) ∷
   re 0 6 (Bx1-2340 ∷ []) ∷ []) Eq.refl

private
  q95 : WsL → Eqn
  q95 c4 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (c₁ (K) (Swap ↑))
  q96 : WsL → Eqn
  q96 c4 = eqn (K0 ∷ Sw34 ∷ []) (Sw34 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑))
  q97 : WsL → Eqn
  q97 c4 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (c₁ (K) (Swap))
  q98 : WsL → Eqn
  q98 c4 = eqn (CS34 ∷ Sw34 ∷ []) (Sw34 ∷ CS34 ∷ []) (wl0039 c4)
  q99 : WsL → Eqn
  q99 c4 = eqn (CS34⁻ ∷ Sw34 ∷ []) (Sw34 ∷ CS34⁻ ∷ []) (wl0040 c4)
  q100 : WsL → Eqn
  q100 c4 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (c₂ (CS) (Swap))
  q101 : WsL → Eqn
  q101 c4 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ []) (wl0145 c4)

-- nat 3 TOFF034: 144 steps
lem-nat-3-TOFF034 : WsL → ⟪ (Sw34 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF034 c4 = derive (Sw34 ∷ Toff034 ∷ []) (Toff034 ∷ Sw34 ∷ [])
  (re 1 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) ∷
   re 3 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   re 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 4 (q95 c4) ∷
   rw⁻ 7 (q12 c4) ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 (q13 c4) ∷
   rw⁻ 9 (q12 c4) ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 (q13 c4) ∷
   rw⁻ 11 (q12 c4) ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 (q95 c4) ∷
   rw⁻ 11 (q14 c4) ∷
   rw 12 (q12 c4) ∷
   rw⁻ 3 (q96 c4) ∷
   rw⁻ 6 (q16 c4) ∷
   re 4 3 (CS14 ∷ []) ∷
   rw⁻ 5 (q17 c4) ∷
   rw⁻ 8 (q16 c4) ∷
   re 6 3 (CS14⁻ ∷ []) ∷
   rw⁻ 7 (q17 c4) ∷
   rw⁻ 10 (q16 c4) ∷
   re 8 3 (CS04 ∷ []) ∷
   rw⁻ 9 (q96 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   rw 11 (q16 c4) ∷
   rw⁻ 2 (q97 c4) ∷
   rw⁻ 3 (q20 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw⁻ 5 (q22 c4) ∷
   rw⁻ 8 (q21 c4) ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q23 c4) ∷
   rw⁻ 8 (q24 c4) ∷
   rw 9 (q23 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q97 c4) ∷
   rw⁻ 9 (q25 c4) ∷
   rw 10 (q21 c4) ∷
   rw⁻ 1 (q95 c4) ∷
   rw⁻ 2 (q27 c4) ∷
   rw⁻ 5 (q12 c4) ∷
   re 3 3 (CX03 ∷ []) ∷
   rw⁻ 4 (q28 c4) ∷
   rw⁻ 7 (q12 c4) ∷
   re 5 3 (CX03 ∷ []) ∷
   re 7 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 6 (q29 c4) ∷
   rw⁻ 8 (q23 c4) ∷
   rw⁻ 9 (q30 c4) ∷
   rw⁻ 10 (q23 c4) ∷
   rw⁻ 11 (q29 c4) ∷
   re 6 7 (CS04 ∷ []) ∷
   rw⁻ 7 (q95 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw 9 (q12 c4) ∷
   rw⁻ 0 (q96 c4) ∷
   rw⁻ 1 (q98 c4) ∷
   rw⁻ 4 (q16 c4) ∷
   re 2 3 (CX04 ∷ []) ∷
   rw⁻ 3 (q99 c4) ∷
   rw⁻ 6 (q16 c4) ∷
   re 4 3 (CX04 ∷ []) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q16 c4) ∷
   rw⁻ 6 (q96 c4) ∷
   rw⁻ 7 (q18 c4) ∷
   rw⁻ 0 (q12 c4) ∷
   rw⁻ 1 (q95 c4) ∷
   rw⁻ 2 (q38 c4) ∷
   re 4 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 3 (q29 c4) ∷
   rw⁻ 5 (q23 c4) ∷
   rw⁻ 6 (q17 c4) ∷
   rw⁻ 7 (q23 c4) ∷
   rw⁻ 8 (q29 c4) ∷
   re 3 7 (CX04 ∷ []) ∷
   rw⁻ 4 (q39 c4) ∷
   re 6 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw 5 (q29 c4) ∷
   rw⁻ 7 (q23 c4) ∷
   rw⁻ 8 (q17 c4) ∷
   rw⁻ 9 (q23 c4) ∷
   rw⁻ 10 (q29 c4) ∷
   re 5 7 (CX04 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 (q12 c4) ∷
   rw⁻ 7 (q95 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw⁻ 1 (q21 c4) ∷
   rw⁻ 2 (q97 c4) ∷
   rw⁻ 3 (q77 c4) ∷
   re 5 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 4 (q23 c4) ∷
   rw⁻ 5 (q72 c4) ∷
   rw 6 (q23 c4) ∷
   re 4 3 (CX04 ∷ []) ∷
   rw⁻ 5 (q78 c4) ∷
   re 7 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 6 (q23 c4) ∷
   rw⁻ 7 (q72 c4) ∷
   rw 8 (q23 c4) ∷
   re 6 3 (CX04 ∷ []) ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 7 (q21 c4) ∷
   rw⁻ 8 (q97 c4) ∷
   rw⁻ 9 (q25 c4) ∷
   rw⁻ 2 (q16 c4) ∷
   rw⁻ 3 (q96 c4) ∷
   re 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 4 (q16 c4) ∷
   re 6 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 5 (q16 c4) ∷
   re 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q16 c4) ∷
   re 8 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 7 (q16 c4) ∷
   rw⁻ 8 (q30 c4) ∷
   rw⁻ 9 (q96 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   rw⁻ 3 (q12 c4) ∷
   rw⁻ 4 (q95 c4) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 (q12 c4) ∷
   re 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 6 (q12 c4) ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 (q12 c4) ∷
   re 9 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 8 (q12 c4) ∷
   rw⁻ 9 (q100 c4) ∷
   rw⁻ 10 (q95 c4) ∷
   rw⁻ 11 (q14 c4) ∷
   rw⁻ 4 (q101 c4) ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 3 3 (Toff013 ∷ []) ∷
   re 2 3 (Toff014 ∷ []) ∷
   re 1 3 (Toff024 ∷ []) ∷
   re 0 3 (Toff034 ∷ []) ∷ []) Eq.refl

private
  q102 : WsL → Eqn
  q102 c4 = eqn (Sb1-2-0-3 ∷ Sw34 ∷ []) (Sw34 ∷ Sb1-2-0-3 ∷ []) (c₃ (Swap ↑ • CS • Swap ↑) (Swap))

-- nat 3 SBOX(1;2;0;3): 2 steps
lem-nat-3-SBOX⟨1·2·0·3⟩ : WsL → ⟪ (Sw34 ∷ Sb1-2-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-0-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·2·0·3⟩ c4 = derive (Sw34 ∷ Sb1-2-0-3 ∷ []) (Sb1-2-0-4 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q102 c4) ∷
   re 0 1 (Sb1-2-0-4 ∷ []) ∷ []) Eq.refl

private
  q103 : WsL → Eqn
  q103 c4 = eqn (Sb⁻1-2-0-3 ∷ Sw34 ∷ []) (Sw34 ∷ Sb⁻1-2-0-3 ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (Swap))

-- nat 3 SBOXd(1;2;0;3): 2 steps
lem-nat-3-SBOXd⟨1·2·0·3⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻1-2-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-0-4 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·2·0·3⟩ c4 = derive (Sw34 ∷ Sb⁻1-2-0-3 ∷ []) (Sb⁻1-2-0-4 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q103 c4) ∷
   re 0 1 (Sb⁻1-2-0-4 ∷ []) ∷ []) Eq.refl

private
  q104 : WsL → Eqn
  q104 c4 = eqn (Sw34 ∷ Bx1-2430 ∷ []) (Bx1-2340 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2430⟩ c4)
  q105 : WsL → Eqn
  q105 c4 = eqn (Sw34 ∷ Toff034 ∷ []) (Toff034 ∷ Sw34 ∷ []) (lem-nat-3-TOFF034 c4)
  q106 : WsL → Eqn
  q106 c4 = eqn (Sw34 ∷ Sb1-2-0-3 ∷ []) (Sb1-2-0-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·0·3⟩ c4)
  q107 : WsL → Eqn
  q107 c4 = eqn (Sw34 ∷ Sb⁻1-2-0-3 ∷ []) (Sb⁻1-2-0-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·2·0·3⟩ c4)

-- nat 3 SBOX(1;2;43;0): 7 steps
lem-nat-3-SBOX⟨1·2·43·0⟩ : WsL → ⟪ (Sw34 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-34-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·2·43·0⟩ c4 = derive (Sw34 ∷ Sb1-2-43-0 ∷ []) (Sb1-2-34-0 ∷ Sw34 ∷ [])
  (re 1 1 (Bx1-2430 ∷ Toff034 ∷ Sb1-2-0-3 ∷ Toff034 ∷ Sb⁻1-2-0-3 ∷ []) ∷
   rw 0 (q104 c4) ∷
   rw 1 (q105 c4) ∷
   rw 2 (q106 c4) ∷
   rw 3 (q105 c4) ∷
   rw 4 (q107 c4) ∷
   re 0 5 (Sb1-2-34-0 ∷ []) ∷ []) Eq.refl

-- nat 3 TOFF123: 2 steps
lem-nat-3-TOFF123 : WsL → ⟪ (Sw34 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-TOFF123 c4 = derive (Sw34 ∷ Toff123 ∷ []) (Toff124 ∷ Sw34 ∷ [])
  (rw⁻ 2 (q16 c4) ∷
   re 0 3 (Toff124 ∷ []) ∷ []) Eq.refl

private
  q108 : WsL → Eqn
  q108 c4 = eqn (Sw34 ∷ Toff214 ∷ []) (Toff213 ∷ Sw34 ∷ []) (lem-nat-3-TOFF214 c4)

-- nat 3 BOX(2;140): 8 steps
lem-nat-3-BOX⟨2·140⟩ : WsL → ⟪ (Sw34 ∷ Bx2-140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-130 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨2·140⟩ c4 = derive (Sw34 ∷ Bx2-140 ∷ []) (Bx2-130 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-20 ∷ Toff214 ∷ CCZ124 ∷ Bx1-20 ∷ []) ∷
   rw 0 (q92 c4) ∷
   rw 1 (q108 c4) ∷
   rw⁻ 2 (q91 c4) ∷
   rw 3 (q108 c4) ∷
   rw 4 (q92 c4) ∷
   rw⁻ 5 (q91 c4) ∷
   re 0 6 (Bx2-130 ∷ []) ∷ []) Eq.refl

private
  q109 : WsL → Eqn
  q109 c4 = eqn (Sw34 ∷ Toff123 ∷ []) (Toff124 ∷ Sw34 ∷ []) (lem-nat-3-TOFF123 c4)
  q110 : WsL → Eqn
  q110 c4 = eqn (Sw34 ∷ Bx2-140 ∷ []) (Bx2-130 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨2·140⟩ c4)

-- nat 3 BOX(1;2340): 8 steps
lem-nat-3-BOX⟨1·2340⟩ : WsL → ⟪ (Sw34 ∷ Bx1-2340 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2430 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-BOX⟨1·2340⟩ c4 = derive (Sw34 ∷ Bx1-2340 ∷ []) (Bx1-2430 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff123 ∷ Bx2-140 ∷ Toff123 ∷ CCZ123 ∷ Bx2-140 ∷ []) ∷
   rw 0 (q89 c4) ∷
   rw 1 (q109 c4) ∷
   rw 2 (q110 c4) ∷
   rw 3 (q109 c4) ∷
   rw 4 (q89 c4) ∷
   rw 5 (q110 c4) ∷
   re 0 6 (Bx1-2430 ∷ []) ∷ []) Eq.refl

private
  q111 : WsL → Eqn
  q111 c4 = eqn (Sb1-2-0-4 ∷ Sw34 ∷ []) (Sw34 ∷ Sb1-2-0-4 ∷ []) (c₃ (Swap ↑ • CS • Swap ↑) (Swap))

-- nat 3 SBOX(1;2;0;4): 2 steps
lem-nat-3-SBOX⟨1·2·0·4⟩ : WsL → ⟪ (Sw34 ∷ Sb1-2-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-0-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·2·0·4⟩ c4 = derive (Sw34 ∷ Sb1-2-0-4 ∷ []) (Sb1-2-0-3 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q111 c4) ∷
   re 0 1 (Sb1-2-0-3 ∷ []) ∷ []) Eq.refl

private
  q112 : WsL → Eqn
  q112 c4 = eqn (Sb⁻1-2-0-4 ∷ Sw34 ∷ []) (Sw34 ∷ Sb⁻1-2-0-4 ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (Swap))

-- nat 3 SBOXd(1;2;0;4): 2 steps
lem-nat-3-SBOXd⟨1·2·0·4⟩ : WsL → ⟪ (Sw34 ∷ Sb⁻1-2-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-0-3 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOXd⟨1·2·0·4⟩ c4 = derive (Sw34 ∷ Sb⁻1-2-0-4 ∷ []) (Sb⁻1-2-0-3 ∷ Sw34 ∷ [])
  (rw⁻ 0 (q112 c4) ∷
   re 0 1 (Sb⁻1-2-0-3 ∷ []) ∷ []) Eq.refl

private
  q113 : WsL → Eqn
  q113 c4 = eqn (Sw34 ∷ Bx1-2340 ∷ []) (Bx1-2430 ∷ Sw34 ∷ []) (lem-nat-3-BOX⟨1·2340⟩ c4)
  q114 : WsL → Eqn
  q114 c4 = eqn (Sw34 ∷ Sb1-2-0-4 ∷ []) (Sb1-2-0-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨1·2·0·4⟩ c4)
  q115 : WsL → Eqn
  q115 c4 = eqn (Sw34 ∷ Sb⁻1-2-0-4 ∷ []) (Sb⁻1-2-0-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOXd⟨1·2·0·4⟩ c4)

-- nat 3 SBOX(1;2;34;0): 7 steps
lem-nat-3-SBOX⟨1·2·34·0⟩ : WsL → ⟪ (Sw34 ∷ Sb1-2-34-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ Sw34 ∷ []) ⟫ʷ
lem-nat-3-SBOX⟨1·2·34·0⟩ c4 = derive (Sw34 ∷ Sb1-2-34-0 ∷ []) (Sb1-2-43-0 ∷ Sw34 ∷ [])
  (re 1 1 (Bx1-2340 ∷ Toff034 ∷ Sb1-2-0-4 ∷ Toff034 ∷ Sb⁻1-2-0-4 ∷ []) ∷
   rw 0 (q113 c4) ∷
   rw 1 (q105 c4) ∷
   rw 2 (q114 c4) ∷
   rw 3 (q105 c4) ∷
   rw 4 (q115 c4) ∷
   re 0 5 (Sb1-2-43-0 ∷ []) ∷ []) Eq.refl

-- nat 0 BOX(2;031): 8 steps
lem-nat-0-BOX⟨2·031⟩ : WsL → ⟪ (Sw01 ∷ Bx2-031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-130 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·031⟩ c4 = derive (Sw01 ∷ Bx2-031 ∷ []) (Bx2-130 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) ∷
   rw⁻ 0 (q7 c4) ∷
   rw 1 (q8 c4) ∷
   rw 2 (q47 c4) ∷
   rw 3 (q8 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw 5 (q47 c4) ∷
   re 0 6 (Bx2-130 ∷ []) ∷ []) Eq.refl

private
  q116 : WsL → Eqn
  q116 c4 = eqn (Sw01 ∷ Toff024 ∷ []) (Toff124 ∷ Sw01 ∷ []) (lem-nat-0-TOFF024 c4)
  q117 : WsL → Eqn
  q117 c4 = eqn (Sw01 ∷ Bx2-031 ∷ []) (Bx2-130 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·031⟩ c4)

-- nat 0 BOX(0;2431): 8 steps
lem-nat-0-BOX⟨0·2431⟩ : WsL → ⟪ (Sw01 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-2430 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨0·2431⟩ c4 = derive (Sw01 ∷ Bx0-2431 ∷ []) (Bx1-2430 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) ∷
   rw 0 (q45 c4) ∷
   rw 1 (q116 c4) ∷
   rw 2 (q117 c4) ∷
   rw 3 (q116 c4) ∷
   rw 4 (q45 c4) ∷
   rw 5 (q117 c4) ∷
   re 0 6 (Bx1-2430 ∷ []) ∷ []) Eq.refl

private
  q118 : WsL → Eqn
  q118 c4 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wl0035 c4)

-- nat 0 SBOX(0;2;1;3): 3 steps
lem-nat-0-SBOX⟨0·2·1·3⟩ : WsL → ⟪ (Sw01 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-0-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·2·1·3⟩ c4 = derive (Sw01 ∷ Sb0-2-1-3 ∷ []) (Sb1-2-0-3 ∷ Sw01 ∷ [])
  (re 1 1 (CS12 ∷ []) ∷
   rw⁻ 0 (q118 c4) ∷
   re 0 1 (Sb1-2-0-3 ∷ []) ∷ []) Eq.refl

private
  q119 : WsL → Eqn
  q119 c4 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wl0036 c4)

-- nat 0 SBOXd(0;2;1;3): 3 steps
lem-nat-0-SBOXd⟨0·2·1·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻1-2-0-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨0·2·1·3⟩ c4 = derive (Sw01 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻1-2-0-3 ∷ Sw01 ∷ [])
  (re 1 1 (CS12⁻ ∷ []) ∷
   rw⁻ 0 (q119 c4) ∷
   re 0 1 (Sb⁻1-2-0-3 ∷ []) ∷ []) Eq.refl

private
  q120 : WsL → Eqn
  q120 c4 = eqn (Sw01 ∷ Bx0-2431 ∷ []) (Bx1-2430 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨0·2431⟩ c4)
  q121 : WsL → Eqn
  q121 c4 = eqn (Sw01 ∷ Toff134 ∷ []) (Toff034 ∷ Sw01 ∷ []) (lem-nat-0-TOFF134 c4)
  q122 : WsL → Eqn
  q122 c4 = eqn (Sw01 ∷ Sb0-2-1-3 ∷ []) (Sb1-2-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·2·1·3⟩ c4)
  q123 : WsL → Eqn
  q123 c4 = eqn (Sw01 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻1-2-0-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨0·2·1·3⟩ c4)

-- nat 0 SBOX(0;2;43;1): 7 steps
lem-nat-0-SBOX⟨0·2·43·1⟩ : WsL → ⟪ (Sw01 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-2-43-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨0·2·43·1⟩ c4 = derive (Sw01 ∷ Sb0-2-43-1 ∷ []) (Sb1-2-43-0 ∷ Sw01 ∷ [])
  (re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw 0 (q120 c4) ∷
   rw 1 (q121 c4) ∷
   rw 2 (q122 c4) ∷
   rw 3 (q121 c4) ∷
   rw 4 (q123 c4) ∷
   re 0 5 (Sb1-2-43-0 ∷ []) ∷ []) Eq.refl

private
  q124 : WsL → Eqn
  q124 c4 = eqn (ι1 ∷ Sw34 ∷ []) (Sw34 ∷ ι1 ∷ []) (c₂ (iI ↑) (Swap ↑))
  q125 : WsL → Eqn
  q125 c4 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wl0031 c4)
  q126 : WsL → Eqn
  q126 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q127 : WsL → Eqn
  q127 c4 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wl0048 c4)
  q128 : WsL → Eqn
  q128 c4 = eqn (Sw01 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q129 : WsL → Eqn
  q129 c4 = eqn (Sw01 ∷ ι1 ∷ []) (ι1 ∷ Sw01 ∷ []) (wl0073 c4)
  q130 : WsL → Eqn
  q130 c4 = eqn (Sw12 ∷ ι1 ∷ []) (ι1 ∷ Sw12 ∷ []) (wl0074 c4)
  q131 : WsL → Eqn
  q131 c4 = eqn (ι1 ∷ Sw23 ∷ []) (Sw23 ∷ ι1 ∷ []) (c₂ (iI ↑) (Swap))
  q132 : WsL → Eqn
  q132 c4 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι1 ∷ []) (wl0131 c4)

-- nat 0 TOFF124: 70 steps
lem-nat-0-TOFF124 : WsL → ⟪ (Sw01 ∷ Toff124 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-TOFF124 c4 = derive (Sw01 ∷ Toff124 ∷ []) (Toff024 ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ Toff123 ∷ Sw34 ∷ []) ∷
   re 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw⁻ 1 (q69 c4) ∷
   rw⁻ 4 (q16 c4) ∷
   re 2 3 (CS24 ∷ []) ∷
   rw⁻ 3 (q42 c4) ∷
   rw⁻ 6 (q16 c4) ∷
   re 4 3 (CS24⁻ ∷ []) ∷
   rw⁻ 5 (q42 c4) ∷
   rw⁻ 8 (q16 c4) ∷
   re 6 3 (CS14 ∷ []) ∷
   rw⁻ 7 (q69 c4) ∷
   rw⁻ 8 (q124 c4) ∷
   rw 9 (q16 c4) ∷
   rw⁻ 0 (q125 c4) ∷
   rw 1 (q126 c4) ∷
   rw⁻ 2 (q127 c4) ∷
   rw 3 (q128 c4) ∷
   rw⁻ 4 (q127 c4) ∷
   re 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 5 (q33 c4) ∷
   rw⁻ 6 (q34 c4) ∷
   rw 7 (q33 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw⁻ 6 (q125 c4) ∷
   rw 7 (q129 c4) ∷
   rw⁻ 0 (q21 c4) ∷
   rw⁻ 1 (q97 c4) ∷
   rw⁻ 2 (q77 c4) ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 3 (q21 c4) ∷
   rw⁻ 4 (q78 c4) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 (q21 c4) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q23 c4) ∷
   rw⁻ 7 (q24 c4) ∷
   rw 8 (q23 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q97 c4) ∷
   rw 8 (q130 c4) ∷
   rw⁻ 1 (q16 c4) ∷
   rw⁻ 2 (q96 c4) ∷
   re 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 3 (q16 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   re 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q16 c4) ∷
   rw⁻ 6 (q17 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q16 c4) ∷
   rw⁻ 8 (q96 c4) ∷
   rw⁻ 9 (q124 c4) ∷
   rw⁻ 2 (q12 c4) ∷
   rw⁻ 3 (q95 c4) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 (q12 c4) ∷
   rw⁻ 5 (q13 c4) ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q12 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 (q12 c4) ∷
   rw⁻ 9 (q95 c4) ∷
   rw⁻ 10 (q131 c4) ∷
   rw⁻ 3 (q132 c4) ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 2 3 (Toff013 ∷ []) ∷
   re 1 3 (Toff014 ∷ []) ∷
   re 0 3 (Toff024 ∷ []) ∷ []) Eq.refl

private
  q133 : WsL → Eqn
  q133 c4 = eqn (Sw01 ∷ Toff213 ∷ []) (Toff203 ∷ Sw01 ∷ []) (wl0004 c4)
  q134 : WsL → Eqn
  q134 c4 = eqn (Sw01 ∷ Bx1-20 ∷ []) (Bx0-21 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·20⟩ c4)

-- nat 0 BOX(2;130): 8 steps
lem-nat-0-BOX⟨2·130⟩ : WsL → ⟪ (Sw01 ∷ Bx2-130 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-031 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·130⟩ c4 = derive (Sw01 ∷ Bx2-130 ∷ []) (Bx2-031 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-20 ∷ Toff213 ∷ CCZ123 ∷ Bx1-20 ∷ []) ∷
   rw⁻ 0 (q4 c4) ∷
   rw 1 (q133 c4) ∷
   rw 2 (q134 c4) ∷
   rw 3 (q133 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw 5 (q134 c4) ∷
   re 0 6 (Bx2-031 ∷ []) ∷ []) Eq.refl

private
  q135 : WsL → Eqn
  q135 c4 = eqn (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) (lem-nat-0-CCZ124 c4)
  q136 : WsL → Eqn
  q136 c4 = eqn (Sw01 ∷ Toff124 ∷ []) (Toff024 ∷ Sw01 ∷ []) (lem-nat-0-TOFF124 c4)
  q137 : WsL → Eqn
  q137 c4 = eqn (Sw01 ∷ Bx2-130 ∷ []) (Bx2-031 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·130⟩ c4)

-- nat 0 BOX(1;2430): 8 steps
lem-nat-0-BOX⟨1·2430⟩ : WsL → ⟪ (Sw01 ∷ Bx1-2430 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨1·2430⟩ c4 = derive (Sw01 ∷ Bx1-2430 ∷ []) (Bx0-2431 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff124 ∷ Bx2-130 ∷ Toff124 ∷ CCZ124 ∷ Bx2-130 ∷ []) ∷
   rw 0 (q135 c4) ∷
   rw 1 (q136 c4) ∷
   rw 2 (q137 c4) ∷
   rw 3 (q136 c4) ∷
   rw 4 (q135 c4) ∷
   rw 5 (q137 c4) ∷
   re 0 6 (Bx0-2431 ∷ []) ∷ []) Eq.refl

private
  q138 : WsL → Eqn
  q138 c4 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wl0138 c4)

-- nat 0 SBOX(1;2;0;3): 3 steps
lem-nat-0-SBOX⟨1·2·0·3⟩ : WsL → ⟪ (Sw01 ∷ Sb1-2-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·2·0·3⟩ c4 = derive (Sw01 ∷ Sb1-2-0-3 ∷ []) (Sb0-2-1-3 ∷ Sw01 ∷ [])
  (re 1 1 (CS02 ∷ []) ∷
   rw⁻ 0 (q138 c4) ∷
   re 0 1 (Sb0-2-1-3 ∷ []) ∷ []) Eq.refl

private
  q139 : WsL → Eqn
  q139 c4 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wl0139 c4)

-- nat 0 SBOXd(1;2;0;3): 3 steps
lem-nat-0-SBOXd⟨1·2·0·3⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻1-2-0-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-3 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨1·2·0·3⟩ c4 = derive (Sw01 ∷ Sb⁻1-2-0-3 ∷ []) (Sb⁻0-2-1-3 ∷ Sw01 ∷ [])
  (re 1 1 (CS02⁻ ∷ []) ∷
   rw⁻ 0 (q139 c4) ∷
   re 0 1 (Sb⁻0-2-1-3 ∷ []) ∷ []) Eq.refl

private
  q140 : WsL → Eqn
  q140 c4 = eqn (Sw01 ∷ Bx1-2430 ∷ []) (Bx0-2431 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨1·2430⟩ c4)
  q141 : WsL → Eqn
  q141 c4 = eqn (Sw01 ∷ Toff034 ∷ []) (Toff134 ∷ Sw01 ∷ []) (lem-nat-0-TOFF034 c4)
  q142 : WsL → Eqn
  q142 c4 = eqn (Sw01 ∷ Sb1-2-0-3 ∷ []) (Sb0-2-1-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·2·0·3⟩ c4)
  q143 : WsL → Eqn
  q143 c4 = eqn (Sw01 ∷ Sb⁻1-2-0-3 ∷ []) (Sb⁻0-2-1-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨1·2·0·3⟩ c4)

-- nat 0 SBOX(1;2;43;0): 7 steps
lem-nat-0-SBOX⟨1·2·43·0⟩ : WsL → ⟪ (Sw01 ∷ Sb1-2-43-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨1·2·43·0⟩ c4 = derive (Sw01 ∷ Sb1-2-43-0 ∷ []) (Sb0-2-43-1 ∷ Sw01 ∷ [])
  (re 1 1 (Bx1-2430 ∷ Toff034 ∷ Sb1-2-0-3 ∷ Toff034 ∷ Sb⁻1-2-0-3 ∷ []) ∷
   rw 0 (q140 c4) ∷
   rw 1 (q141 c4) ∷
   rw 2 (q142 c4) ∷
   rw 3 (q141 c4) ∷
   rw 4 (q143 c4) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q144 : WsL → Eqn
  q144 c4 = eqn (Sw12 ∷ Bx0-12 ∷ []) (Bx0-21 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·12⟩ c4)

-- nat 1 BOX(1;032): 8 steps
lem-nat-1-BOX⟨1·032⟩ : WsL → ⟪ (Sw12 ∷ Bx1-032 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-031 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·032⟩ c4 = derive (Sw12 ∷ Bx1-032 ∷ []) (Bx2-031 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) ∷
   rw 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q144 c4) ∷
   rw 3 (q2 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q144 c4) ∷
   re 0 6 (Bx2-031 ∷ []) ∷ []) Eq.refl

private
  q145 : WsL → Eqn
  q145 c4 = eqn (Sw12 ∷ CCZ014 ∷ []) (CCZ024 ∷ Sw12 ∷ []) (lem-nat-1-CCZ014 c4)
  q146 : WsL → Eqn
  q146 c4 = eqn (Sw12 ∷ Toff014 ∷ []) (Toff024 ∷ Sw12 ∷ []) (lem-nat-1-TOFF014 c4)
  q147 : WsL → Eqn
  q147 c4 = eqn (Sw12 ∷ Bx1-032 ∷ []) (Bx2-031 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·032⟩ c4)

-- nat 1 BOX(0;1432): 8 steps
lem-nat-1-BOX⟨0·1432⟩ : WsL → ⟪ (Sw12 ∷ Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·1432⟩ c4 = derive (Sw12 ∷ Bx0-1432 ∷ []) (Bx0-2431 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-032 ∷ Toff014 ∷ CCZ014 ∷ Bx1-032 ∷ []) ∷
   rw 0 (q145 c4) ∷
   rw 1 (q146 c4) ∷
   rw 2 (q147 c4) ∷
   rw 3 (q146 c4) ∷
   rw 4 (q145 c4) ∷
   rw 5 (q147 c4) ∷
   re 0 6 (Bx0-2431 ∷ []) ∷ []) Eq.refl

private
  q148 : WsL → Eqn
  q148 c4 = eqn (CS12 ∷ Sw12 ∷ []) (Sw12 ∷ CS12 ∷ []) (wl0134 c4)

-- nat 1 SBOX(0;1;2;3): 3 steps
lem-nat-1-SBOX⟨0·1·2·3⟩ : WsL → ⟪ (Sw12 ∷ Sb0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-1-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·1·2·3⟩ c4 = derive (Sw12 ∷ Sb0-1-2-3 ∷ []) (Sb0-2-1-3 ∷ Sw12 ∷ [])
  (re 1 1 (CS12 ∷ []) ∷
   rw⁻ 0 (q148 c4) ∷
   re 0 1 (Sb0-2-1-3 ∷ []) ∷ []) Eq.refl

private
  q149 : WsL → Eqn
  q149 c4 = eqn (CS12⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS12⁻ ∷ []) (wl0135 c4)

-- nat 1 SBOXd(0;1;2;3): 3 steps
lem-nat-1-SBOXd⟨0·1·2·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻0-1-2-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-2-1-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·1·2·3⟩ c4 = derive (Sw12 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-2-1-3 ∷ Sw12 ∷ [])
  (re 1 1 (CS12⁻ ∷ []) ∷
   rw⁻ 0 (q149 c4) ∷
   re 0 1 (Sb⁻0-2-1-3 ∷ []) ∷ []) Eq.refl

private
  q150 : WsL → Eqn
  q150 c4 = eqn (Sw12 ∷ Bx0-1432 ∷ []) (Bx0-2431 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·1432⟩ c4)
  q151 : WsL → Eqn
  q151 c4 = eqn (Sw12 ∷ Toff234 ∷ []) (Toff134 ∷ Sw12 ∷ []) (wl0140 c4)
  q152 : WsL → Eqn
  q152 c4 = eqn (Sw12 ∷ Sb0-1-2-3 ∷ []) (Sb0-2-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·1·2·3⟩ c4)
  q153 : WsL → Eqn
  q153 c4 = eqn (Sw12 ∷ Sb⁻0-1-2-3 ∷ []) (Sb⁻0-2-1-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·1·2·3⟩ c4)

-- nat 1 SBOX(0;1;43;2): 7 steps
lem-nat-1-SBOX⟨0·1·43·2⟩ : WsL → ⟪ (Sw12 ∷ Sb0-1-43-2 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·1·43·2⟩ c4 = derive (Sw12 ∷ Sb0-1-43-2 ∷ []) (Sb0-2-43-1 ∷ Sw12 ∷ [])
  (re 1 1 (Bx0-1432 ∷ Toff234 ∷ Sb0-1-2-3 ∷ Toff234 ∷ Sb⁻0-1-2-3 ∷ []) ∷
   rw 0 (q150 c4) ∷
   rw 1 (q151 c4) ∷
   rw 2 (q152 c4) ∷
   rw 3 (q151 c4) ∷
   rw 4 (q153 c4) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q154 : WsL → Eqn
  q154 c4 = eqn (Sw12 ∷ CCZ023 ∷ []) (CCZ013 ∷ Sw12 ∷ []) (lem-nat-1-CCZ023 c4)
  q155 : WsL → Eqn
  q155 c4 = eqn (Sw12 ∷ Toff203 ∷ []) (Toff103 ∷ Sw12 ∷ []) (lem-nat-1-TOFF203 c4)
  q156 : WsL → Eqn
  q156 c4 = eqn (Sw12 ∷ Bx0-21 ∷ []) (Bx0-12 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·21⟩ c4)

-- nat 1 BOX(2;031): 8 steps
lem-nat-1-BOX⟨2·031⟩ : WsL → ⟪ (Sw12 ∷ Bx2-031 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-032 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·031⟩ c4 = derive (Sw12 ∷ Bx2-031 ∷ []) (Bx1-032 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) ∷
   rw 0 (q154 c4) ∷
   rw 1 (q155 c4) ∷
   rw 2 (q156 c4) ∷
   rw 3 (q155 c4) ∷
   rw 4 (q154 c4) ∷
   rw 5 (q156 c4) ∷
   re 0 6 (Bx1-032 ∷ []) ∷ []) Eq.refl

private
  q157 : WsL → Eqn
  q157 c4 = eqn (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) (lem-nat-1-CCZ024 c4)
  q158 : WsL → Eqn
  q158 c4 = eqn (Sw12 ∷ Toff024 ∷ []) (Toff014 ∷ Sw12 ∷ []) (lem-nat-1-TOFF024 c4)
  q159 : WsL → Eqn
  q159 c4 = eqn (Sw12 ∷ Bx2-031 ∷ []) (Bx1-032 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·031⟩ c4)

-- nat 1 BOX(0;2431): 8 steps
lem-nat-1-BOX⟨0·2431⟩ : WsL → ⟪ (Sw12 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨0·2431⟩ c4 = derive (Sw12 ∷ Bx0-2431 ∷ []) (Bx0-1432 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ Bx2-031 ∷ []) ∷
   rw 0 (q157 c4) ∷
   rw 1 (q158 c4) ∷
   rw 2 (q159 c4) ∷
   rw 3 (q158 c4) ∷
   rw 4 (q157 c4) ∷
   rw 5 (q159 c4) ∷
   re 0 6 (Bx0-1432 ∷ []) ∷ []) Eq.refl

-- nat 1 SBOX(0;2;1;3): 3 steps
lem-nat-1-SBOX⟨0·2·1·3⟩ : WsL → ⟪ (Sw12 ∷ Sb0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-2-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·2·1·3⟩ c4 = derive (Sw12 ∷ Sb0-2-1-3 ∷ []) (Sb0-1-2-3 ∷ Sw12 ∷ [])
  (re 1 1 (CS12 ∷ []) ∷
   rw⁻ 0 (q148 c4) ∷
   re 0 1 (Sb0-1-2-3 ∷ []) ∷ []) Eq.refl

-- nat 1 SBOXd(0;2;1;3): 3 steps
lem-nat-1-SBOXd⟨0·2·1·3⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻0-2-1-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻0-1-2-3 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨0·2·1·3⟩ c4 = derive (Sw12 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-1-2-3 ∷ Sw12 ∷ [])
  (re 1 1 (CS12⁻ ∷ []) ∷
   rw⁻ 0 (q149 c4) ∷
   re 0 1 (Sb⁻0-1-2-3 ∷ []) ∷ []) Eq.refl

private
  q160 : WsL → Eqn
  q160 c4 = eqn (Sw12 ∷ Bx0-2431 ∷ []) (Bx0-1432 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨0·2431⟩ c4)
  q161 : WsL → Eqn
  q161 c4 = eqn (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) (wl0136 c4)
  q162 : WsL → Eqn
  q162 c4 = eqn (Sw12 ∷ Sb0-2-1-3 ∷ []) (Sb0-1-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨0·2·1·3⟩ c4)
  q163 : WsL → Eqn
  q163 c4 = eqn (Sw12 ∷ Sb⁻0-2-1-3 ∷ []) (Sb⁻0-1-2-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨0·2·1·3⟩ c4)

-- nat 1 SBOX(0;2;43;1): 7 steps
lem-nat-1-SBOX⟨0·2·43·1⟩ : WsL → ⟪ (Sw12 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-43-2 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨0·2·43·1⟩ c4 = derive (Sw12 ∷ Sb0-2-43-1 ∷ []) (Sb0-1-43-2 ∷ Sw12 ∷ [])
  (re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   rw 0 (q160 c4) ∷
   rw 1 (q161 c4) ∷
   rw 2 (q162 c4) ∷
   rw 3 (q161 c4) ∷
   rw 4 (q163 c4) ∷
   re 0 5 (Sb0-1-43-2 ∷ []) ∷ []) Eq.refl

private
  q164 : WsL → Eqn
  q164 c4 = eqn (CZ13 ∷ Sw01 ∷ []) (Sw01 ∷ CZ03 ∷ []) (wl0092 c4)

-- nat 0 BOX(2;30): 3 steps
lem-nat-0-BOX⟨2·30⟩ : WsL → ⟪ (Sw01 ∷ Bx2-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-31 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·30⟩ c4 = derive (Sw01 ∷ Bx2-30 ∷ []) (Bx2-31 ∷ Sw01 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw⁻ 0 (q164 c4) ∷
   re 0 1 (Bx2-31 ∷ []) ∷ []) Eq.refl

private
  q165 : WsL → Eqn
  q165 c4 = eqn (Sw01 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ))
  q166 : WsL → Eqn
  q166 c4 = eqn (Sw01 ∷ Toff324 ∷ []) (Toff324 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ • CCZ • K ↑ • iI))
  q167 : WsL → Eqn
  q167 c4 = eqn (Sw01 ∷ Bx2-30 ∷ []) (Bx2-31 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·30⟩ c4)

-- nat 0 BOX(3;240): 8 steps
lem-nat-0-BOX⟨3·240⟩ : WsL → ⟪ (Sw01 ∷ Bx3-240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-241 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·240⟩ c4 = derive (Sw01 ∷ Bx3-240 ∷ []) (Bx3-241 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) ∷
   rw 0 (q165 c4) ∷
   rw 1 (q166 c4) ∷
   rw 2 (q167 c4) ∷
   rw 3 (q166 c4) ∷
   rw 4 (q165 c4) ∷
   rw 5 (q167 c4) ∷
   re 0 6 (Bx3-241 ∷ []) ∷ []) Eq.refl

private
  q168 : WsL → Eqn
  q168 c4 = eqn (Sw01 ∷ Bx3-240 ∷ []) (Bx3-241 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·240⟩ c4)

-- nat 0 BOX(2;3140): 8 steps
lem-nat-0-BOX⟨2·3140⟩ : WsL → ⟪ (Sw01 ∷ Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·3140⟩ c4 = derive (Sw01 ∷ Bx2-3140 ∷ []) (Bx2-3041 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ []) ∷
   rw⁻ 0 (q4 c4) ∷
   rw 1 (q133 c4) ∷
   rw 2 (q168 c4) ∷
   rw 3 (q133 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw 5 (q168 c4) ∷
   re 0 6 (Bx2-3041 ∷ []) ∷ []) Eq.refl

private
  q169 : WsL → Eqn
  q169 c4 = eqn (CS13 ∷ Sw01 ∷ []) (Sw01 ∷ CS03 ∷ []) (wl0061 c4)

-- nat 0 SBOX(2;3;0;4): 3 steps
lem-nat-0-SBOX⟨2·3·0·4⟩ : WsL → ⟪ (Sw01 ∷ Sb2-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-1-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·3·0·4⟩ c4 = derive (Sw01 ∷ Sb2-3-0-4 ∷ []) (Sb2-3-1-4 ∷ Sw01 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   rw⁻ 0 (q169 c4) ∷
   re 0 1 (Sb2-3-1-4 ∷ []) ∷ []) Eq.refl

private
  q170 : WsL → Eqn
  q170 c4 = eqn (CS13⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS03⁻ ∷ []) (wl0121 c4)

-- nat 0 SBOXd(2;3;0;4): 3 steps
lem-nat-0-SBOXd⟨2·3·0·4⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-1-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·3·0·4⟩ c4 = derive (Sw01 ∷ Sb⁻2-3-0-4 ∷ []) (Sb⁻2-3-1-4 ∷ Sw01 ∷ [])
  (re 1 1 (CS03⁻ ∷ []) ∷
   rw⁻ 0 (q170 c4) ∷
   re 0 1 (Sb⁻2-3-1-4 ∷ []) ∷ []) Eq.refl

private
  q171 : WsL → Eqn
  q171 c4 = eqn (Sw01 ∷ Bx2-3140 ∷ []) (Bx2-3041 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3140⟩ c4)
  q172 : WsL → Eqn
  q172 c4 = eqn (Sw01 ∷ Toff014 ∷ []) (Toff104 ∷ Sw01 ∷ []) (lem-nat-0-TOFF014 c4)
  q173 : WsL → Eqn
  q173 c4 = eqn (Sw01 ∷ Sb2-3-0-4 ∷ []) (Sb2-3-1-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·0·4⟩ c4)
  q174 : WsL → Eqn
  q174 c4 = eqn (Sw01 ∷ Sb⁻2-3-0-4 ∷ []) (Sb⁻2-3-1-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·3·0·4⟩ c4)

-- nat 0 SBOX(2;3;14;0): 7 steps
lem-nat-0-SBOX⟨2·3·14·0⟩ : WsL → ⟪ (Sw01 ∷ Sb2-3-14-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-04-1 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·3·14·0⟩ c4 = derive (Sw01 ∷ Sb2-3-14-0 ∷ []) (Sb2-3-04-1 ∷ Sw01 ∷ [])
  (re 1 1 (Bx2-3140 ∷ Toff014 ∷ Sb2-3-0-4 ∷ Toff014 ∷ Sb⁻2-3-0-4 ∷ []) ∷
   rw 0 (q171 c4) ∷
   rw 1 (q172 c4) ∷
   rw 2 (q173 c4) ∷
   rw 3 (q172 c4) ∷
   rw 4 (q174 c4) ∷
   re 0 5 (Sb2-3-04-1 ∷ []) ∷ []) Eq.refl

private
  q175 : WsL → Eqn
  q175 c4 = eqn (CZ03 ∷ Sw01 ∷ []) (Sw01 ∷ CZ13 ∷ []) (wl0088 c4)

-- nat 0 BOX(2;31): 3 steps
lem-nat-0-BOX⟨2·31⟩ : WsL → ⟪ (Sw01 ∷ Bx2-31 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-30 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·31⟩ c4 = derive (Sw01 ∷ Bx2-31 ∷ []) (Bx2-30 ∷ Sw01 ∷ [])
  (re 1 1 (CZ13 ∷ []) ∷
   rw⁻ 0 (q175 c4) ∷
   re 0 1 (Bx2-30 ∷ []) ∷ []) Eq.refl

private
  q176 : WsL → Eqn
  q176 c4 = eqn (Sw01 ∷ Bx2-31 ∷ []) (Bx2-30 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·31⟩ c4)

-- nat 0 BOX(3;241): 8 steps
lem-nat-0-BOX⟨3·241⟩ : WsL → ⟪ (Sw01 ∷ Bx3-241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-240 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨3·241⟩ c4 = derive (Sw01 ∷ Bx3-241 ∷ []) (Bx3-240 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-31 ∷ Toff324 ∷ CCZ234 ∷ Bx2-31 ∷ []) ∷
   rw 0 (q165 c4) ∷
   rw 1 (q166 c4) ∷
   rw 2 (q176 c4) ∷
   rw 3 (q166 c4) ∷
   rw 4 (q165 c4) ∷
   rw 5 (q176 c4) ∷
   re 0 6 (Bx3-240 ∷ []) ∷ []) Eq.refl

private
  q177 : WsL → Eqn
  q177 c4 = eqn (Sw01 ∷ Bx3-241 ∷ []) (Bx3-240 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨3·241⟩ c4)

-- nat 0 BOX(2;3041): 8 steps
lem-nat-0-BOX⟨2·3041⟩ : WsL → ⟪ (Sw01 ∷ Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-BOX⟨2·3041⟩ c4 = derive (Sw01 ∷ Bx2-3041 ∷ []) (Bx2-3140 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-241 ∷ Toff203 ∷ CCZ023 ∷ Bx3-241 ∷ []) ∷
   rw⁻ 0 (q7 c4) ∷
   rw 1 (q8 c4) ∷
   rw 2 (q177 c4) ∷
   rw 3 (q8 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw 5 (q177 c4) ∷
   re 0 6 (Bx2-3140 ∷ []) ∷ []) Eq.refl

-- nat 0 SBOX(2;3;1;4): 3 steps
lem-nat-0-SBOX⟨2·3·1·4⟩ : WsL → ⟪ (Sw01 ∷ Sb2-3-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-0-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·3·1·4⟩ c4 = derive (Sw01 ∷ Sb2-3-1-4 ∷ []) (Sb2-3-0-4 ∷ Sw01 ∷ [])
  (re 1 1 (CS13 ∷ []) ∷
   rw⁻ 0 (q34 c4) ∷
   re 0 1 (Sb2-3-0-4 ∷ []) ∷ []) Eq.refl

private
  q178 : WsL → Eqn
  q178 c4 = eqn (CS03⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS13⁻ ∷ []) (wl0022 c4)

-- nat 0 SBOXd(2;3;1;4): 3 steps
lem-nat-0-SBOXd⟨2·3·1·4⟩ : WsL → ⟪ (Sw01 ∷ Sb⁻2-3-1-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-0-4 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOXd⟨2·3·1·4⟩ c4 = derive (Sw01 ∷ Sb⁻2-3-1-4 ∷ []) (Sb⁻2-3-0-4 ∷ Sw01 ∷ [])
  (re 1 1 (CS13⁻ ∷ []) ∷
   rw⁻ 0 (q178 c4) ∷
   re 0 1 (Sb⁻2-3-0-4 ∷ []) ∷ []) Eq.refl

private
  q179 : WsL → Eqn
  q179 c4 = eqn (Sw01 ∷ Bx2-3041 ∷ []) (Bx2-3140 ∷ Sw01 ∷ []) (lem-nat-0-BOX⟨2·3041⟩ c4)
  q180 : WsL → Eqn
  q180 c4 = eqn (Sw01 ∷ Toff104 ∷ []) (Toff014 ∷ Sw01 ∷ []) (lem-nat-0-TOFF104 c4)
  q181 : WsL → Eqn
  q181 c4 = eqn (Sw01 ∷ Sb2-3-1-4 ∷ []) (Sb2-3-0-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨2·3·1·4⟩ c4)
  q182 : WsL → Eqn
  q182 c4 = eqn (Sw01 ∷ Sb⁻2-3-1-4 ∷ []) (Sb⁻2-3-0-4 ∷ Sw01 ∷ []) (lem-nat-0-SBOXd⟨2·3·1·4⟩ c4)

-- nat 0 SBOX(2;3;04;1): 7 steps
lem-nat-0-SBOX⟨2·3·04·1⟩ : WsL → ⟪ (Sw01 ∷ Sb2-3-04-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-14-0 ∷ Sw01 ∷ []) ⟫ʷ
lem-nat-0-SBOX⟨2·3·04·1⟩ c4 = derive (Sw01 ∷ Sb2-3-04-1 ∷ []) (Sb2-3-14-0 ∷ Sw01 ∷ [])
  (re 1 1 (Bx2-3041 ∷ Toff104 ∷ Sb2-3-1-4 ∷ Toff104 ∷ Sb⁻2-3-1-4 ∷ []) ∷
   rw 0 (q179 c4) ∷
   rw 1 (q180 c4) ∷
   rw 2 (q181 c4) ∷
   rw 3 (q180 c4) ∷
   rw 4 (q182 c4) ∷
   re 0 5 (Sb2-3-14-0 ∷ []) ∷ []) Eq.refl

private
  q183 : WsL → Eqn
  q183 c4 = eqn (CZ03 ∷ Sw12 ∷ []) (Sw12 ∷ CZ03 ∷ []) (wl0098 c4)

-- nat 1 BOX(1;30): 3 steps
lem-nat-1-BOX⟨1·30⟩ : WsL → ⟪ (Sw12 ∷ Bx1-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-30 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·30⟩ c4 = derive (Sw12 ∷ Bx1-30 ∷ []) (Bx2-30 ∷ Sw12 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw⁻ 0 (q183 c4) ∷
   re 0 1 (Bx2-30 ∷ []) ∷ []) Eq.refl

private
  q184 : WsL → Eqn
  q184 c4 = eqn (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) (wl0084 c4)
  q185 : WsL → Eqn
  q185 c4 = eqn (Sw12 ∷ Bx1-30 ∷ []) (Bx2-30 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·30⟩ c4)

-- nat 1 BOX(3;140): 8 steps
lem-nat-1-BOX⟨3·140⟩ : WsL → ⟪ (Sw12 ∷ Bx3-140 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-240 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·140⟩ c4 = derive (Sw12 ∷ Bx3-140 ∷ []) (Bx3-240 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-30 ∷ Toff314 ∷ CCZ134 ∷ Bx1-30 ∷ []) ∷
   rw⁻ 0 (q184 c4) ∷
   rw 1 (q65 c4) ∷
   rw 2 (q185 c4) ∷
   rw 3 (q65 c4) ∷
   rw⁻ 4 (q184 c4) ∷
   rw 5 (q185 c4) ∷
   re 0 6 (Bx3-240 ∷ []) ∷ []) Eq.refl

private
  q186 : WsL → Eqn
  q186 c4 = eqn (CCZ123 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ123 ∷ []) (wl0111 c4)
  q187 : WsL → Eqn
  q187 c4 = eqn (Sw12 ∷ Toff123 ∷ []) (Toff213 ∷ Sw12 ∷ []) (wl0146 c4)
  q188 : WsL → Eqn
  q188 c4 = eqn (Sw12 ∷ Bx3-140 ∷ []) (Bx3-240 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·140⟩ c4)

-- nat 1 BOX(1;3240): 8 steps
lem-nat-1-BOX⟨1·3240⟩ : WsL → ⟪ (Sw12 ∷ Bx1-3240 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨1·3240⟩ c4 = derive (Sw12 ∷ Bx1-3240 ∷ []) (Bx2-3140 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff123 ∷ Bx3-140 ∷ Toff123 ∷ CCZ123 ∷ Bx3-140 ∷ []) ∷
   rw⁻ 0 (q186 c4) ∷
   rw 1 (q187 c4) ∷
   rw 2 (q188 c4) ∷
   rw 3 (q187 c4) ∷
   rw⁻ 4 (q186 c4) ∷
   rw 5 (q188 c4) ∷
   re 0 6 (Bx2-3140 ∷ []) ∷ []) Eq.refl

-- nat 1 SBOX(1;3;0;4): 3 steps
lem-nat-1-SBOX⟨1·3·0·4⟩ : WsL → ⟪ (Sw12 ∷ Sb1-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-0-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·3·0·4⟩ c4 = derive (Sw12 ∷ Sb1-3-0-4 ∷ []) (Sb2-3-0-4 ∷ Sw12 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   rw⁻ 0 (q24 c4) ∷
   re 0 1 (Sb2-3-0-4 ∷ []) ∷ []) Eq.refl

-- nat 1 SBOXd(1;3;0;4): 3 steps
lem-nat-1-SBOXd⟨1·3·0·4⟩ : WsL → ⟪ (Sw12 ∷ Sb⁻1-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb⁻2-3-0-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOXd⟨1·3·0·4⟩ c4 = derive (Sw12 ∷ Sb⁻1-3-0-4 ∷ []) (Sb⁻2-3-0-4 ∷ Sw12 ∷ [])
  (re 1 1 (CS03⁻ ∷ []) ∷
   rw⁻ 0 (q63 c4) ∷
   re 0 1 (Sb⁻2-3-0-4 ∷ []) ∷ []) Eq.refl

private
  q189 : WsL → Eqn
  q189 c4 = eqn (Sw12 ∷ Bx1-3240 ∷ []) (Bx2-3140 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨1·3240⟩ c4)
  q190 : WsL → Eqn
  q190 c4 = eqn (Sw12 ∷ Sb1-3-0-4 ∷ []) (Sb2-3-0-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·3·0·4⟩ c4)
  q191 : WsL → Eqn
  q191 c4 = eqn (Sw12 ∷ Sb⁻1-3-0-4 ∷ []) (Sb⁻2-3-0-4 ∷ Sw12 ∷ []) (lem-nat-1-SBOXd⟨1·3·0·4⟩ c4)

-- nat 1 SBOX(1;3;24;0): 7 steps
lem-nat-1-SBOX⟨1·3·24·0⟩ : WsL → ⟪ (Sw12 ∷ Sb1-3-24-0 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-3-14-0 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨1·3·24·0⟩ c4 = derive (Sw12 ∷ Sb1-3-24-0 ∷ []) (Sb2-3-14-0 ∷ Sw12 ∷ [])
  (re 1 1 (Bx1-3240 ∷ Toff024 ∷ Sb1-3-0-4 ∷ Toff024 ∷ Sb⁻1-3-0-4 ∷ []) ∷
   rw 0 (q189 c4) ∷
   rw 1 (q158 c4) ∷
   rw 2 (q190 c4) ∷
   rw 3 (q158 c4) ∷
   rw 4 (q191 c4) ∷
   re 0 5 (Sb2-3-14-0 ∷ []) ∷ []) Eq.refl

-- nat 1 BOX(2;30): 3 steps
lem-nat-1-BOX⟨2·30⟩ : WsL → ⟪ (Sw12 ∷ Bx2-30 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-30 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·30⟩ c4 = derive (Sw12 ∷ Bx2-30 ∷ []) (Bx1-30 ∷ Sw12 ∷ [])
  (re 1 1 (CZ03 ∷ []) ∷
   rw⁻ 0 (q183 c4) ∷
   re 0 1 (Bx1-30 ∷ []) ∷ []) Eq.refl

private
  q192 : WsL → Eqn
  q192 c4 = eqn (CCZ134 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ234 ∷ []) (wl0034 c4)
  q193 : WsL → Eqn
  q193 c4 = eqn (Sw12 ∷ Toff324 ∷ []) (Toff314 ∷ Sw12 ∷ []) (wl0063 c4)
  q194 : WsL → Eqn
  q194 c4 = eqn (Sw12 ∷ Bx2-30 ∷ []) (Bx1-30 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨2·30⟩ c4)

-- nat 1 BOX(3;240): 8 steps
lem-nat-1-BOX⟨3·240⟩ : WsL → ⟪ (Sw12 ∷ Bx3-240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-140 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨3·240⟩ c4 = derive (Sw12 ∷ Bx3-240 ∷ []) (Bx3-140 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) ∷
   rw⁻ 0 (q192 c4) ∷
   rw 1 (q193 c4) ∷
   rw 2 (q194 c4) ∷
   rw 3 (q193 c4) ∷
   rw⁻ 4 (q192 c4) ∷
   rw 5 (q194 c4) ∷
   re 0 6 (Bx3-140 ∷ []) ∷ []) Eq.refl

private
  q195 : WsL → Eqn
  q195 c4 = eqn (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) (wl0112 c4)
  q196 : WsL → Eqn
  q196 c4 = eqn (Sw12 ∷ Bx3-240 ∷ []) (Bx3-140 ∷ Sw12 ∷ []) (lem-nat-1-BOX⟨3·240⟩ c4)

-- nat 1 BOX(2;3140): 8 steps
lem-nat-1-BOX⟨2·3140⟩ : WsL → ⟪ (Sw12 ∷ Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-3240 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-BOX⟨2·3140⟩ c4 = derive (Sw12 ∷ Bx2-3140 ∷ []) (Bx1-3240 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ []) ∷
   rw⁻ 0 (q186 c4) ∷
   rw 1 (q195 c4) ∷
   rw 2 (q196 c4) ∷
   rw 3 (q195 c4) ∷
   rw⁻ 4 (q186 c4) ∷
   rw 5 (q196 c4) ∷
   re 0 6 (Bx1-3240 ∷ []) ∷ []) Eq.refl

-- nat 1 SBOX(2;3;0;4): 3 steps
lem-nat-1-SBOX⟨2·3·0·4⟩ : WsL → ⟪ (Sw12 ∷ Sb2-3-0-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb1-3-0-4 ∷ Sw12 ∷ []) ⟫ʷ
lem-nat-1-SBOX⟨2·3·0·4⟩ c4 = derive (Sw12 ∷ Sb2-3-0-4 ∷ []) (Sb1-3-0-4 ∷ Sw12 ∷ [])
  (re 1 1 (CS03 ∷ []) ∷
   rw⁻ 0 (q24 c4) ∷
   re 0 1 (Sb1-3-0-4 ∷ []) ∷ []) Eq.refl
