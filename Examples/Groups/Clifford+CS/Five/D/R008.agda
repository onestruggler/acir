{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R008 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0003 ; wl0004 ; wl0005 ; wl0006 ; wl0007 ; wl0008 ; wl0009 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0016 ; wl0017 ; wl0025 ; wl0026 ; wl0027 ; wl0028 ; wl0039 ; wl0046 ; wl0048 ; wl0064 ; wl0065 ; wl0066 ; wl0067 ; wl0068 ; wl0073 ; wl0109 ; wl0115 ; wl0117 ; wl0118 ; wl0119 ; wl0122 ; wl0123 ; wl0124 ; wl0125 ; wl0134 ; wl0135 ; wl0136 ; wl0137 ; wl0138 ; wl0141 ; wl0142 ; wl0040 ; wl0044 ; wl0083 ; wl0120 ; wl0128 ; wl0129 ; wl0149)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-push-CS04-sw1-R ; lem-comm-push-CS04-sw2-R)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-push-BOX⟨0·21⟩-sw0-R ; lem-comm-push-BOX⟨1·20⟩-sw1-R ; lem-comm-push-BOX⟨1·230⟩-sw2-R ; lem-comm-push-BOX⟨1·320⟩-sw3-R ; lem-comm-push-BOX⟨1·420⟩-sw2-R ; lem-comm-push-BOX⟨2·03⟩-sw2-R ; lem-comm-push-BOX⟨4·03⟩-sw1-R ; lem-comm-push-BOX⟨4·103⟩-sw1-R ; lem-comm-push-BOX⟨4·10⟩-sw1-R ; lem-comm-push-BOX⟨4·20⟩-sw0-R ; lem-comm-push-CS04-sw0-R ; lem-comm-push-CS14-sw0-R ; lem-comm-push-CSd14-sw0-R ; lem-comm-push-CX04-sw1-R ; lem-comm-push-CX04-sw2-R)

private
  q1 : WsL → Eqn
  q1 c4 = eqn (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ []) (wl0064 c4)
  q2 : WsL → Eqn
  q2 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0003 c4)
  q3 : WsL → Eqn
  q3 c4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap))
  q4 : WsL → Eqn
  q4 c4 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (c₁ (iI) (Swap ↑))
  q5 : WsL → Eqn
  q5 c4 = eqn (K4 ∷ Sw34 ∷ []) (Sw34 ∷ K3 ∷ []) (wl0065 c4)
  q6 : WsL → Eqn
  q6 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0004 c4)
  q7 : WsL → Eqn
  q7 c4 = eqn (CX01 ∷ Sw34 ∷ []) (Sw34 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap ↑))
  q8 : WsL → Eqn
  q8 c4 = eqn (ι ∷ Sw34 ∷ []) (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑))
  q9 : WsL → Eqn
  q9 c4 = eqn (Sw23 ∷ K4 ∷ []) (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K))
  q10 : WsL → Eqn
  q10 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl0017 c4)
  q11 : WsL → Eqn
  q11 c4 = eqn (CS14⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS14⁻ ∷ []) (wl0048 c4)
  q12 : WsL → Eqn
  q12 c4 = eqn (Sw23 ∷ CS04 ∷ []) (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4)
  q13 : WsL → Eqn
  q13 c4 = eqn (K3 ∷ Sw34 ∷ []) (Sw34 ∷ K4 ∷ []) (wl0066 c4)
  q14 : WsL → Eqn
  q14 c4 = eqn (K2 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ []) (wl0067 c4)

-- comm push TOFF401 sw2 R: 62 steps
lem-comm-push-TOFF401-sw2-R : WsL → ⟪ (Sw23 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-TOFF401-sw2-R c4 = derive (Sw23 ∷ Toff401 ∷ []) (Toff401 ∷ Sw23 ∷ [])
  (re 1 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) ∷
   re 2 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
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
   rw 0 (q9 c4) ∷
   rw⁻ 1 (q10 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 3 (q11 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   rw 5 (q12 c4) ∷
   rw 6 (q9 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   rw⁻ 1 (q13 c4) ∷
   re 3 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 2 (q6 c4) ∷
   rw⁻ 3 (q7 c4) ∷
   re 5 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 (q2 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 (q2 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   re 2 8 (Toff201 ∷ []) ∷
   re 1 3 (Toff301 ∷ []) ∷
   re 0 3 (Toff401 ∷ []) ∷ []) Eq.refl

private
  q15 : WsL → Eqn
  q15 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0005 c4)
  q16 : WsL → Eqn
  q16 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0006 c4)
  q17 : WsL → Eqn
  q17 c4 = eqn (CS24⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS14⁻ ∷ []) (wl0007 c4)
  q18 : WsL → Eqn
  q18 c4 = eqn (Sw12 ∷ CS04 ∷ []) (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4)
  q19 : WsL → Eqn
  q19 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q20 : WsL → Eqn
  q20 c4 = eqn (CX12 ∷ Sw01 ∷ []) (Sw01 ∷ CX02 ∷ []) (wl0117 c4)
  q21 : WsL → Eqn
  q21 c4 = eqn (Sw01 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q22 : WsL → Eqn
  q22 c4 = eqn (Sw01 ∷ CS04 ∷ []) (CS14 ∷ Sw01 ∷ []) (lem-comm-push-CS04-sw0-R c4)
  q23 : WsL → Eqn
  q23 c4 = eqn (CX12 ∷ Sw34 ∷ []) (Sw34 ∷ CX12 ∷ []) (c₃ (CX₀₁ ↑) (Swap))

-- comm push CCZ024 sw0 R: 46 steps
lem-comm-push-CCZ024-sw0-R : WsL → ⟪ (Sw01 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-CCZ024-sw0-R c4 = derive (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ [])
  (re 1 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
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
   rw⁻ 1 (q15 c4) ∷
   rw⁻ 4 (q16 c4) ∷
   re 2 3 (CX02 ∷ []) ∷
   rw⁻ 3 (q17 c4) ∷
   rw⁻ 6 (q16 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 (q18 c4) ∷
   rw 6 (q16 c4) ∷
   rw 0 (q19 c4) ∷
   rw⁻ 1 (q20 c4) ∷
   rw 2 (q21 c4) ∷
   rw⁻ 3 (q20 c4) ∷
   rw 4 (q22 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   re 2 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 1 (q6 c4) ∷
   rw⁻ 2 (q23 c4) ∷
   re 4 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q23 c4) ∷
   re 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   re 1 5 (CCZ123 ∷ []) ∷
   re 0 3 (CCZ124 ∷ []) ∷ []) Eq.refl

private
  q24 : WsL → Eqn
  q24 c4 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (c₁ (K) (Swap ↑))
  q25 : WsL → Eqn
  q25 c4 = eqn (K0 ∷ Sw34 ∷ []) (Sw34 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑))
  q26 : WsL → Eqn
  q26 c4 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (c₁ (K) (Swap))
  q27 : WsL → Eqn
  q27 c4 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap))
  q28 : WsL → Eqn
  q28 c4 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wl0109 c4)
  q29 : WsL → Eqn
  q29 c4 = eqn (Sw01 ∷ ι ∷ []) (ι ∷ Sw01 ∷ []) (wl0025 c4)
  q30 : WsL → Eqn
  q30 c4 = eqn (K1 ∷ Sw34 ∷ []) (Sw34 ∷ K1 ∷ []) (c₂ (K ↑) (Swap ↑))
  q31 : WsL → Eqn
  q31 c4 = eqn (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wl0027 c4)

-- comm push TOFF024 sw0 R: 62 steps
lem-comm-push-TOFF024-sw0-R : WsL → ⟪ (Sw01 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-TOFF024-sw0-R c4 = derive (Sw01 ∷ Toff024 ∷ []) (Toff124 ∷ Sw01 ∷ [])
  (re 1 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 (q24 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q3 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q3 c4) ∷
   rw⁻ 10 (q2 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 (q24 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw 11 (q2 c4) ∷
   rw⁻ 2 (q25 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q7 c4) ∷
   rw⁻ 9 (q6 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q25 c4) ∷
   rw⁻ 9 (q8 c4) ∷
   rw 10 (q6 c4) ∷
   rw⁻ 1 (q26 c4) ∷
   rw⁻ 2 (q15 c4) ∷
   rw⁻ 5 (q16 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q17 c4) ∷
   rw⁻ 7 (q16 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 (q18 c4) ∷
   rw⁻ 7 (q26 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw 9 (q16 c4) ∷
   rw⁻ 0 (q28 c4) ∷
   rw 1 (q19 c4) ∷
   rw⁻ 2 (q20 c4) ∷
   rw 3 (q21 c4) ∷
   rw⁻ 4 (q20 c4) ∷
   rw 5 (q22 c4) ∷
   rw⁻ 6 (q28 c4) ∷
   rw 7 (q29 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   rw⁻ 1 (q30 c4) ∷
   re 3 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 2 (q6 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   re 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q23 c4) ∷
   re 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q30 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw 1 (q31 c4) ∷
   re 1 8 (Toff123 ∷ []) ∷
   re 0 3 (Toff124 ∷ []) ∷ []) Eq.refl

private
  q32 : WsL → Eqn
  q32 c4 = eqn (Sw01 ∷ K4 ∷ []) (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑))
  q33 : WsL → Eqn
  q33 c4 = eqn (Sw01 ∷ CS14 ∷ []) (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R c4)
  q34 : WsL → Eqn
  q34 c4 = eqn (CX10 ∷ Sw01 ∷ []) (Sw01 ∷ CX01 ∷ []) (wl0115 c4)
  q35 : WsL → Eqn
  q35 c4 = eqn (Sw01 ∷ CS14⁻ ∷ []) (CS04⁻ ∷ Sw01 ∷ []) (lem-comm-push-CSd14-sw0-R c4)
  q36 : WsL → Eqn
  q36 c4 = eqn (CX10 ∷ Sw34 ∷ []) (Sw34 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Swap ↑))
  q37 : WsL → Eqn
  q37 c4 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Swap))
  q38 : WsL → Eqn
  q38 c4 = eqn (K2 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (wl0124 c4)

-- comm push TOFF401 sw0 R: 63 steps
lem-comm-push-TOFF401-sw0-R : WsL → ⟪ (Sw01 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-TOFF401-sw0-R c4 = derive (Sw01 ∷ Toff401 ∷ []) (Toff401 ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) ∷
   re 2 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
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
   rw 0 (q32 c4) ∷
   rw 1 (q33 c4) ∷
   rw⁻ 2 (q34 c4) ∷
   rw 3 (q35 c4) ∷
   rw⁻ 4 (q34 c4) ∷
   rw 5 (q22 c4) ∷
   rw 6 (q32 c4) ∷
   rw 7 (q29 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   rw⁻ 1 (q13 c4) ∷
   re 3 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 2 (q6 c4) ∷
   rw⁻ 3 (q36 c4) ∷
   re 5 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q36 c4) ∷
   re 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 4 (q37 c4) ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 (q2 c4) ∷
   rw⁻ 6 (q37 c4) ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 (q2 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw 2 (q38 c4) ∷
   re 2 8 (Toff201 ∷ []) ∷
   re 1 3 (Toff301 ∷ []) ∷
   re 0 3 (Toff401 ∷ []) ∷ []) Eq.refl

private
  q39 : WsL → Eqn
  q39 c4 = eqn (CCZ124 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ124 ∷ []) (wl0122 c4)
  q40 : WsL → Eqn
  q40 c4 = eqn (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) (wl0123 c4)
  q41 : WsL → Eqn
  q41 c4 = eqn (Sw12 ∷ Bx4-103 ∷ []) (Bx4-203 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨4·103⟩-sw1-R c4)

-- comm push BOX(1;4203) sw1 R: 8 steps
lem-comm-push-BOX⟨1·4203⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx1-4203 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·4203⟩-sw1-R c4 = derive (Sw12 ∷ Bx1-4203 ∷ []) (Bx2-4103 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff124 ∷ Bx4-103 ∷ Toff124 ∷ CCZ124 ∷ Bx4-103 ∷ []) ∷
   rw⁻ 0 (q39 c4) ∷
   rw 1 (q40 c4) ∷
   rw 2 (q41 c4) ∷
   rw 3 (q40 c4) ∷
   rw⁻ 4 (q39 c4) ∷
   rw 5 (q41 c4) ∷
   re 0 6 (Bx2-4103 ∷ []) ∷ []) Eq.refl

private
  q42 : WsL → Eqn
  q42 c4 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wl0039 c4)
  q43 : WsL → Eqn
  q43 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl0013 c4)
  q44 : WsL → Eqn
  q44 c4 = eqn (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ []) (wl0014 c4)

-- comm push CCZ124 sw0 R: 46 steps
lem-comm-push-CCZ124-sw0-R : WsL → ⟪ (Sw01 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-CCZ124-sw0-R c4 = derive (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   re 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw⁻ 3 (q6 c4) ∷
   re 1 3 (CS24 ∷ []) ∷
   rw⁻ 2 (q23 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (CS24⁻ ∷ []) ∷
   rw⁻ 4 (q23 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (CS14 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw 0 (q19 c4) ∷
   rw⁻ 1 (q42 c4) ∷
   rw 2 (q21 c4) ∷
   rw⁻ 3 (q42 c4) ∷
   rw 4 (q33 c4) ∷
   rw⁻ 0 (q16 c4) ∷
   rw⁻ 1 (q43 c4) ∷
   re 3 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 2 (q16 c4) ∷
   rw⁻ 3 (q44 c4) ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 (q16 c4) ∷
   rw 5 (q18 c4) ∷
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
   re 0 3 (CCZ024 ∷ []) ∷ []) Eq.refl

private
  q45 : WsL → Eqn
  q45 c4 = eqn (K2 ∷ Sw34 ∷ []) (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap))
  q46 : WsL → Eqn
  q46 c4 = eqn (ι1 ∷ Sw34 ∷ []) (Sw34 ∷ ι1 ∷ []) (c₂ (iI ↑) (Swap ↑))
  q47 : WsL → Eqn
  q47 c4 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (c₂ (Swap) (K))
  q48 : WsL → Eqn
  q48 c4 = eqn (Sw01 ∷ ι1 ∷ []) (ι1 ∷ Sw01 ∷ []) (wl0118 c4)
  q49 : WsL → Eqn
  q49 c4 = eqn (K1 ∷ Sw12 ∷ []) (Sw12 ∷ K2 ∷ []) (wl0073 c4)
  q50 : WsL → Eqn
  q50 c4 = eqn (Sw12 ∷ ι1 ∷ []) (ι1 ∷ Sw12 ∷ []) (wl0119 c4)
  q51 : WsL → Eqn
  q51 c4 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (c₂ (K ↑) (Swap))
  q52 : WsL → Eqn
  q52 c4 = eqn (ι1 ∷ Sw23 ∷ []) (Sw23 ∷ ι1 ∷ []) (c₂ (iI ↑) (Swap))
  q53 : WsL → Eqn
  q53 c4 = eqn (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι1 ∷ []) (wl0134 c4)

-- comm push TOFF214 sw0 R: 62 steps
lem-comm-push-TOFF214-sw0-R : WsL → ⟪ (Sw01 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-TOFF214-sw0-R c4 = derive (Sw01 ∷ Toff214 ∷ []) (Toff204 ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ Toff213 ∷ Sw34 ∷ []) ∷
   re 2 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw⁻ 1 (q45 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (CS24 ∷ []) ∷
   rw⁻ 3 (q23 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CS24⁻ ∷ []) ∷
   rw⁻ 5 (q23 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 6 3 (CS14 ∷ []) ∷
   rw⁻ 7 (q45 c4) ∷
   rw⁻ 8 (q46 c4) ∷
   rw 9 (q6 c4) ∷
   rw 0 (q47 c4) ∷
   rw 1 (q19 c4) ∷
   rw⁻ 2 (q42 c4) ∷
   rw 3 (q21 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   rw 5 (q33 c4) ∷
   rw 6 (q47 c4) ∷
   rw 7 (q48 c4) ∷
   rw⁻ 0 (q16 c4) ∷
   rw⁻ 1 (q49 c4) ∷
   rw⁻ 2 (q43 c4) ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 3 (q16 c4) ∷
   rw⁻ 4 (q44 c4) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 (q16 c4) ∷
   rw 6 (q18 c4) ∷
   rw⁻ 7 (q49 c4) ∷
   rw 8 (q50 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   re 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   re 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q6 c4) ∷
   rw⁻ 8 (q30 c4) ∷
   rw⁻ 9 (q46 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw⁻ 3 (q51 c4) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 (q2 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q2 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 (q2 c4) ∷
   rw⁻ 9 (q51 c4) ∷
   rw⁻ 10 (q52 c4) ∷
   rw⁻ 3 (q53 c4) ∷
   re 3 8 (Toff102 ∷ []) ∷
   re 2 3 (Toff103 ∷ []) ∷
   re 1 3 (Toff104 ∷ []) ∷
   re 0 3 (Toff204 ∷ []) ∷ []) Eq.refl

private
  q54 : WsL → Eqn
  q54 c4 = eqn (Sw12 ∷ K4 ∷ []) (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑))
  q55 : WsL → Eqn
  q55 c4 = eqn (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (wl0068 c4)

-- comm push TOFF402 sw0 R: 62 steps
lem-comm-push-TOFF402-sw0-R : WsL → ⟪ (Sw01 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-TOFF402-sw0-R c4 = derive (Sw01 ∷ Toff402 ∷ []) (Toff412 ∷ Sw01 ∷ [])
  (re 1 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 4 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
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
   rw 1 (q54 c4) ∷
   rw⁻ 2 (q15 c4) ∷
   rw⁻ 5 (q16 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q17 c4) ∷
   rw⁻ 7 (q16 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 (q18 c4) ∷
   rw 7 (q54 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw 9 (q16 c4) ∷
   rw 0 (q32 c4) ∷
   rw 1 (q19 c4) ∷
   rw⁻ 2 (q20 c4) ∷
   rw 3 (q21 c4) ∷
   rw⁻ 4 (q20 c4) ∷
   rw 5 (q22 c4) ∷
   rw 6 (q32 c4) ∷
   rw 7 (q29 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   rw⁻ 1 (q13 c4) ∷
   re 3 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 2 (q6 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   re 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q23 c4) ∷
   re 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw 1 (q55 c4) ∷
   re 1 8 (Toff312 ∷ []) ∷
   re 0 3 (Toff412 ∷ []) ∷ []) Eq.refl

private
  q56 : WsL → Eqn
  q56 c4 = eqn (CCZ123 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ023 ∷ []) (wl0135 c4)
  q57 : WsL → Eqn
  q57 c4 = eqn (Sw01 ∷ Toff203 ∷ []) (Toff213 ∷ Sw01 ∷ []) (wl0136 c4)
  q58 : WsL → Eqn
  q58 c4 = eqn (Sw01 ∷ Bx0-21 ∷ []) (Bx1-20 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨0·21⟩-sw0-R c4)

-- comm push BOX(2;031) sw0 R: 8 steps
lem-comm-push-BOX⟨2·031⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx2-031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-130 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·031⟩-sw0-R c4 = derive (Sw01 ∷ Bx2-031 ∷ []) (Bx2-130 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) ∷
   rw⁻ 0 (q56 c4) ∷
   rw 1 (q57 c4) ∷
   rw 2 (q58 c4) ∷
   rw 3 (q57 c4) ∷
   rw⁻ 4 (q56 c4) ∷
   rw 5 (q58 c4) ∷
   re 0 6 (Bx2-130 ∷ []) ∷ []) Eq.refl

private
  q59 : WsL → Eqn
  q59 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl0008 c4)
  q60 : WsL → Eqn
  q60 c4 = eqn (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) (wl0009 c4)
  q61 : WsL → Eqn
  q61 c4 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wl0026 c4)
  q62 : WsL → Eqn
  q62 c4 = eqn (Sw01 ∷ CS34 ∷ []) (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))
  q63 : WsL → Eqn
  q63 c4 = eqn (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) (wl0016 c4)
  q64 : WsL → Eqn
  q64 c4 = eqn (Sw01 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑))
  q65 : WsL → Eqn
  q65 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl0011 c4)
  q66 : WsL → Eqn
  q66 c4 = eqn (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) (wl0012 c4)
  q67 : WsL → Eqn
  q67 c4 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι1 ∷ []) (wl0125 c4)

-- comm push TOFF134 sw0 R: 86 steps
lem-comm-push-TOFF134-sw0-R : WsL → ⟪ (Sw01 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-TOFF134-sw0-R c4 = derive (Sw01 ∷ Toff134 ∷ []) (Toff034 ∷ Sw01 ∷ [])
  (re 1 1 (Sw23 ∷ Toff124 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff123 ∷ Sw34 ∷ []) ∷
   re 3 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw⁻ 2 (q30 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (CS24 ∷ []) ∷
   rw⁻ 4 (q23 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (CS24⁻ ∷ []) ∷
   rw⁻ 6 (q23 c4) ∷
   rw⁻ 9 (q6 c4) ∷
   re 7 3 (CS14 ∷ []) ∷
   rw⁻ 8 (q30 c4) ∷
   rw⁻ 9 (q46 c4) ∷
   rw 10 (q6 c4) ∷
   rw⁻ 1 (q51 c4) ∷
   rw⁻ 2 (q59 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (CX13 ∷ []) ∷
   rw⁻ 4 (q60 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (CX13 ∷ []) ∷
   rw⁻ 6 (q10 c4) ∷
   rw⁻ 7 (q51 c4) ∷
   rw⁻ 8 (q52 c4) ∷
   rw 9 (q2 c4) ∷
   rw⁻ 0 (q61 c4) ∷
   rw 1 (q62 c4) ∷
   rw⁻ 2 (q63 c4) ∷
   rw 3 (q64 c4) ∷
   rw⁻ 4 (q63 c4) ∷
   rw 5 (q33 c4) ∷
   rw⁻ 6 (q61 c4) ∷
   rw 7 (q48 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw⁻ 1 (q24 c4) ∷
   rw⁻ 2 (q65 c4) ∷
   re 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 4 (q66 c4) ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 5 (q2 c4) ∷
   rw 6 (q12 c4) ∷
   rw⁻ 7 (q24 c4) ∷
   rw⁻ 8 (q52 c4) ∷
   rw⁻ 1 (q16 c4) ∷
   rw⁻ 2 (q26 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 (q16 c4) ∷
   rw⁻ 5 (q44 c4) ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 (q16 c4) ∷
   rw 7 (q18 c4) ∷
   rw⁻ 8 (q26 c4) ∷
   rw 9 (q50 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw⁻ 3 (q25 c4) ∷
   re 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   re 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 8 (q6 c4) ∷
   rw⁻ 9 (q25 c4) ∷
   rw⁻ 10 (q46 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 4 (q24 c4) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 (q2 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 (q2 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 (q2 c4) ∷
   rw⁻ 10 (q24 c4) ∷
   rw⁻ 11 (q52 c4) ∷
   rw⁻ 4 (q67 c4) ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 3 3 (Toff013 ∷ []) ∷
   re 2 3 (Toff014 ∷ []) ∷
   re 1 3 (Toff024 ∷ []) ∷
   re 0 3 (Toff034 ∷ []) ∷ []) Eq.refl

private
  q68 : WsL → Eqn
  q68 c4 = eqn (CCZ123 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ123 ∷ []) (wl0137 c4)
  q69 : WsL → Eqn
  q69 c4 = eqn (Sw12 ∷ Toff213 ∷ []) (Toff123 ∷ Sw12 ∷ []) (wl0138 c4)
  q70 : WsL → Eqn
  q70 c4 = eqn (Sw12 ∷ Bx1-20 ∷ []) (Bx2-10 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨1·20⟩-sw1-R c4)

-- comm push BOX(2;130) sw1 R: 8 steps
lem-comm-push-BOX⟨2·130⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx2-130 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-230 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·130⟩-sw1-R c4 = derive (Sw12 ∷ Bx2-130 ∷ []) (Bx1-230 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-20 ∷ Toff213 ∷ CCZ123 ∷ Bx1-20 ∷ []) ∷
   rw⁻ 0 (q68 c4) ∷
   rw 1 (q69 c4) ∷
   rw 2 (q70 c4) ∷
   rw 3 (q69 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   rw 5 (q70 c4) ∷
   re 0 6 (Bx1-230 ∷ []) ∷ []) Eq.refl

private
  q71 : WsL → Eqn
  q71 c4 = eqn (Sw23 ∷ Bx1-230 ∷ []) (Bx1-320 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨1·230⟩-sw2-R c4)

-- comm push BOX(2;1430) sw2 R: 12 steps
lem-comm-push-BOX⟨2·1430⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·1430⟩-sw2-R c4 = derive (Sw23 ∷ Bx2-1430 ∷ []) (Bx3-1420 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ124 ∷ Toff214 ∷ Bx1-230 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ []) ∷
   rw⁻ 2 (q2 c4) ∷
   re 0 3 (CCZ134 ∷ []) ∷
   rw⁻ 3 (q2 c4) ∷
   re 1 3 (Toff314 ∷ []) ∷
   rw 2 (q71 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (Toff314 ∷ []) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (CCZ134 ∷ []) ∷
   rw 5 (q71 c4) ∷
   re 0 6 (Bx3-1420 ∷ []) ∷ []) Eq.refl

private
  q72 : WsL → Eqn
  q72 c4 = eqn (CCZ134 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ134 ∷ []) (wl0141 c4)
  q73 : WsL → Eqn
  q73 c4 = eqn (Sw34 ∷ Toff314 ∷ []) (Toff413 ∷ Sw34 ∷ []) (wl0142 c4)
  q74 : WsL → Eqn
  q74 c4 = eqn (Sw34 ∷ Bx1-320 ∷ []) (Bx1-420 ∷ Sw34 ∷ []) (lem-comm-push-BOX⟨1·320⟩-sw3-R c4)

-- comm push BOX(3;1420) sw3 R: 8 steps
lem-comm-push-BOX⟨3·1420⟩-sw3-R : WsL → ⟪ (Sw34 ∷ Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨3·1420⟩-sw3-R c4 = derive (Sw34 ∷ Bx3-1420 ∷ []) (Bx4-1320 ∷ Sw34 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ []) ∷
   rw⁻ 0 (q72 c4) ∷
   rw 1 (q73 c4) ∷
   rw 2 (q74 c4) ∷
   rw 3 (q73 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   rw 5 (q74 c4) ∷
   re 0 6 (Bx4-1320 ∷ []) ∷ []) Eq.refl

private
  q75 : WsL → Eqn
  q75 c4 = eqn (CX02 ∷ Sw34 ∷ []) (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))
  q76 : WsL → Eqn
  q76 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl0046 c4)
  q77 : WsL → Eqn
  q77 c4 = eqn (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) (wl0028 c4)
  q78 : WsL → Eqn
  q78 c4 = eqn (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) (wl0001 c4)

-- comm push TOFF024 sw3 R: 76 steps
lem-comm-push-TOFF024-sw3-R : WsL → ⟪ (Sw34 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-TOFF024-sw3-R c4 = derive (Sw34 ∷ Toff024 ∷ []) (Toff023 ∷ Sw34 ∷ [])
  (re 1 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 (q24 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q3 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q3 c4) ∷
   rw⁻ 10 (q2 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 (q24 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw 11 (q2 c4) ∷
   rw⁻ 2 (q25 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q7 c4) ∷
   rw⁻ 9 (q6 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q25 c4) ∷
   rw⁻ 9 (q8 c4) ∷
   rw 10 (q6 c4) ∷
   rw⁻ 1 (q26 c4) ∷
   rw⁻ 2 (q15 c4) ∷
   rw⁻ 5 (q16 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q17 c4) ∷
   rw⁻ 7 (q16 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 (q18 c4) ∷
   rw⁻ 7 (q26 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw 9 (q16 c4) ∷
   rw⁻ 0 (q25 c4) ∷
   re 2 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 1 (q6 c4) ∷
   rw⁻ 2 (q75 c4) ∷
   re 4 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q75 c4) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q25 c4) ∷
   rw⁻ 7 (q8 c4) ∷
   rw⁻ 0 (q16 c4) ∷
   rw⁻ 1 (q26 c4) ∷
   rw⁻ 2 (q76 c4) ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 3 (q16 c4) ∷
   rw⁻ 4 (q77 c4) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 (q16 c4) ∷
   rw⁻ 6 (q78 c4) ∷
   rw⁻ 7 (q26 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   rw⁻ 2 (q24 c4) ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 (q2 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 (q2 c4) ∷
   rw⁻ 8 (q24 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   re 0 3 (Toff023 ∷ []) ∷ []) Eq.refl

private
  q79 : WsL → Eqn
  q79 c4 = eqn (Sw23 ∷ Bx1-420 ∷ []) (Bx1-430 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨1·420⟩-sw2-R c4)

-- comm push BOX(4;1320) sw2 R: 12 steps
lem-comm-push-BOX⟨4·1320⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx4-1320 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·1320⟩-sw2-R c4 = derive (Sw23 ∷ Bx4-1320 ∷ []) (Bx4-1230 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff413 ∷ Bx1-420 ∷ Toff413 ∷ CCZ134 ∷ Bx1-420 ∷ []) ∷
   re 1 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 0 (q2 c4) ∷
   re 2 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q79 c4) ∷
   re 4 1 (Sw23 ∷ Toff412 ∷ Sw23 ∷ []) ∷
   rw 3 (q2 c4) ∷
   re 5 1 (Sw23 ∷ CCZ124 ∷ Sw23 ∷ []) ∷
   rw 4 (q2 c4) ∷
   rw 5 (q79 c4) ∷
   re 0 6 (Bx4-1230 ∷ []) ∷ []) Eq.refl

private
  q80 : WsL → Eqn
  q80 c4 = eqn (CCZ234 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ134 ∷ []) (wl0044 c4)
  q81 : WsL → Eqn
  q81 c4 = eqn (Sw12 ∷ Toff134 ∷ []) (Toff234 ∷ Sw12 ∷ []) (wl0083 c4)
  q82 : WsL → Eqn
  q82 c4 = eqn (Sw12 ∷ Bx4-10 ∷ []) (Bx4-20 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨4·10⟩-sw1-R c4)

-- comm push BOX(1;430) sw1 R: 8 steps
lem-comm-push-BOX⟨1·430⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx1-430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-430 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·430⟩-sw1-R c4 = derive (Sw12 ∷ Bx1-430 ∷ []) (Bx2-430 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) ∷
   rw⁻ 0 (q80 c4) ∷
   rw 1 (q81 c4) ∷
   rw 2 (q82 c4) ∷
   rw 3 (q81 c4) ∷
   rw⁻ 4 (q80 c4) ∷
   rw 5 (q82 c4) ∷
   re 0 6 (Bx2-430 ∷ []) ∷ []) Eq.refl

private
  q83 : WsL → Eqn
  q83 c4 = eqn (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι1 ∷ []) (wl0120 c4)

-- comm push TOFF412 sw0 R: 62 steps
lem-comm-push-TOFF412-sw0-R : WsL → ⟪ (Sw01 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-TOFF412-sw0-R c4 = derive (Sw01 ∷ Toff412 ∷ []) (Toff402 ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) ∷
   re 2 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw⁻ 1 (q5 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (CS24 ∷ []) ∷
   rw⁻ 3 (q23 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CS24⁻ ∷ []) ∷
   rw⁻ 5 (q23 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 6 3 (CS14 ∷ []) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 8 (q46 c4) ∷
   rw 9 (q6 c4) ∷
   rw 0 (q32 c4) ∷
   rw 1 (q19 c4) ∷
   rw⁻ 2 (q42 c4) ∷
   rw 3 (q21 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   rw 5 (q33 c4) ∷
   rw 6 (q32 c4) ∷
   rw 7 (q48 c4) ∷
   rw⁻ 0 (q16 c4) ∷
   rw 1 (q54 c4) ∷
   rw⁻ 2 (q43 c4) ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 3 (q16 c4) ∷
   rw⁻ 4 (q44 c4) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 (q16 c4) ∷
   rw 6 (q18 c4) ∷
   rw 7 (q54 c4) ∷
   rw 8 (q50 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw⁻ 2 (q13 c4) ∷
   re 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   re 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q6 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw⁻ 9 (q46 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 (q2 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q2 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 (q2 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw⁻ 10 (q52 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   re 3 8 (Toff201 ∷ []) ∷
   re 2 3 (Toff301 ∷ []) ∷
   re 1 3 (Toff401 ∷ []) ∷
   re 0 3 (Toff402 ∷ []) ∷ []) Eq.refl

private
  q84 : WsL → Eqn
  q84 c4 = eqn (Sw01 ∷ CCZ234 ∷ []) (CCZ234 ∷ Sw01 ∷ []) (c₂ (Swap) (CCZ))
  q85 : WsL → Eqn
  q85 c4 = eqn (Sw01 ∷ Toff234 ∷ []) (Toff234 ∷ Sw01 ∷ []) (c₂ (Swap) (Toff))
  q86 : WsL → Eqn
  q86 c4 = eqn (Sw01 ∷ Bx4-20 ∷ []) (Bx4-21 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨4·20⟩-sw0-R c4)

-- comm push BOX(2;430) sw0 R: 8 steps
lem-comm-push-BOX⟨2·430⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx2-430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-431 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·430⟩-sw0-R c4 = derive (Sw01 ∷ Bx2-430 ∷ []) (Bx2-431 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) ∷
   rw 0 (q84 c4) ∷
   rw 1 (q85 c4) ∷
   rw 2 (q86 c4) ∷
   rw 3 (q85 c4) ∷
   rw 4 (q84 c4) ∷
   rw 5 (q86 c4) ∷
   re 0 6 (Bx2-431 ∷ []) ∷ []) Eq.refl

private
  q87 : WsL → Eqn
  q87 c4 = eqn (Sw23 ∷ Bx2-03 ∷ []) (Bx3-02 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨2·03⟩-sw2-R c4)

-- comm push BOX(0;213) sw2 R: 12 steps
lem-comm-push-BOX⟨0·213⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx0-213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-312 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·213⟩-sw2-R c4 = derive (Sw23 ∷ Bx0-213 ∷ []) (Bx0-312 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   rw⁻ 2 (q2 c4) ∷
   re 0 3 (CCZ013 ∷ []) ∷
   rw⁻ 3 (q2 c4) ∷
   re 1 3 (Toff013 ∷ []) ∷
   rw 2 (q87 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (Toff013 ∷ []) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (CCZ013 ∷ []) ∷
   rw 5 (q87 c4) ∷
   re 0 6 (Bx0-312 ∷ []) ∷ []) Eq.refl

private
  q88 : WsL → Eqn
  q88 c4 = eqn (K2 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ []) (wl0040 c4)
  q89 : WsL → Eqn
  q89 c4 = eqn (CS34 ∷ Sw34 ∷ []) (Sw34 ∷ CS34 ∷ []) (wl0129 c4)
  q90 : WsL → Eqn
  q90 c4 = eqn (CS34⁻ ∷ Sw34 ∷ []) (Sw34 ∷ CS34⁻ ∷ []) (wl0128 c4)
  q91 : WsL → Eqn
  q91 c4 = eqn (Sw23 ∷ CX04 ∷ []) (CX04 ∷ Sw23 ∷ []) (lem-comm-push-CX04-sw2-R c4)
  q92 : WsL → Eqn
  q92 c4 = eqn (Sw12 ∷ CX04 ∷ []) (CX04 ∷ Sw12 ∷ []) (lem-comm-push-CX04-sw1-R c4)
  q93 : WsL → Eqn
  q93 c4 = eqn (CS01 ∷ Sw34 ∷ []) (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑))
  q94 : WsL → Eqn
  q94 c4 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (c₂ (CS) (Swap))
  q95 : WsL → Eqn
  q95 c4 = eqn (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K2 ∷ ι ∷ []) (wl0149 c4)

-- comm push TOFF304 sw3 R: 114 steps
lem-comm-push-TOFF304-sw3-R : WsL → ⟪ (Sw34 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-TOFF304-sw3-R c4 = derive (Sw34 ∷ Toff304 ∷ []) (Toff403 ∷ Sw34 ∷ [])
  (re 1 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) ∷
   re 3 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) ∷
   re 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 4 (q51 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 (q3 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 (q3 c4) ∷
   rw⁻ 11 (q2 c4) ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 (q51 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw 12 (q2 c4) ∷
   rw⁻ 3 (q30 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CS14 ∷ []) ∷
   rw⁻ 5 (q7 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 6 3 (CS14⁻ ∷ []) ∷
   rw⁻ 7 (q7 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   re 8 3 (CS04 ∷ []) ∷
   rw⁻ 9 (q30 c4) ∷
   rw⁻ 10 (q8 c4) ∷
   rw 11 (q6 c4) ∷
   rw⁻ 2 (q88 c4) ∷
   rw⁻ 3 (q15 c4) ∷
   rw⁻ 6 (q16 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw⁻ 5 (q17 c4) ∷
   rw⁻ 8 (q16 c4) ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 7 (q18 c4) ∷
   rw⁻ 8 (q88 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw 10 (q16 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q59 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (CX03 ∷ []) ∷
   rw⁻ 4 (q60 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (CX03 ∷ []) ∷
   rw 6 (q12 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw 9 (q2 c4) ∷
   rw⁻ 0 (q5 c4) ∷
   rw⁻ 1 (q89 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (CX04 ∷ []) ∷
   rw⁻ 3 (q90 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CX04 ∷ []) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw⁻ 7 (q8 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw 1 (q9 c4) ∷
   rw⁻ 2 (q65 c4) ∷
   rw 3 (q91 c4) ∷
   rw⁻ 4 (q66 c4) ∷
   rw 5 (q91 c4) ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 (q2 c4) ∷
   rw 7 (q9 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw⁻ 1 (q16 c4) ∷
   rw 2 (q54 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   rw 4 (q92 c4) ∷
   rw⁻ 5 (q44 c4) ∷
   rw 6 (q92 c4) ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 7 (q16 c4) ∷
   rw 8 (q54 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw⁻ 3 (q13 c4) ∷
   re 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 4 (q6 c4) ∷
   re 6 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   re 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   re 8 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 7 (q6 c4) ∷
   rw⁻ 8 (q93 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw⁻ 10 (q8 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 (q2 c4) ∷
   re 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 6 (q2 c4) ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 (q2 c4) ∷
   re 9 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 8 (q2 c4) ∷
   rw⁻ 9 (q94 c4) ∷
   rw⁻ 10 (q14 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw⁻ 4 (q95 c4) ∷
   re 4 8 (Toff201 ∷ []) ∷
   re 3 3 (Toff301 ∷ []) ∷
   re 2 3 (Toff401 ∷ []) ∷
   re 1 3 (Toff402 ∷ []) ∷
   re 0 3 (Toff403 ∷ []) ∷ []) Eq.refl

private
  q96 : WsL → Eqn
  q96 c4 = eqn (Sw12 ∷ Bx4-03 ∷ []) (Bx4-03 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨4·03⟩-sw1-R c4)

-- comm push BOX(0;413) sw1 R: 12 steps
lem-comm-push-BOX⟨0·413⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx0-413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-423 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·413⟩-sw1-R c4 = derive (Sw12 ∷ Bx0-413 ∷ []) (Bx0-423 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ CCZ014 ∷ Bx4-03 ∷ []) ∷
   rw⁻ 2 (q16 c4) ∷
   re 0 3 (CCZ024 ∷ []) ∷
   rw⁻ 3 (q16 c4) ∷
   re 1 3 (Toff024 ∷ []) ∷
   rw 2 (q96 c4) ∷
   rw⁻ 5 (q16 c4) ∷
   re 3 3 (Toff024 ∷ []) ∷
   rw⁻ 6 (q16 c4) ∷
   re 4 3 (CCZ024 ∷ []) ∷
   rw 5 (q96 c4) ∷
   re 0 6 (Bx0-423 ∷ []) ∷ []) Eq.refl
