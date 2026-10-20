{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R007 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl0001 ; wl0003 ; wl0004 ; wl0006 ; wl0008 ; wl0009 ; wl0011 ; wl0012 ; wl0013 ; wl0014 ; wl0025 ; wl0064 ; wl0065 ; wl0066 ; wl0067 ; wl0101 ; wl0102 ; wl0103 ; wl0104 ; wl0107 ; wl0108 ; wl0109 ; wl0115 ; wl0116 ; wl0117 ; wl0118 ; wl0119 ; wl0120 ; wl0122 ; wl0123 ; wl0124 ; wl0005 ; wl0007 ; wl0010 ; wl0029 ; wl0047 ; wl0125 ; wl0128 ; wl0129 ; wl0130 ; wl0131 ; wl0132 ; wl0133)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-push-CS04-sw0-L ; lem-comm-push-CS04-sw1-R ; lem-comm-push-CS04-sw2-R)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-push-BOX⟨0·13⟩-sw0-R ; lem-comm-push-BOX⟨0·21⟩-sw2-R ; lem-comm-push-BOX⟨0·31⟩-sw2-L ; lem-comm-push-BOX⟨0·41⟩-sw1-R ; lem-comm-push-BOX⟨0·42⟩-sw1-L ; lem-comm-push-BOX⟨1·03⟩-sw1-R ; lem-comm-push-BOX⟨4·203⟩-sw1-L ; lem-comm-push-CS04-sw0-R ; lem-comm-push-CS14-sw0-L ; lem-comm-push-CS14-sw0-R ; lem-comm-push-CSd14-sw0-L ; lem-comm-push-CSd14-sw0-R ; lem-comm-push-CX04-sw1-R ; lem-comm-push-CX04-sw2-R)

private
  q1 : WsL → Eqn
  q1 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl0003 c4)
  q2 : WsL → Eqn
  q2 c4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap))
  q3 : WsL → Eqn
  q3 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0004 c4)
  q4 : WsL → Eqn
  q4 c4 = eqn (CX01 ∷ Sw34 ∷ []) (Sw34 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap ↑))
  q5 : WsL → Eqn
  q5 c4 = eqn (Sw01 ∷ CS14 ∷ []) (CS04 ∷ Sw01 ∷ []) (lem-comm-push-CS14-sw0-R c4)
  q6 : WsL → Eqn
  q6 c4 = eqn (CX10 ∷ Sw01 ∷ []) (Sw01 ∷ CX01 ∷ []) (wl0115 c4)
  q7 : WsL → Eqn
  q7 c4 = eqn (Sw01 ∷ CS14⁻ ∷ []) (CS04⁻ ∷ Sw01 ∷ []) (lem-comm-push-CSd14-sw0-R c4)
  q8 : WsL → Eqn
  q8 c4 = eqn (Sw01 ∷ CS04 ∷ []) (CS14 ∷ Sw01 ∷ []) (lem-comm-push-CS04-sw0-R c4)
  q9 : WsL → Eqn
  q9 c4 = eqn (CX10 ∷ Sw34 ∷ []) (Sw34 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Swap ↑))
  q10 : WsL → Eqn
  q10 c4 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Swap))
  q11 : WsL → Eqn
  q11 c4 = eqn (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0108 c4)

-- comm push CCZ014 sw0 R: 48 steps
lem-comm-push-CCZ014-sw0-R : WsL → ⟪ (Sw01 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-CCZ014-sw0-R c4 = derive (Sw01 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 (q1 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   re 1 3 (CS14 ∷ []) ∷
   rw⁻ 2 (q4 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (CS14⁻ ∷ []) ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw 6 (q3 c4) ∷
   rw 0 (q5 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw 2 (q7 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw 4 (q8 c4) ∷
   rw⁻ 0 (q3 c4) ∷
   re 2 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 1 (q3 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 4 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw 3 (q3 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   re 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 (q1 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   re 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q10 c4) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw 2 (q11 c4) ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   re 0 3 (CCZ014 ∷ []) ∷ []) Eq.refl

private
  q12 : WsL → Eqn
  q12 c4 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (c₁ (K) (Swap ↑))
  q13 : WsL → Eqn
  q13 c4 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (c₁ (iI) (Swap ↑))
  q14 : WsL → Eqn
  q14 c4 = eqn (K0 ∷ Sw34 ∷ []) (Sw34 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑))
  q15 : WsL → Eqn
  q15 c4 = eqn (ι ∷ Sw34 ∷ []) (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑))
  q16 : WsL → Eqn
  q16 c4 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wl0109 c4)
  q17 : WsL → Eqn
  q17 c4 = eqn (Sw01 ∷ ι ∷ []) (ι ∷ Sw01 ∷ []) (wl0025 c4)
  q18 : WsL → Eqn
  q18 c4 = eqn (K1 ∷ Sw34 ∷ []) (Sw34 ∷ K1 ∷ []) (c₂ (K ↑) (Swap ↑))
  q19 : WsL → Eqn
  q19 c4 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (c₂ (K ↑) (Swap))
  q20 : WsL → Eqn
  q20 c4 = eqn (K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wl0116 c4)

-- comm push TOFF014 sw0 R: 63 steps
lem-comm-push-TOFF014-sw0-R : WsL → ⟪ (Sw01 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-TOFF014-sw0-R c4 = derive (Sw01 ∷ Toff014 ∷ []) (Toff104 ∷ Sw01 ∷ [])
  (re 1 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   re 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 (q12 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 (q2 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 (q12 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw 10 (q1 c4) ∷
   rw⁻ 1 (q14 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 2 3 (CS14 ∷ []) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (CS14⁻ ∷ []) ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q14 c4) ∷
   rw⁻ 8 (q15 c4) ∷
   rw 9 (q3 c4) ∷
   rw⁻ 0 (q16 c4) ∷
   rw 1 (q5 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   rw 5 (q8 c4) ∷
   rw⁻ 6 (q16 c4) ∷
   rw 7 (q17 c4) ∷
   rw⁻ 0 (q3 c4) ∷
   rw⁻ 1 (q18 c4) ∷
   re 3 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 2 (q3 c4) ∷
   rw⁻ 3 (q9 c4) ∷
   re 5 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   re 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 6 (q3 c4) ∷
   rw⁻ 7 (q18 c4) ∷
   rw⁻ 8 (q15 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q19 c4) ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 4 (q10 c4) ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 6 (q10 c4) ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 (q1 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw 2 (q20 c4) ∷
   re 2 8 (Toff102 ∷ []) ∷
   re 1 3 (Toff103 ∷ []) ∷
   re 0 3 (Toff104 ∷ []) ∷ []) Eq.refl

private
  q21 : WsL → Eqn
  q21 c4 = eqn (CCZ012 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ012 ∷ []) (wl0103 c4)
  q22 : WsL → Eqn
  q22 c4 = eqn (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) (wl0104 c4)
  q23 : WsL → Eqn
  q23 c4 = eqn (Sw01 ∷ Bx0-13 ∷ []) (Bx1-03 ∷ Sw01 ∷ []) (lem-comm-push-BOX⟨0·13⟩-sw0-R c4)

-- comm push BOX(1;023) sw0 R: 8 steps
lem-comm-push-BOX⟨1·023⟩-sw0-R : WsL → ⟪ (Sw01 ∷ Bx1-023 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-123 ∷ Sw01 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·023⟩-sw0-R c4 = derive (Sw01 ∷ Bx1-023 ∷ []) (Bx0-123 ∷ Sw01 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) ∷
   rw⁻ 0 (q21 c4) ∷
   rw 1 (q22 c4) ∷
   rw 2 (q23 c4) ∷
   rw 3 (q22 c4) ∷
   rw⁻ 4 (q21 c4) ∷
   rw 5 (q23 c4) ∷
   re 0 6 (Bx0-123 ∷ []) ∷ []) Eq.refl

private
  q24 : WsL → Eqn
  q24 c4 = eqn (CCZ012 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ012 ∷ []) (wl0101 c4)
  q25 : WsL → Eqn
  q25 c4 = eqn (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) (wl0102 c4)
  q26 : WsL → Eqn
  q26 c4 = eqn (Sw12 ∷ Bx1-03 ∷ []) (Bx2-03 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨1·03⟩-sw1-R c4)

-- comm push BOX(0;123) sw1 R: 8 steps
lem-comm-push-BOX⟨0·123⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx0-123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-213 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·123⟩-sw1-R c4 = derive (Sw12 ∷ Bx0-123 ∷ []) (Bx0-213 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ012 ∷ Toff012 ∷ Bx1-03 ∷ Toff012 ∷ CCZ012 ∷ Bx1-03 ∷ []) ∷
   rw⁻ 0 (q24 c4) ∷
   rw 1 (q25 c4) ∷
   rw 2 (q26 c4) ∷
   rw 3 (q25 c4) ∷
   rw⁻ 4 (q24 c4) ∷
   rw 5 (q26 c4) ∷
   re 0 6 (Bx0-213 ∷ []) ∷ []) Eq.refl

private
  q27 : WsL → Eqn
  q27 c4 = eqn (CX12 ∷ Sw34 ∷ []) (Sw34 ∷ CX12 ∷ []) (c₃ (CX₀₁ ↑) (Swap))
  q28 : WsL → Eqn
  q28 c4 = eqn (CS14 ∷ Sw01 ∷ []) (Sw01 ∷ CS04 ∷ []) (lem-comm-push-CS14-sw0-L c4)
  q29 : WsL → Eqn
  q29 c4 = eqn (CX12 ∷ Sw01 ∷ []) (Sw01 ∷ CX02 ∷ []) (wl0117 c4)
  q30 : WsL → Eqn
  q30 c4 = eqn (Sw01 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q31 : WsL → Eqn
  q31 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q32 : WsL → Eqn
  q32 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0006 c4)
  q33 : WsL → Eqn
  q33 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl0013 c4)
  q34 : WsL → Eqn
  q34 c4 = eqn (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ []) (wl0014 c4)
  q35 : WsL → Eqn
  q35 c4 = eqn (Sw12 ∷ CS04 ∷ []) (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4)

-- comm push CCZ124 sw0 L: 46 steps
lem-comm-push-CCZ124-sw0-L : WsL → ⟪ (CCZ124 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ024 ∷ []) ⟫ʷ
lem-comm-push-CCZ124-sw0-L c4 = derive (CCZ124 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ024 ∷ [])
  (re 0 1 (Sw34 ∷ CCZ123 ∷ Sw34 ∷ []) ∷
   re 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw⁻ 2 (q3 c4) ∷
   re 0 3 (CS24 ∷ []) ∷
   rw⁻ 1 (q27 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 2 3 (CS24⁻ ∷ []) ∷
   rw⁻ 3 (q27 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (CS14 ∷ []) ∷
   rw 5 (q3 c4) ∷
   rw 4 (q28 c4) ∷
   rw 3 (q29 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw 1 (q29 c4) ∷
   rw⁻ 0 (q31 c4) ∷
   rw⁻ 1 (q32 c4) ∷
   rw⁻ 2 (q33 c4) ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 3 (q32 c4) ∷
   rw⁻ 4 (q34 c4) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 (q32 c4) ∷
   rw 6 (q35 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   re 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 3 (q3 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   re 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q3 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 (q1 c4) ∷
   re 4 5 (CCZ012 ∷ []) ∷
   re 3 3 (CCZ013 ∷ []) ∷
   re 2 3 (CCZ014 ∷ []) ∷
   re 1 3 (CCZ024 ∷ []) ∷ []) Eq.refl

private
  q36 : WsL → Eqn
  q36 c4 = eqn (K4 ∷ Sw34 ∷ []) (Sw34 ∷ K3 ∷ []) (wl0065 c4)
  q37 : WsL → Eqn
  q37 c4 = eqn (ι1 ∷ Sw34 ∷ []) (Sw34 ∷ ι1 ∷ []) (c₂ (iI ↑) (Swap ↑))
  q38 : WsL → Eqn
  q38 c4 = eqn (Sw01 ∷ ι1 ∷ []) (ι1 ∷ Sw01 ∷ []) (wl0118 c4)
  q39 : WsL → Eqn
  q39 c4 = eqn (Sw01 ∷ K4 ∷ []) (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑))
  q40 : WsL → Eqn
  q40 c4 = eqn (Sw12 ∷ K4 ∷ []) (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑))
  q41 : WsL → Eqn
  q41 c4 = eqn (Sw12 ∷ ι1 ∷ []) (ι1 ∷ Sw12 ∷ []) (wl0119 c4)
  q42 : WsL → Eqn
  q42 c4 = eqn (K3 ∷ Sw34 ∷ []) (Sw34 ∷ K4 ∷ []) (wl0066 c4)
  q43 : WsL → Eqn
  q43 c4 = eqn (K2 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ []) (wl0067 c4)
  q44 : WsL → Eqn
  q44 c4 = eqn (ι1 ∷ Sw23 ∷ []) (Sw23 ∷ ι1 ∷ []) (c₂ (iI ↑) (Swap))
  q45 : WsL → Eqn
  q45 c4 = eqn (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι1 ∷ []) (wl0120 c4)

-- comm push TOFF412 sw0 L: 62 steps
lem-comm-push-TOFF412-sw0-L : WsL → ⟪ (Toff412 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff402 ∷ []) ⟫ʷ
lem-comm-push-TOFF412-sw0-L c4 = derive (Toff412 ∷ Sw01 ∷ []) (Sw01 ∷ Toff402 ∷ [])
  (re 0 1 (Sw34 ∷ Toff312 ∷ Sw34 ∷ []) ∷
   re 1 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw⁻ 0 (q36 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   re 1 3 (CS24 ∷ []) ∷
   rw⁻ 2 (q27 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (CS24⁻ ∷ []) ∷
   rw⁻ 4 (q27 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (CS14 ∷ []) ∷
   rw⁻ 6 (q36 c4) ∷
   rw⁻ 7 (q37 c4) ∷
   rw 8 (q3 c4) ∷
   rw⁻ 7 (q38 c4) ∷
   rw⁻ 6 (q39 c4) ∷
   rw 5 (q28 c4) ∷
   rw 4 (q29 c4) ∷
   rw⁻ 3 (q30 c4) ∷
   rw 2 (q29 c4) ∷
   rw⁻ 1 (q31 c4) ∷
   rw⁻ 0 (q39 c4) ∷
   rw⁻ 1 (q32 c4) ∷
   rw 2 (q40 c4) ∷
   rw⁻ 3 (q33 c4) ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 (q32 c4) ∷
   rw⁻ 5 (q34 c4) ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 (q32 c4) ∷
   rw 7 (q35 c4) ∷
   rw 8 (q40 c4) ∷
   rw 9 (q41 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 3 (q42 c4) ∷
   re 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q3 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   re 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 8 (q3 c4) ∷
   rw⁻ 9 (q42 c4) ∷
   rw⁻ 10 (q37 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw⁻ 4 (q43 c4) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 (q1 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 (q1 c4) ∷
   rw⁻ 10 (q43 c4) ∷
   rw⁻ 11 (q44 c4) ∷
   rw⁻ 4 (q45 c4) ∷
   re 4 8 (Toff201 ∷ []) ∷
   re 3 3 (Toff301 ∷ []) ∷
   re 2 3 (Toff401 ∷ []) ∷
   re 1 3 (Toff402 ∷ []) ∷ []) Eq.refl

private
  q46 : WsL → Eqn
  q46 c4 = eqn (Bx4-203 ∷ Sw12 ∷ []) (Sw12 ∷ Bx4-103 ∷ []) (lem-comm-push-BOX⟨4·203⟩-sw1-L c4)
  q47 : WsL → Eqn
  q47 c4 = eqn (CCZ124 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ124 ∷ []) (wl0122 c4)
  q48 : WsL → Eqn
  q48 c4 = eqn (Sw12 ∷ Toff124 ∷ []) (Toff214 ∷ Sw12 ∷ []) (wl0123 c4)

-- comm push BOX(2;4103) sw1 L: 8 steps
lem-comm-push-BOX⟨2·4103⟩-sw1-L : WsL → ⟪ (Bx2-4103 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx1-4203 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·4103⟩-sw1-L c4 = derive (Bx2-4103 ∷ Sw12 ∷ []) (Sw12 ∷ Bx1-4203 ∷ [])
  (re 0 1 (CCZ124 ∷ Toff214 ∷ Bx4-203 ∷ Toff214 ∷ CCZ124 ∷ Bx4-203 ∷ []) ∷
   rw 5 (q46 c4) ∷
   rw 4 (q47 c4) ∷
   rw⁻ 3 (q48 c4) ∷
   rw 2 (q46 c4) ∷
   rw⁻ 1 (q48 c4) ∷
   rw 0 (q47 c4) ∷
   re 1 6 (Bx1-4203 ∷ []) ∷ []) Eq.refl

private
  q49 : WsL → Eqn
  q49 c4 = eqn (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ []) (wl0064 c4)
  q50 : WsL → Eqn
  q50 c4 = eqn (CS04 ∷ Sw01 ∷ []) (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L c4)
  q51 : WsL → Eqn
  q51 c4 = eqn (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) (wl0107 c4)
  q52 : WsL → Eqn
  q52 c4 = eqn (CS14⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS04⁻ ∷ []) (lem-comm-push-CSd14-sw0-L c4)
  q53 : WsL → Eqn
  q53 c4 = eqn (K2 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (wl0124 c4)

-- comm push TOFF401 sw0 L: 63 steps
lem-comm-push-TOFF401-sw0-L : WsL → ⟪ (Toff401 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff401 ∷ []) ⟫ʷ
lem-comm-push-TOFF401-sw0-L c4 = derive (Toff401 ∷ Sw01 ∷ []) (Sw01 ∷ Toff401 ∷ [])
  (re 0 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) ∷
   re 1 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 2 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw⁻ 1 (q49 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 (q49 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw 9 (q1 c4) ∷
   rw⁻ 0 (q36 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   re 1 3 (CS14 ∷ []) ∷
   rw⁻ 2 (q4 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (CS14⁻ ∷ []) ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw⁻ 6 (q36 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw 8 (q3 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   rw⁻ 6 (q39 c4) ∷
   rw 5 (q50 c4) ∷
   rw 4 (q51 c4) ∷
   rw 3 (q52 c4) ∷
   rw 2 (q51 c4) ∷
   rw 1 (q28 c4) ∷
   rw⁻ 0 (q39 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw⁻ 2 (q42 c4) ∷
   re 4 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 3 (q3 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   re 6 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   re 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 7 (q3 c4) ∷
   rw⁻ 8 (q42 c4) ∷
   rw⁻ 9 (q15 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q10 c4) ∷
   re 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 7 (q10 c4) ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 (q1 c4) ∷
   rw⁻ 9 (q43 c4) ∷
   rw⁻ 10 (q13 c4) ∷
   rw 3 (q53 c4) ∷
   re 3 8 (Toff201 ∷ []) ∷
   re 2 3 (Toff301 ∷ []) ∷
   re 1 3 (Toff401 ∷ []) ∷ []) Eq.refl

private
  q54 : WsL → Eqn
  q54 c4 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (c₁ (K) (Swap))
  q55 : WsL → Eqn
  q55 c4 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι1 ∷ []) (wl0125 c4)

-- comm push TOFF124 sw0 L: 62 steps
lem-comm-push-TOFF124-sw0-L : WsL → ⟪ (Toff124 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff024 ∷ []) ⟫ʷ
lem-comm-push-TOFF124-sw0-L c4 = derive (Toff124 ∷ Sw01 ∷ []) (Sw01 ∷ Toff024 ∷ [])
  (re 0 1 (Sw34 ∷ Toff123 ∷ Sw34 ∷ []) ∷
   re 1 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw⁻ 0 (q18 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   re 1 3 (CS24 ∷ []) ∷
   rw⁻ 2 (q27 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (CS24⁻ ∷ []) ∷
   rw⁻ 4 (q27 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (CS14 ∷ []) ∷
   rw⁻ 6 (q18 c4) ∷
   rw⁻ 7 (q37 c4) ∷
   rw 8 (q3 c4) ∷
   rw⁻ 7 (q38 c4) ∷
   rw 6 (q16 c4) ∷
   rw 5 (q28 c4) ∷
   rw 4 (q29 c4) ∷
   rw⁻ 3 (q30 c4) ∷
   rw 2 (q29 c4) ∷
   rw⁻ 1 (q31 c4) ∷
   rw 0 (q16 c4) ∷
   rw⁻ 1 (q32 c4) ∷
   rw⁻ 2 (q54 c4) ∷
   rw⁻ 3 (q33 c4) ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 (q32 c4) ∷
   rw⁻ 5 (q34 c4) ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 (q32 c4) ∷
   rw 7 (q35 c4) ∷
   rw⁻ 8 (q54 c4) ∷
   rw 9 (q41 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   re 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q3 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   re 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 8 (q3 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw⁻ 10 (q37 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw⁻ 4 (q12 c4) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 (q1 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 (q1 c4) ∷
   rw⁻ 10 (q12 c4) ∷
   rw⁻ 11 (q44 c4) ∷
   rw⁻ 4 (q55 c4) ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 3 3 (Toff013 ∷ []) ∷
   re 2 3 (Toff014 ∷ []) ∷
   re 1 3 (Toff024 ∷ []) ∷ []) Eq.refl

private
  q56 : WsL → Eqn
  q56 c4 = eqn (Bx0-42 ∷ Sw12 ∷ []) (Sw12 ∷ Bx0-41 ∷ []) (lem-comm-push-BOX⟨0·42⟩-sw1-L c4)

-- comm push BOX(4;012) sw1 L: 12 steps
lem-comm-push-BOX⟨4·012⟩-sw1-L : WsL → ⟪ (Bx4-012 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx4-021 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·012⟩-sw1-L c4 = derive (Bx4-012 ∷ Sw12 ∷ []) (Sw12 ∷ Bx4-021 ∷ [])
  (re 0 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) ∷
   rw 5 (q56 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   re 5 3 (CCZ024 ∷ []) ∷
   rw⁻ 3 (q32 c4) ∷
   re 4 3 (Toff402 ∷ []) ∷
   rw 2 (q56 c4) ∷
   rw⁻ 1 (q32 c4) ∷
   re 2 3 (Toff402 ∷ []) ∷
   rw⁻ 0 (q32 c4) ∷
   re 1 3 (CCZ024 ∷ []) ∷
   re 1 6 (Bx4-021 ∷ []) ∷ []) Eq.refl

private
  q57 : WsL → Eqn
  q57 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl0005 c4)
  q58 : WsL → Eqn
  q58 c4 = eqn (CS24⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS14⁻ ∷ []) (wl0007 c4)
  q59 : WsL → Eqn
  q59 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl0008 c4)
  q60 : WsL → Eqn
  q60 c4 = eqn (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) (wl0009 c4)
  q61 : WsL → Eqn
  q61 c4 = eqn (Sw23 ∷ CS04 ∷ []) (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4)
  q62 : WsL → Eqn
  q62 c4 = eqn (CS34⁻ ∷ Sw34 ∷ []) (Sw34 ∷ CS34⁻ ∷ []) (wl0128 c4)
  q63 : WsL → Eqn
  q63 c4 = eqn (CS34 ∷ Sw34 ∷ []) (Sw34 ∷ CS34 ∷ []) (wl0129 c4)
  q64 : WsL → Eqn
  q64 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl0011 c4)
  q65 : WsL → Eqn
  q65 c4 = eqn (Sw23 ∷ CX04 ∷ []) (CX04 ∷ Sw23 ∷ []) (lem-comm-push-CX04-sw2-R c4)
  q66 : WsL → Eqn
  q66 c4 = eqn (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) (wl0012 c4)
  q67 : WsL → Eqn
  q67 c4 = eqn (Sw12 ∷ CX04 ∷ []) (CX04 ∷ Sw12 ∷ []) (lem-comm-push-CX04-sw1-R c4)
  q68 : WsL → Eqn
  q68 c4 = eqn (CS01 ∷ Sw34 ∷ []) (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑))
  q69 : WsL → Eqn
  q69 c4 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (c₂ (CS) (Swap))
  q70 : WsL → Eqn
  q70 c4 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0130 c4)

-- comm push CCZ034 sw3 L: 87 steps
lem-comm-push-CCZ034-sw3-L : WsL → ⟪ (CCZ034 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ CCZ034 ∷ []) ⟫ʷ
lem-comm-push-CCZ034-sw3-L c4 = derive (CCZ034 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ034 ∷ [])
  (re 0 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) ∷
   re 1 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 (q2 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 (q1 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 2 3 (CS14 ∷ []) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (CS14⁻ ∷ []) ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw 7 (q3 c4) ∷
   rw⁻ 1 (q57 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   re 2 3 (CX02 ∷ []) ∷
   rw⁻ 3 (q58 c4) ∷
   rw⁻ 6 (q32 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 (q35 c4) ∷
   rw 6 (q32 c4) ∷
   rw⁻ 0 (q59 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   re 1 3 (CX03 ∷ []) ∷
   rw⁻ 2 (q60 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CX03 ∷ []) ∷
   rw 4 (q61 c4) ∷
   rw 5 (q1 c4) ∷
   re 4 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q3 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   re 4 3 (CX04 ∷ []) ∷
   rw 2 (q62 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   re 2 3 (CX04 ∷ []) ∷
   rw 0 (q63 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q64 c4) ∷
   rw 3 (q65 c4) ∷
   rw⁻ 4 (q66 c4) ∷
   rw 5 (q65 c4) ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw⁻ 3 (q33 c4) ∷
   rw 4 (q67 c4) ∷
   rw⁻ 5 (q34 c4) ∷
   rw 6 (q67 c4) ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 7 (q32 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   re 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 4 (q3 c4) ∷
   re 6 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   re 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q3 c4) ∷
   re 8 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 7 (q3 c4) ∷
   rw⁻ 8 (q68 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 (q1 c4) ∷
   re 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 (q1 c4) ∷
   re 9 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 8 (q1 c4) ∷
   rw⁻ 9 (q69 c4) ∷
   rw⁻ 5 (q70 c4) ∷
   re 5 5 (CCZ012 ∷ []) ∷
   re 4 3 (CCZ013 ∷ []) ∷
   re 3 3 (CCZ014 ∷ []) ∷
   re 2 3 (CCZ024 ∷ []) ∷
   re 1 3 (CCZ034 ∷ []) ∷ []) Eq.refl

private
  q71 : WsL → Eqn
  q71 c4 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap))
  q72 : WsL → Eqn
  q72 c4 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ []) (wl0131 c4)

-- comm push TOFF034 sw3 L: 114 steps
lem-comm-push-TOFF034-sw3-L : WsL → ⟪ (Toff034 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Toff034 ∷ []) ⟫ʷ
lem-comm-push-TOFF034-sw3-L c4 = derive (Toff034 ∷ Sw34 ∷ []) (Sw34 ∷ Toff034 ∷ [])
  (re 0 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) ∷
   re 1 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 (q12 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q2 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 (q12 c4) ∷
   rw⁻ 10 (q13 c4) ∷
   rw 11 (q1 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q14 c4) ∷
   rw⁻ 9 (q15 c4) ∷
   rw 10 (q3 c4) ∷
   rw⁻ 1 (q54 c4) ∷
   rw⁻ 2 (q57 c4) ∷
   rw⁻ 5 (q32 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q58 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 (q35 c4) ∷
   rw⁻ 7 (q54 c4) ∷
   rw⁻ 8 (q71 c4) ∷
   rw 9 (q32 c4) ∷
   rw⁻ 0 (q12 c4) ∷
   rw⁻ 1 (q59 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (CX03 ∷ []) ∷
   rw⁻ 3 (q60 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CX03 ∷ []) ∷
   rw 5 (q61 c4) ∷
   rw⁻ 6 (q12 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw 8 (q1 c4) ∷
   rw 7 (q15 c4) ∷
   rw 6 (q14 c4) ∷
   re 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q3 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 5 3 (CX04 ∷ []) ∷
   rw 3 (q62 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   re 3 3 (CX04 ∷ []) ∷
   rw 1 (q63 c4) ∷
   rw 0 (q14 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q12 c4) ∷
   rw⁻ 3 (q64 c4) ∷
   rw 4 (q65 c4) ∷
   rw⁻ 5 (q66 c4) ∷
   rw 6 (q65 c4) ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 (q1 c4) ∷
   rw⁻ 8 (q12 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw⁻ 3 (q54 c4) ∷
   rw⁻ 4 (q33 c4) ∷
   rw 5 (q67 c4) ∷
   rw⁻ 6 (q34 c4) ∷
   rw 7 (q67 c4) ∷
   re 9 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 8 (q32 c4) ∷
   rw⁻ 9 (q54 c4) ∷
   rw⁻ 10 (q71 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   re 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   re 7 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 6 (q3 c4) ∷
   re 8 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 7 (q3 c4) ∷
   re 9 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 8 (q3 c4) ∷
   rw⁻ 9 (q68 c4) ∷
   rw⁻ 10 (q14 c4) ∷
   rw⁻ 11 (q15 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 5 (q12 c4) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 8 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 7 (q1 c4) ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 (q1 c4) ∷
   re 10 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 9 (q1 c4) ∷
   rw⁻ 10 (q69 c4) ∷
   rw⁻ 11 (q12 c4) ∷
   rw⁻ 12 (q13 c4) ∷
   rw⁻ 5 (q72 c4) ∷
   re 5 8 (Toff012 ∷ []) ∷
   re 4 3 (Toff013 ∷ []) ∷
   re 3 3 (Toff014 ∷ []) ∷
   re 2 3 (Toff024 ∷ []) ∷
   re 1 3 (Toff034 ∷ []) ∷ []) Eq.refl

private
  q73 : WsL → Eqn
  q73 c4 = eqn (Bx0-31 ∷ Sw23 ∷ []) (Sw23 ∷ Bx0-21 ∷ []) (lem-comm-push-BOX⟨0·31⟩-sw2-L c4)
  q74 : WsL → Eqn
  q74 c4 = eqn (CCZ023 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ023 ∷ []) (wl0132 c4)
  q75 : WsL → Eqn
  q75 c4 = eqn (Sw23 ∷ Toff203 ∷ []) (Toff302 ∷ Sw23 ∷ []) (wl0133 c4)

-- comm push BOX(3;021) sw2 L: 8 steps
lem-comm-push-BOX⟨3·021⟩-sw2-L : WsL → ⟪ (Bx3-021 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Bx2-031 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨3·021⟩-sw2-L c4 = derive (Bx3-021 ∷ Sw23 ∷ []) (Sw23 ∷ Bx2-031 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) ∷
   rw 5 (q73 c4) ∷
   rw 4 (q74 c4) ∷
   rw⁻ 3 (q75 c4) ∷
   rw 2 (q73 c4) ∷
   rw⁻ 1 (q75 c4) ∷
   rw 0 (q74 c4) ∷
   re 1 6 (Bx2-031 ∷ []) ∷ []) Eq.refl

private
  q76 : WsL → Eqn
  q76 c4 = eqn (Sw23 ∷ Bx0-21 ∷ []) (Bx0-31 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨0·21⟩-sw2-R c4)

-- comm push BOX(2;031) sw2 R: 8 steps
lem-comm-push-BOX⟨2·031⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx2-031 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-021 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·031⟩-sw2-R c4 = derive (Sw23 ∷ Bx2-031 ∷ []) (Bx3-021 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) ∷
   rw⁻ 0 (q74 c4) ∷
   rw 1 (q75 c4) ∷
   rw 2 (q76 c4) ∷
   rw 3 (q75 c4) ∷
   rw⁻ 4 (q74 c4) ∷
   rw 5 (q76 c4) ∷
   re 0 6 (Bx3-021 ∷ []) ∷ []) Eq.refl

-- comm push CCZ034 sw3 R: 87 steps
lem-comm-push-CCZ034-sw3-R : WsL → ⟪ (Sw34 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-CCZ034-sw3-R c4 = derive (Sw34 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw34 ∷ [])
  (re 1 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   re 3 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q2 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 (q1 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw 8 (q3 c4) ∷
   rw⁻ 2 (q57 c4) ∷
   rw⁻ 5 (q32 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q58 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 (q35 c4) ∷
   rw 7 (q32 c4) ∷
   rw⁻ 1 (q59 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (CX03 ∷ []) ∷
   rw⁻ 3 (q60 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CX03 ∷ []) ∷
   rw 5 (q61 c4) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 0 (q63 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   re 1 3 (CX04 ∷ []) ∷
   rw⁻ 2 (q62 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (CX04 ∷ []) ∷
   re 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q64 c4) ∷
   rw 2 (q65 c4) ∷
   rw⁻ 3 (q66 c4) ∷
   rw 4 (q65 c4) ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 1 (q32 c4) ∷
   rw⁻ 2 (q33 c4) ∷
   rw 3 (q67 c4) ∷
   rw⁻ 4 (q34 c4) ∷
   rw 5 (q67 c4) ∷
   re 7 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 6 (q32 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   re 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 3 (q3 c4) ∷
   re 5 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 4 (q3 c4) ∷
   re 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   re 7 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 6 (q3 c4) ∷
   rw⁻ 7 (q68 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 (q1 c4) ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 5 (q1 c4) ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 8 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 7 (q1 c4) ∷
   rw⁻ 8 (q69 c4) ∷
   rw⁻ 4 (q70 c4) ∷
   re 4 5 (CCZ012 ∷ []) ∷
   re 3 3 (CCZ013 ∷ []) ∷
   re 2 3 (CCZ014 ∷ []) ∷
   re 1 3 (CCZ024 ∷ []) ∷
   re 0 3 (CCZ034 ∷ []) ∷ []) Eq.refl

-- comm push TOFF034 sw3 R: 114 steps
lem-comm-push-TOFF034-sw3-R : WsL → ⟪ (Sw34 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-TOFF034-sw3-R c4 = derive (Sw34 ∷ Toff034 ∷ []) (Toff034 ∷ Sw34 ∷ [])
  (re 1 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) ∷
   re 3 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   re 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 4 (q12 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 (q2 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 (q12 c4) ∷
   rw⁻ 11 (q13 c4) ∷
   rw 12 (q1 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (CS14 ∷ []) ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (CS14⁻ ∷ []) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 10 (q3 c4) ∷
   re 8 3 (CS04 ∷ []) ∷
   rw⁻ 9 (q14 c4) ∷
   rw⁻ 10 (q15 c4) ∷
   rw 11 (q3 c4) ∷
   rw⁻ 2 (q54 c4) ∷
   rw⁻ 3 (q57 c4) ∷
   rw⁻ 6 (q32 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw⁻ 5 (q58 c4) ∷
   rw⁻ 8 (q32 c4) ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 7 (q35 c4) ∷
   rw⁻ 8 (q54 c4) ∷
   rw⁻ 9 (q71 c4) ∷
   rw 10 (q32 c4) ∷
   rw⁻ 1 (q12 c4) ∷
   rw⁻ 2 (q59 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CX03 ∷ []) ∷
   rw⁻ 4 (q60 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CX03 ∷ []) ∷
   rw 6 (q61 c4) ∷
   rw⁻ 7 (q12 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw 9 (q1 c4) ∷
   rw⁻ 0 (q14 c4) ∷
   rw⁻ 1 (q63 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 2 3 (CX04 ∷ []) ∷
   rw⁻ 3 (q62 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (CX04 ∷ []) ∷
   re 6 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q12 c4) ∷
   rw⁻ 2 (q64 c4) ∷
   rw 3 (q65 c4) ∷
   rw⁻ 4 (q66 c4) ∷
   rw 5 (q65 c4) ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 7 (q12 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw⁻ 1 (q32 c4) ∷
   rw⁻ 2 (q54 c4) ∷
   rw⁻ 3 (q33 c4) ∷
   rw 4 (q67 c4) ∷
   rw⁻ 5 (q34 c4) ∷
   rw 6 (q67 c4) ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 7 (q32 c4) ∷
   rw⁻ 8 (q54 c4) ∷
   rw⁻ 9 (q71 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   re 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 4 (q3 c4) ∷
   re 6 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   re 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q3 c4) ∷
   re 8 1 (Sw34 ∷ CX03 ∷ Sw34 ∷ []) ∷
   rw 7 (q3 c4) ∷
   rw⁻ 8 (q68 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw⁻ 10 (q15 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw⁻ 4 (q12 c4) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 (q1 c4) ∷
   re 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 (q1 c4) ∷
   re 9 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 8 (q1 c4) ∷
   rw⁻ 9 (q69 c4) ∷
   rw⁻ 10 (q12 c4) ∷
   rw⁻ 11 (q13 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 3 3 (Toff013 ∷ []) ∷
   re 2 3 (Toff014 ∷ []) ∷
   re 1 3 (Toff024 ∷ []) ∷
   re 0 3 (Toff034 ∷ []) ∷ []) Eq.refl

private
  q77 : WsL → Eqn
  q77 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl0047 c4)
  q78 : WsL → Eqn
  q78 c4 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wl0029 c4)
  q79 : WsL → Eqn
  q79 c4 = eqn (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) (wl0001 c4)
  q80 : WsL → Eqn
  q80 c4 = eqn (CX02 ∷ Sw34 ∷ []) (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))

-- comm push CCZ023 sw3 R: 58 steps
lem-comm-push-CCZ023-sw3-R : WsL → ⟪ (Sw34 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-CCZ023-sw3-R c4 = derive (Sw34 ∷ CCZ023 ∷ []) (CCZ024 ∷ Sw34 ∷ [])
  (re 1 1 (Sw12 ∷ CCZ013 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 (q1 c4) ∷
   rw⁻ 1 (q77 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   re 2 3 (CX02 ∷ []) ∷
   rw⁻ 3 (q78 c4) ∷
   rw⁻ 6 (q32 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw⁻ 5 (q79 c4) ∷
   rw 6 (q32 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   re 0 3 (CS24 ∷ []) ∷
   rw⁻ 1 (q80 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 2 3 (CS24⁻ ∷ []) ∷
   rw⁻ 3 (q80 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (CS04 ∷ []) ∷
   rw⁻ 0 (q32 c4) ∷
   rw⁻ 1 (q33 c4) ∷
   re 3 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 2 (q32 c4) ∷
   rw⁻ 3 (q34 c4) ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 (q32 c4) ∷
   rw 5 (q35 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   re 3 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 2 (q3 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   re 5 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q3 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 (q1 c4) ∷
   re 3 5 (CCZ012 ∷ []) ∷
   re 2 3 (CCZ013 ∷ []) ∷
   re 1 3 (CCZ014 ∷ []) ∷
   re 0 3 (CCZ024 ∷ []) ∷ []) Eq.refl

private
  q81 : WsL → Eqn
  q81 c4 = eqn (Sw12 ∷ K3 ∷ []) (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K))

-- comm push TOFF302 sw3 R: 76 steps
lem-comm-push-TOFF302-sw3-R : WsL → ⟪ (Sw34 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Sw34 ∷ []) ⟫ʷ
lem-comm-push-TOFF302-sw3-R c4 = derive (Sw34 ∷ Toff302 ∷ []) (Toff402 ∷ Sw34 ∷ [])
  (re 1 1 (Sw12 ∷ Toff301 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw⁻ 2 (q49 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 (q2 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 (q49 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw 10 (q1 c4) ∷
   rw 1 (q81 c4) ∷
   rw⁻ 2 (q77 c4) ∷
   rw⁻ 5 (q32 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q78 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   rw⁻ 6 (q79 c4) ∷
   rw 7 (q81 c4) ∷
   rw⁻ 8 (q71 c4) ∷
   rw 9 (q32 c4) ∷
   rw⁻ 0 (q36 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   re 1 3 (CS24 ∷ []) ∷
   rw⁻ 2 (q80 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (CS24⁻ ∷ []) ∷
   rw⁻ 4 (q80 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw⁻ 6 (q36 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw⁻ 0 (q32 c4) ∷
   rw 1 (q40 c4) ∷
   rw⁻ 2 (q33 c4) ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 3 (q32 c4) ∷
   rw⁻ 4 (q34 c4) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 (q32 c4) ∷
   rw 6 (q35 c4) ∷
   rw 7 (q40 c4) ∷
   rw⁻ 8 (q71 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw⁻ 2 (q42 c4) ∷
   re 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 3 (q3 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   re 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q3 c4) ∷
   rw⁻ 8 (q42 c4) ∷
   rw⁻ 9 (q15 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 (q1 c4) ∷
   rw⁻ 9 (q43 c4) ∷
   rw⁻ 10 (q13 c4) ∷
   re 3 8 (Toff201 ∷ []) ∷
   re 2 3 (Toff301 ∷ []) ∷
   re 1 3 (Toff401 ∷ []) ∷
   re 0 3 (Toff402 ∷ []) ∷ []) Eq.refl

private
  q82 : WsL → Eqn
  q82 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q83 : WsL → Eqn
  q83 c4 = eqn (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) (wl0010 c4)
  q84 : WsL → Eqn
  q84 c4 = eqn (Sw12 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS))

-- comm push CCZ034 sw1 R: 83 steps
lem-comm-push-CCZ034-sw1-R : WsL → ⟪ (Sw12 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-CCZ034-sw1-R c4 = derive (Sw12 ∷ CCZ034 ∷ []) (CCZ034 ∷ Sw12 ∷ [])
  (re 1 1 (Sw23 ∷ CCZ024 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   re 3 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q2 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 (q1 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw 8 (q3 c4) ∷
   rw⁻ 2 (q57 c4) ∷
   rw⁻ 5 (q32 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q58 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 (q35 c4) ∷
   rw 7 (q32 c4) ∷
   rw⁻ 1 (q59 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (CX03 ∷ []) ∷
   rw⁻ 3 (q60 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CX03 ∷ []) ∷
   rw 5 (q61 c4) ∷
   rw 6 (q1 c4) ∷
   rw 0 (q82 c4) ∷
   rw⁻ 1 (q83 c4) ∷
   rw 2 (q84 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   rw 4 (q35 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q64 c4) ∷
   re 3 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 2 (q1 c4) ∷
   rw⁻ 3 (q66 c4) ∷
   re 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q61 c4) ∷
   rw⁻ 1 (q32 c4) ∷
   rw⁻ 2 (q33 c4) ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 3 (q32 c4) ∷
   rw⁻ 4 (q34 c4) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 (q32 c4) ∷
   rw 6 (q35 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   re 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 3 (q3 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   re 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q3 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 (q1 c4) ∷
   re 4 5 (CCZ012 ∷ []) ∷
   re 3 3 (CCZ013 ∷ []) ∷
   re 2 3 (CCZ014 ∷ []) ∷
   re 1 3 (CCZ024 ∷ []) ∷
   re 0 3 (CCZ034 ∷ []) ∷ []) Eq.refl

-- comm push TOFF034 sw1 R: 110 steps
lem-comm-push-TOFF034-sw1-R : WsL → ⟪ (Sw12 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-TOFF034-sw1-R c4 = derive (Sw12 ∷ Toff034 ∷ []) (Toff034 ∷ Sw12 ∷ [])
  (re 1 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) ∷
   re 2 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) ∷
   re 3 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   re 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 4 (q12 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 (q2 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 (q12 c4) ∷
   rw⁻ 11 (q13 c4) ∷
   rw 12 (q1 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (CS14 ∷ []) ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (CS14⁻ ∷ []) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 10 (q3 c4) ∷
   re 8 3 (CS04 ∷ []) ∷
   rw⁻ 9 (q14 c4) ∷
   rw⁻ 10 (q15 c4) ∷
   rw 11 (q3 c4) ∷
   rw⁻ 2 (q54 c4) ∷
   rw⁻ 3 (q57 c4) ∷
   rw⁻ 6 (q32 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw⁻ 5 (q58 c4) ∷
   rw⁻ 8 (q32 c4) ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 7 (q35 c4) ∷
   rw⁻ 8 (q54 c4) ∷
   rw⁻ 9 (q71 c4) ∷
   rw 10 (q32 c4) ∷
   rw⁻ 1 (q12 c4) ∷
   rw⁻ 2 (q59 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CX03 ∷ []) ∷
   rw⁻ 4 (q60 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CX03 ∷ []) ∷
   rw 6 (q61 c4) ∷
   rw⁻ 7 (q12 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw 9 (q1 c4) ∷
   rw⁻ 0 (q54 c4) ∷
   rw 1 (q82 c4) ∷
   rw⁻ 2 (q83 c4) ∷
   rw 3 (q84 c4) ∷
   rw⁻ 4 (q83 c4) ∷
   rw 5 (q35 c4) ∷
   rw⁻ 6 (q54 c4) ∷
   rw⁻ 7 (q71 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q12 c4) ∷
   rw⁻ 2 (q64 c4) ∷
   re 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 4 (q66 c4) ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q61 c4) ∷
   rw⁻ 7 (q12 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw⁻ 1 (q32 c4) ∷
   rw⁻ 2 (q54 c4) ∷
   rw⁻ 3 (q33 c4) ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 (q32 c4) ∷
   rw⁻ 5 (q34 c4) ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 (q32 c4) ∷
   rw 7 (q35 c4) ∷
   rw⁻ 8 (q54 c4) ∷
   rw⁻ 9 (q71 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   re 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q3 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   re 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 8 (q3 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw⁻ 10 (q15 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw⁻ 4 (q12 c4) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 (q1 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 (q1 c4) ∷
   rw⁻ 10 (q12 c4) ∷
   rw⁻ 11 (q13 c4) ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 3 3 (Toff013 ∷ []) ∷
   re 2 3 (Toff014 ∷ []) ∷
   re 1 3 (Toff024 ∷ []) ∷
   re 0 3 (Toff034 ∷ []) ∷ []) Eq.refl

private
  q85 : WsL → Eqn
  q85 c4 = eqn (Sw12 ∷ Bx0-41 ∷ []) (Bx0-42 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨0·41⟩-sw1-R c4)

-- comm push BOX(4;021) sw1 R: 12 steps
lem-comm-push-BOX⟨4·021⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx4-021 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-012 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨4·021⟩-sw1-R c4 = derive (Sw12 ∷ Bx4-021 ∷ []) (Bx4-012 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) ∷
   re 1 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   rw 0 (q32 c4) ∷
   re 2 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) ∷
   rw 1 (q32 c4) ∷
   rw 2 (q85 c4) ∷
   re 4 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) ∷
   rw 3 (q32 c4) ∷
   re 5 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   rw 4 (q32 c4) ∷
   rw 5 (q85 c4) ∷
   re 0 6 (Bx4-012 ∷ []) ∷ []) Eq.refl
