{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.R006 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (WsL ; wl ; wp)
open import Examples.Groups.Clifford+CS.FiveV.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.FiveV.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-push-CK40-sw0-L ; lem-comm-push-CKd40-sw0-L ; lem-comm-push-CS04-sw0-L ; lem-comm-push-CS04-sw1-L ; lem-comm-push-CS04-sw1-R ; lem-comm-push-CS04-sw2-L ; lem-comm-push-CS04-sw2-R ; lem-comm-push-CX04-sw0-L ; lem-comm-push-CX04-sw1-L ; lem-comm-push-CX40-sw0-L ; lem-comm-push-CX40-sw1-L ; lem-comm-push-CX40-sw2-L ; lem-comm-push-CZ04-sw0-L ; lem-comm-push-CZ04-sw1-L ; lem-comm-push-CZ04-sw2-L)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-push-CK40-sw1-L ; lem-comm-push-CK40-sw2-L ; lem-comm-push-SWAP04-sw2-L)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-push-BOX⟨0·12⟩-sw1-L ; lem-comm-push-BOX⟨0·12⟩-sw2-R ; lem-comm-push-BOX⟨0·13⟩-sw2-L ; lem-comm-push-BOX⟨0·21⟩-sw1-R ; lem-comm-push-BOX⟨1·03⟩-sw0-L ; lem-comm-push-BOX⟨2·03⟩-sw1-L ; lem-comm-push-CS14-sw0-L ; lem-comm-push-CSd14-sw0-L ; lem-comm-push-CX04-sw2-L ; lem-comm-push-SWAP04-sw0-L)

private
  q1 : WsL → Eqn
  q1 c4 = eqn (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ []) (wl 64 c4)
  q2 : WsL → Eqn
  q2 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl 3 c4)
  q3 : WsL → Eqn
  q3 c4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap))
  q4 : WsL → Eqn
  q4 c4 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (c₁ (iI) (Swap ↑))
  q5 : WsL → Eqn
  q5 c4 = eqn (K4 ∷ Sw34 ∷ []) (Sw34 ∷ K3 ∷ []) (wl 65 c4)
  q6 : WsL → Eqn
  q6 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl 4 c4)
  q7 : WsL → Eqn
  q7 c4 = eqn (CX01 ∷ Sw34 ∷ []) (Sw34 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap ↑))
  q8 : WsL → Eqn
  q8 c4 = eqn (ι ∷ Sw34 ∷ []) (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑))
  q9 : WsL → Eqn
  q9 c4 = eqn (Sw12 ∷ K4 ∷ []) (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑))
  q10 : WsL → Eqn
  q10 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl 5 c4)
  q11 : WsL → Eqn
  q11 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl 6 c4)
  q12 : WsL → Eqn
  q12 c4 = eqn (CS24⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS14⁻ ∷ []) (wl 7 c4)
  q13 : WsL → Eqn
  q13 c4 = eqn (Sw12 ∷ CS04 ∷ []) (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4)
  q14 : WsL → Eqn
  q14 c4 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap))
  q15 : WsL → Eqn
  q15 c4 = eqn (Sw23 ∷ K4 ∷ []) (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K))
  q16 : WsL → Eqn
  q16 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl 8 c4)
  q17 : WsL → Eqn
  q17 c4 = eqn (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) (wl 9 c4)
  q18 : WsL → Eqn
  q18 c4 = eqn (Sw23 ∷ CS04 ∷ []) (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4)
  q19 : WsL → Eqn
  q19 c4 = eqn (CS04 ∷ Sw12 ∷ []) (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L c4)
  q20 : WsL → Eqn
  q20 c4 = eqn (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) (wl 10 c4)
  q21 : WsL → Eqn
  q21 c4 = eqn (Sw12 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS))
  q22 : WsL → Eqn
  q22 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q23 : WsL → Eqn
  q23 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl 11 c4)
  q24 : WsL → Eqn
  q24 c4 = eqn (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) (wl 12 c4)
  q25 : WsL → Eqn
  q25 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl 13 c4)
  q26 : WsL → Eqn
  q26 c4 = eqn (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ []) (wl 14 c4)
  q27 : WsL → Eqn
  q27 c4 = eqn (K3 ∷ Sw34 ∷ []) (Sw34 ∷ K4 ∷ []) (wl 66 c4)
  q28 : WsL → Eqn
  q28 c4 = eqn (K2 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ []) (wl 67 c4)

-- comm push TOFF403 sw1 L: 110 steps
lem-comm-push-TOFF403-sw1-L : WsL → ⟪ (Toff403 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Toff403 ∷ []) ⟫ʷ
lem-comm-push-TOFF403-sw1-L c4 = derive (Toff403 ∷ Sw12 ∷ []) (Sw12 ∷ Toff403 ∷ [])
  (re 0 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) ∷
   re 1 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) ∷
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
   rw 1 (q9 c4) ∷
   rw⁻ 2 (q10 c4) ∷
   rw⁻ 5 (q11 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q12 c4) ∷
   rw⁻ 7 (q11 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 (q13 c4) ∷
   rw 7 (q9 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw 9 (q11 c4) ∷
   rw 0 (q15 c4) ∷
   rw⁻ 1 (q16 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   re 2 3 (CX03 ∷ []) ∷
   rw⁻ 3 (q17 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (CX03 ∷ []) ∷
   rw 5 (q18 c4) ∷
   rw 6 (q15 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw 8 (q2 c4) ∷
   rw 7 (q14 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   rw 5 (q19 c4) ∷
   rw 4 (q20 c4) ∷
   rw⁻ 3 (q21 c4) ∷
   rw 2 (q20 c4) ∷
   rw⁻ 1 (q22 c4) ∷
   rw⁻ 0 (q9 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   rw 2 (q15 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   re 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 4 (q2 c4) ∷
   rw⁻ 5 (q24 c4) ∷
   re 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 6 (q2 c4) ∷
   rw 7 (q18 c4) ∷
   rw 8 (q15 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw 3 (q9 c4) ∷
   rw⁻ 4 (q25 c4) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 (q11 c4) ∷
   rw⁻ 6 (q26 c4) ∷
   re 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 7 (q11 c4) ∷
   rw 8 (q13 c4) ∷
   rw 9 (q9 c4) ∷
   rw⁻ 10 (q14 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw⁻ 4 (q27 c4) ∷
   re 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   re 8 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 7 (q6 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   re 10 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 9 (q6 c4) ∷
   rw⁻ 10 (q27 c4) ∷
   rw⁻ 11 (q8 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw⁻ 5 (q28 c4) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 (q2 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 (q2 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 (q2 c4) ∷
   rw⁻ 11 (q28 c4) ∷
   rw⁻ 12 (q4 c4) ∷
   re 5 8 (Toff201 ∷ []) ∷
   re 4 3 (Toff301 ∷ []) ∷
   re 3 3 (Toff401 ∷ []) ∷
   re 2 3 (Toff402 ∷ []) ∷
   re 1 3 (Toff403 ∷ []) ∷ []) Eq.refl

private
  q29 : WsL → Eqn
  q29 c4 = eqn (Sw01 ∷ ι ∷ []) (ι ∷ Sw01 ∷ []) (wl 25 c4)
  q30 : WsL → Eqn
  q30 c4 = eqn (Sw01 ∷ K4 ∷ []) (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑))
  q31 : WsL → Eqn
  q31 c4 = eqn (CS04 ∷ Sw01 ∷ []) (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L c4)
  q32 : WsL → Eqn
  q32 c4 = eqn (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) (wl 16 c4)
  q33 : WsL → Eqn
  q33 c4 = eqn (Sw01 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑))
  q34 : WsL → Eqn
  q34 c4 = eqn (Sw01 ∷ CS34 ∷ []) (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))
  q35 : WsL → Eqn
  q35 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl 17 c4)
  q36 : WsL → Eqn
  q36 c4 = eqn (CX12 ∷ Sw34 ∷ []) (Sw34 ∷ CX12 ∷ []) (c₃ (CX₀₁ ↑) (Swap))
  q37 : WsL → Eqn
  q37 c4 = eqn (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (wl 68 c4)

-- comm push TOFF403 sw0 L: 86 steps
lem-comm-push-TOFF403-sw0-L : WsL → ⟪ (Toff403 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff413 ∷ []) ⟫ʷ
lem-comm-push-TOFF403-sw0-L c4 = derive (Toff403 ∷ Sw01 ∷ []) (Sw01 ∷ Toff413 ∷ [])
  (re 0 1 (Sw23 ∷ Toff402 ∷ Sw23 ∷ []) ∷
   re 1 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) ∷
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
   rw 1 (q9 c4) ∷
   rw⁻ 2 (q10 c4) ∷
   rw⁻ 5 (q11 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q12 c4) ∷
   rw⁻ 7 (q11 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 (q13 c4) ∷
   rw 7 (q9 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw 9 (q11 c4) ∷
   rw 0 (q15 c4) ∷
   rw⁻ 1 (q16 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   re 2 3 (CX03 ∷ []) ∷
   rw⁻ 3 (q17 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (CX03 ∷ []) ∷
   rw 5 (q18 c4) ∷
   rw 6 (q15 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw 8 (q2 c4) ∷
   rw⁻ 7 (q29 c4) ∷
   rw⁻ 6 (q30 c4) ∷
   rw 5 (q31 c4) ∷
   rw 4 (q32 c4) ∷
   rw⁻ 3 (q33 c4) ∷
   rw 2 (q32 c4) ∷
   rw⁻ 1 (q34 c4) ∷
   rw⁻ 0 (q30 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   rw 2 (q15 c4) ∷
   rw⁻ 3 (q23 c4) ∷
   re 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 4 (q2 c4) ∷
   rw⁻ 5 (q24 c4) ∷
   re 7 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 6 (q2 c4) ∷
   rw⁻ 7 (q35 c4) ∷
   rw 8 (q15 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw⁻ 3 (q27 c4) ∷
   re 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q36 c4) ∷
   re 7 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q36 c4) ∷
   re 9 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 8 (q6 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw⁻ 10 (q8 c4) ∷
   rw 3 (q37 c4) ∷
   re 3 8 (Toff312 ∷ []) ∷
   re 2 3 (Toff412 ∷ []) ∷
   re 1 3 (Toff413 ∷ []) ∷ []) Eq.refl

private
  q38 : WsL → Eqn
  q38 c4 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (c₁ (K) (Swap ↑))
  q39 : WsL → Eqn
  q39 c4 = eqn (K0 ∷ Sw34 ∷ []) (Sw34 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑))
  q40 : WsL → Eqn
  q40 c4 = eqn (CS04 ∷ Sw23 ∷ []) (Sw23 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw2-L c4)
  q41 : WsL → Eqn
  q41 c4 = eqn (CS14⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS14⁻ ∷ []) (wl 48 c4)

-- comm push TOFF014 sw2 L: 62 steps
lem-comm-push-TOFF014-sw2-L : WsL → ⟪ (Toff014 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Toff014 ∷ []) ⟫ʷ
lem-comm-push-TOFF014-sw2-L c4 = derive (Toff014 ∷ Sw23 ∷ []) (Sw23 ∷ Toff014 ∷ [])
  (re 0 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 (q38 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 (q3 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 (q38 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw 9 (q2 c4) ∷
   rw⁻ 0 (q39 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   re 1 3 (CS14 ∷ []) ∷
   rw⁻ 2 (q7 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (CS14⁻ ∷ []) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw⁻ 6 (q39 c4) ∷
   rw⁻ 7 (q8 c4) ∷
   rw 8 (q6 c4) ∷
   rw 7 (q4 c4) ∷
   rw 6 (q38 c4) ∷
   rw 5 (q40 c4) ∷
   rw 4 (q3 c4) ∷
   rw 3 (q41 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q35 c4) ∷
   rw 0 (q38 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw⁻ 2 (q39 c4) ∷
   re 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   re 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q6 c4) ∷
   rw⁻ 8 (q39 c4) ∷
   rw⁻ 9 (q8 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 (q2 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q2 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 (q2 c4) ∷
   rw⁻ 9 (q38 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 2 3 (Toff013 ∷ []) ∷
   re 1 3 (Toff014 ∷ []) ∷ []) Eq.refl

private
  q42 : WsL → Eqn
  q42 c4 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (c₂ (K ↑) (Swap))
  q43 : WsL → Eqn
  q43 c4 = eqn (K1 ∷ Sw34 ∷ []) (Sw34 ∷ K1 ∷ []) (c₂ (K ↑) (Swap ↑))

-- comm push TOFF104 sw2 L: 62 steps
lem-comm-push-TOFF104-sw2-L : WsL → ⟪ (Toff104 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Toff104 ∷ []) ⟫ʷ
lem-comm-push-TOFF104-sw2-L c4 = derive (Toff104 ∷ Sw23 ∷ []) (Sw23 ∷ Toff104 ∷ [])
  (re 0 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) ∷
   re 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 1 (q42 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 (q3 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 (q42 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw 9 (q2 c4) ∷
   rw⁻ 0 (q43 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   re 1 3 (CS14 ∷ []) ∷
   rw⁻ 2 (q7 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (CS14⁻ ∷ []) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw⁻ 6 (q43 c4) ∷
   rw⁻ 7 (q8 c4) ∷
   rw 8 (q6 c4) ∷
   rw 7 (q4 c4) ∷
   rw 6 (q42 c4) ∷
   rw 5 (q40 c4) ∷
   rw 4 (q3 c4) ∷
   rw 3 (q41 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q35 c4) ∷
   rw 0 (q42 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw⁻ 2 (q43 c4) ∷
   re 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   re 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q6 c4) ∷
   rw⁻ 8 (q43 c4) ∷
   rw⁻ 9 (q8 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw⁻ 3 (q42 c4) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 (q2 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q2 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 (q2 c4) ∷
   rw⁻ 9 (q42 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   re 3 8 (Toff102 ∷ []) ∷
   re 2 3 (Toff103 ∷ []) ∷
   re 1 3 (Toff104 ∷ []) ∷ []) Eq.refl

private
  q44 : WsL → Eqn
  q44 c4 = eqn (CZ04 ∷ Sw23 ∷ []) (Sw23 ∷ CZ04 ∷ []) (lem-comm-push-CZ04-sw2-L c4)
  q45 : WsL → Eqn
  q45 c4 = eqn (CZ04 ∷ Sw12 ∷ []) (Sw12 ∷ CZ04 ∷ []) (lem-comm-push-CZ04-sw1-L c4)
  q46 : WsL → Eqn
  q46 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl 18 c4)
  q47 : WsL → Eqn
  q47 c4 = eqn (CZ04 ∷ Sw01 ∷ []) (Sw01 ∷ CZ14 ∷ []) (lem-comm-push-CZ04-sw0-L c4)

-- resp CZ04 at 3: 6 steps
lem-resp-CZ04-at-3 : WsL → ⟪ (CZ04 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CZ14 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CZ04-at-3 c4 = derive (CZ04 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CZ14 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q2 c4) ∷
   rw 0 (q44 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw 1 (q45 c4) ∷
   rw⁻ 3 (q46 c4) ∷
   rw 2 (q47 c4) ∷ []) Eq.refl

private
  q48 : WsL → Eqn
  q48 c4 = eqn (CX40 ∷ Sw23 ∷ []) (Sw23 ∷ CX40 ∷ []) (lem-comm-push-CX40-sw2-L c4)
  q49 : WsL → Eqn
  q49 c4 = eqn (CX40 ∷ Sw12 ∷ []) (Sw12 ∷ CX40 ∷ []) (lem-comm-push-CX40-sw1-L c4)
  q50 : WsL → Eqn
  q50 c4 = eqn (CX40 ∷ Sw01 ∷ []) (Sw01 ∷ CX41 ∷ []) (lem-comm-push-CX40-sw0-L c4)

-- resp CX40 at 3: 6 steps
lem-resp-CX40-at-3 : WsL → ⟪ (CX40 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX41 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CX40-at-3 c4 = derive (CX40 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX41 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q2 c4) ∷
   rw 0 (q48 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw 1 (q49 c4) ∷
   rw⁻ 3 (q46 c4) ∷
   rw 2 (q50 c4) ∷ []) Eq.refl

-- resp CX40 at 1: 2 steps
lem-resp-CX40-at-1 : WsL → ⟪ (CX40 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX41 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX40-at-1 c4 = derive (CX40 ∷ []) (Sw01 ∷ CX41 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q46 c4) ∷
   rw 0 (q50 c4) ∷ []) Eq.refl

private
  q51 : WsL → Eqn
  q51 c4 = eqn (CK40 ∷ Sw01 ∷ []) (Sw01 ∷ CK41 ∷ []) (lem-comm-push-CK40-sw0-L c4)

-- resp CK40 at 1: 2 steps
lem-resp-CK40-at-1 : WsL → ⟪ (CK40 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK41 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CK40-at-1 c4 = derive (CK40 ∷ []) (Sw01 ∷ CK41 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q46 c4) ∷
   rw 0 (q51 c4) ∷ []) Eq.refl

private
  q52 : WsL → Eqn
  q52 c4 = eqn (CK40⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK41⁻ ∷ []) (lem-comm-push-CKd40-sw0-L c4)

-- resp CKd40 at 1: 2 steps
lem-resp-CKd40-at-1 : WsL → ⟪ (CK40⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CK41⁻ ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CKd40-at-1 c4 = derive (CK40⁻ ∷ []) (Sw01 ∷ CK41⁻ ∷ Sw01 ∷ [])
  (rw⁻ 1 (q46 c4) ∷
   rw 0 (q52 c4) ∷ []) Eq.refl

-- resp CZ04 at 2: 4 steps
lem-resp-CZ04-at-2 : WsL → ⟪ (CZ04 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CZ14 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CZ04-at-2 c4 = derive (CZ04 ∷ []) (Sw12 ∷ Sw01 ∷ CZ14 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q11 c4) ∷
   rw 0 (q45 c4) ∷
   rw⁻ 2 (q46 c4) ∷
   rw 1 (q47 c4) ∷ []) Eq.refl

-- resp CX40 at 2: 4 steps
lem-resp-CX40-at-2 : WsL → ⟪ (CX40 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX41 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX40-at-2 c4 = derive (CX40 ∷ []) (Sw12 ∷ Sw01 ∷ CX41 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q11 c4) ∷
   rw 0 (q49 c4) ∷
   rw⁻ 2 (q46 c4) ∷
   rw 1 (q50 c4) ∷ []) Eq.refl

private
  q53 : WsL → Eqn
  q53 c4 = eqn (CK40 ∷ Sw12 ∷ []) (Sw12 ∷ CK40 ∷ []) (lem-comm-push-CK40-sw1-L c4)

-- resp CK40 at 2: 4 steps
lem-resp-CK40-at-2 : WsL → ⟪ (CK40 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CK41 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CK40-at-2 c4 = derive (CK40 ∷ []) (Sw12 ∷ Sw01 ∷ CK41 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q11 c4) ∷
   rw 0 (q53 c4) ∷
   rw⁻ 2 (q46 c4) ∷
   rw 1 (q51 c4) ∷ []) Eq.refl

private
  q54 : WsL → Eqn
  q54 c4 = eqn (CK40 ∷ Sw23 ∷ []) (Sw23 ∷ CK40 ∷ []) (lem-comm-push-CK40-sw2-L c4)

-- resp CK40 at 3: 6 steps
lem-resp-CK40-at-3 : WsL → ⟪ (CK40 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CK40-at-3 c4 = derive (CK40 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CK41 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q2 c4) ∷
   rw 0 (q54 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw 1 (q53 c4) ∷
   rw⁻ 3 (q46 c4) ∷
   rw 2 (q51 c4) ∷ []) Eq.refl

private
  q55 : WsL → Eqn
  q55 c4 = eqn (K2 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ []) (wl 40 c4)
  q56 : WsL → Eqn
  q56 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl 47 c4)
  q57 : WsL → Eqn
  q57 c4 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wl 29 c4)
  q58 : WsL → Eqn
  q58 c4 = eqn (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) (wl 1 c4)
  q59 : WsL → Eqn
  q59 c4 = eqn (K2 ∷ Sw34 ∷ []) (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap))
  q60 : WsL → Eqn
  q60 c4 = eqn (CX02 ∷ Sw34 ∷ []) (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))
  q61 : WsL → Eqn
  q61 c4 = eqn (K1 ∷ Sw12 ∷ []) (Sw12 ∷ K2 ∷ []) (wl 73 c4)

-- comm push TOFF203 sw3 L: 76 steps
lem-comm-push-TOFF203-sw3-L : WsL → ⟪ (Toff203 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Toff204 ∷ []) ⟫ʷ
lem-comm-push-TOFF203-sw3-L c4 = derive (Toff203 ∷ Sw34 ∷ []) (Sw34 ∷ Toff204 ∷ [])
  (re 0 1 (Sw12 ∷ Toff103 ∷ Sw12 ∷ []) ∷
   re 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 1 (q42 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 (q3 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 (q42 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw 9 (q2 c4) ∷
   rw⁻ 0 (q55 c4) ∷
   rw⁻ 1 (q56 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   re 2 3 (CX02 ∷ []) ∷
   rw⁻ 3 (q57 c4) ∷
   rw⁻ 6 (q11 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw⁻ 5 (q58 c4) ∷
   rw⁻ 6 (q55 c4) ∷
   rw⁻ 7 (q14 c4) ∷
   rw 8 (q11 c4) ∷
   rw 7 (q8 c4) ∷
   rw 6 (q59 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw 4 (q60 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   re 4 3 (CS24⁻ ∷ []) ∷
   rw 2 (q60 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   re 2 3 (CS24 ∷ []) ∷
   rw 0 (q59 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   rw⁻ 2 (q61 c4) ∷
   rw⁻ 3 (q25 c4) ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 (q11 c4) ∷
   rw⁻ 5 (q26 c4) ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 (q11 c4) ∷
   rw 7 (q13 c4) ∷
   rw⁻ 8 (q61 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   re 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   re 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 8 (q6 c4) ∷
   rw⁻ 9 (q43 c4) ∷
   rw⁻ 10 (q8 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 (q2 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 (q2 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 (q2 c4) ∷
   rw⁻ 10 (q42 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   re 4 8 (Toff102 ∷ []) ∷
   re 3 3 (Toff103 ∷ []) ∷
   re 2 3 (Toff104 ∷ []) ∷
   re 1 3 (Toff204 ∷ []) ∷ []) Eq.refl

private
  q62 : WsL → Eqn
  q62 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl 46 c4)
  q63 : WsL → Eqn
  q63 c4 = eqn (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) (wl 28 c4)

-- comm push TOFF204 sw3 L: 76 steps
lem-comm-push-TOFF204-sw3-L : WsL → ⟪ (Toff204 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Toff203 ∷ []) ⟫ʷ
lem-comm-push-TOFF204-sw3-L c4 = derive (Toff204 ∷ Sw34 ∷ []) (Sw34 ∷ Toff203 ∷ [])
  (re 0 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) ∷
   re 1 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) ∷
   re 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 (q42 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 (q3 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q3 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 (q42 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw 10 (q2 c4) ∷
   rw⁻ 1 (q43 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (CS14 ∷ []) ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CS14⁻ ∷ []) ∷
   rw⁻ 5 (q7 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q43 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw 9 (q6 c4) ∷
   rw⁻ 0 (q55 c4) ∷
   rw⁻ 1 (q10 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   re 2 3 (CX02 ∷ []) ∷
   rw⁻ 3 (q12 c4) ∷
   rw⁻ 6 (q11 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 (q13 c4) ∷
   rw⁻ 6 (q55 c4) ∷
   rw⁻ 7 (q14 c4) ∷
   rw 8 (q11 c4) ∷
   rw 7 (q8 c4) ∷
   rw 6 (q59 c4) ∷
   re 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q6 c4) ∷
   rw 4 (q60 c4) ∷
   re 3 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   rw 2 (q60 c4) ∷
   re 1 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 3 (q6 c4) ∷
   rw 0 (q59 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   rw⁻ 2 (q61 c4) ∷
   rw⁻ 3 (q62 c4) ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 (q11 c4) ∷
   rw⁻ 5 (q63 c4) ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 (q11 c4) ∷
   rw⁻ 7 (q58 c4) ∷
   rw⁻ 8 (q61 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw⁻ 3 (q42 c4) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 (q2 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q2 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 (q2 c4) ∷
   rw⁻ 9 (q42 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   re 3 8 (Toff102 ∷ []) ∷
   re 2 3 (Toff103 ∷ []) ∷
   re 1 3 (Toff203 ∷ []) ∷ []) Eq.refl

-- comm push CCZ023 sw3 L: 58 steps
lem-comm-push-CCZ023-sw3-L : WsL → ⟪ (CCZ023 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ CCZ024 ∷ []) ⟫ʷ
lem-comm-push-CCZ023-sw3-L c4 = derive (CCZ023 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ024 ∷ [])
  (re 0 1 (Sw12 ∷ CCZ013 ∷ Sw12 ∷ []) ∷
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
   rw⁻ 0 (q56 c4) ∷
   rw⁻ 3 (q11 c4) ∷
   re 1 3 (CX02 ∷ []) ∷
   rw⁻ 2 (q57 c4) ∷
   rw⁻ 5 (q11 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q58 c4) ∷
   rw 5 (q11 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw 3 (q60 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   re 3 3 (CS24⁻ ∷ []) ∷
   rw 1 (q60 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   re 1 3 (CS24 ∷ []) ∷
   rw⁻ 1 (q11 c4) ∷
   rw⁻ 2 (q25 c4) ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 3 (q11 c4) ∷
   rw⁻ 4 (q26 c4) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 (q11 c4) ∷
   rw 6 (q13 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   re 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   re 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q6 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 (q2 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q2 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 (q2 c4) ∷
   re 4 5 (CCZ012 ∷ []) ∷
   re 3 3 (CCZ013 ∷ []) ∷
   re 2 3 (CCZ014 ∷ []) ∷
   re 1 3 (CCZ024 ∷ []) ∷ []) Eq.refl

-- comm push CCZ024 sw3 L: 58 steps
lem-comm-push-CCZ024-sw3-L : WsL → ⟪ (CCZ024 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ CCZ023 ∷ []) ⟫ʷ
lem-comm-push-CCZ024-sw3-L c4 = derive (CCZ024 ∷ Sw34 ∷ []) (Sw34 ∷ CCZ023 ∷ [])
  (re 0 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   re 1 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
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
   rw⁻ 0 (q10 c4) ∷
   rw⁻ 3 (q11 c4) ∷
   re 1 3 (CX02 ∷ []) ∷
   rw⁻ 2 (q12 c4) ∷
   rw⁻ 5 (q11 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw 4 (q13 c4) ∷
   rw 5 (q11 c4) ∷
   re 4 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw 3 (q60 c4) ∷
   re 2 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw 1 (q60 c4) ∷
   re 0 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 2 (q6 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   rw⁻ 2 (q62 c4) ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 3 (q11 c4) ∷
   rw⁻ 4 (q63 c4) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 (q11 c4) ∷
   rw⁻ 6 (q58 c4) ∷
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
   re 1 3 (CCZ023 ∷ []) ∷ []) Eq.refl

private
  q64 : WsL → Eqn
  q64 c4 = eqn (Sw04 ∷ Sw23 ∷ []) (Sw23 ∷ Sw04 ∷ []) (lem-comm-push-SWAP04-sw2-L c4)
  q65 : WsL → Eqn
  q65 c4 = eqn (CZ12 ∷ Sw34 ∷ []) (Sw34 ∷ CZ12 ∷ []) (c₃ (CZ ↑) (Swap))
  q66 : WsL → Eqn
  q66 c4 = eqn (CZ23 ∷ Sw12 ∷ []) (Sw12 ∷ CZ13 ∷ []) (wl 36 c4)
  q67 : WsL → Eqn
  q67 c4 = eqn (Sw01 ∷ CZ23 ∷ []) (CZ23 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ))
  q68 : WsL → Eqn
  q68 c4 = eqn (CZ13 ∷ Sw12 ∷ []) (Sw12 ∷ CZ23 ∷ []) (wl 33 c4)

-- comm SWAP03 BOX(2;14): 21 steps
lem-comm-SWAP03-BOX⟨2·14⟩ : WsL → ⟪ (Sw03 ∷ Bx2-14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-14 ∷ Sw03 ∷ []) ⟫ʷ
lem-comm-SWAP03-BOX⟨2·14⟩ c4 = derive (Sw03 ∷ Bx2-14 ∷ []) (Bx2-14 ∷ Sw03 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   re 1 1 (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q6 c4) ∷
   re 1 3 (Sw04 ∷ []) ∷
   rw 1 (q64 c4) ∷
   re 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q65 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (CZ13 ∷ []) ∷
   rw⁻ 6 (q66 c4) ∷
   rw 5 (q67 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   re 4 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 2 (q65 c4) ∷
   re 3 7 (Sw04 ∷ []) ∷
   rw 3 (q64 c4) ∷
   re 4 1 (Sw34 ∷ Sw03 ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   re 0 5 (CZ14 ∷ []) ∷
   re 0 1 (Bx2-14 ∷ []) ∷ []) Eq.refl

private
  q69 : WsL → Eqn
  q69 c4 = eqn (Sw12 ∷ K3 ∷ []) (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K))

-- comm push TOFF302 sw3 L: 76 steps
lem-comm-push-TOFF302-sw3-L : WsL → ⟪ (Toff302 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Toff402 ∷ []) ⟫ʷ
lem-comm-push-TOFF302-sw3-L c4 = derive (Toff302 ∷ Sw34 ∷ []) (Sw34 ∷ Toff402 ∷ [])
  (re 0 1 (Sw12 ∷ Toff301 ∷ Sw12 ∷ []) ∷
   re 1 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 2 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 (q3 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 (q1 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw 9 (q2 c4) ∷
   rw 0 (q69 c4) ∷
   rw⁻ 1 (q56 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   re 2 3 (CX02 ∷ []) ∷
   rw⁻ 3 (q57 c4) ∷
   rw⁻ 6 (q11 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw⁻ 5 (q58 c4) ∷
   rw 6 (q69 c4) ∷
   rw⁻ 7 (q14 c4) ∷
   rw 8 (q11 c4) ∷
   rw 7 (q8 c4) ∷
   rw 6 (q27 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw 4 (q60 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   re 4 3 (CS24⁻ ∷ []) ∷
   rw 2 (q60 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   re 2 3 (CS24 ∷ []) ∷
   rw 0 (q27 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   rw 2 (q9 c4) ∷
   rw⁻ 3 (q25 c4) ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 (q11 c4) ∷
   rw⁻ 5 (q26 c4) ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 (q11 c4) ∷
   rw 7 (q13 c4) ∷
   rw 8 (q9 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw⁻ 3 (q27 c4) ∷
   re 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   re 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 8 (q6 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw⁻ 10 (q8 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 4 (q28 c4) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 (q2 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 (q2 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 (q2 c4) ∷
   rw⁻ 10 (q28 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   re 4 8 (Toff201 ∷ []) ∷
   re 3 3 (Toff301 ∷ []) ∷
   re 2 3 (Toff401 ∷ []) ∷
   re 1 3 (Toff402 ∷ []) ∷ []) Eq.refl

-- comm push TOFF402 sw3 L: 76 steps
lem-comm-push-TOFF402-sw3-L : WsL → ⟪ (Toff402 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Toff302 ∷ []) ⟫ʷ
lem-comm-push-TOFF402-sw3-L c4 = derive (Toff402 ∷ Sw34 ∷ []) (Sw34 ∷ Toff302 ∷ [])
  (re 0 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) ∷
   re 1 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) ∷
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
   rw⁻ 4 (q11 c4) ∷
   re 2 3 (CX02 ∷ []) ∷
   rw⁻ 3 (q12 c4) ∷
   rw⁻ 6 (q11 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 (q13 c4) ∷
   rw 6 (q9 c4) ∷
   rw⁻ 7 (q14 c4) ∷
   rw 8 (q11 c4) ∷
   rw 7 (q8 c4) ∷
   rw 6 (q5 c4) ∷
   re 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q6 c4) ∷
   rw 4 (q60 c4) ∷
   re 3 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   rw 2 (q60 c4) ∷
   re 1 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 3 (q6 c4) ∷
   rw 0 (q5 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   rw 2 (q69 c4) ∷
   rw⁻ 3 (q62 c4) ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 (q11 c4) ∷
   rw⁻ 5 (q63 c4) ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 (q11 c4) ∷
   rw⁻ 7 (q58 c4) ∷
   rw 8 (q69 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw⁻ 3 (q28 c4) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 (q2 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q2 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 (q2 c4) ∷
   rw⁻ 9 (q28 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   re 3 8 (Toff201 ∷ []) ∷
   re 2 3 (Toff301 ∷ []) ∷
   re 1 3 (Toff302 ∷ []) ∷ []) Eq.refl

private
  q70 : WsL → Eqn
  q70 c4 = eqn (Sw04 ∷ Sw01 ∷ []) (Sw01 ∷ Sw14 ∷ []) (lem-comm-push-SWAP04-sw0-L c4)

-- resp SWAP04 at 1: 2 steps
lem-resp-SWAP04-at-1 : WsL → ⟪ (Sw04 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Sw14 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-SWAP04-at-1 c4 = derive (Sw04 ∷ []) (Sw01 ∷ Sw14 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q46 c4) ∷
   rw 0 (q70 c4) ∷ []) Eq.refl

private
  q71 : WsL → Eqn
  q71 c4 = eqn (CX04 ∷ Sw23 ∷ []) (Sw23 ∷ CX04 ∷ []) (lem-comm-push-CX04-sw2-L c4)
  q72 : WsL → Eqn
  q72 c4 = eqn (CX04 ∷ Sw12 ∷ []) (Sw12 ∷ CX04 ∷ []) (lem-comm-push-CX04-sw1-L c4)
  q73 : WsL → Eqn
  q73 c4 = eqn (CX04 ∷ Sw01 ∷ []) (Sw01 ∷ CX14 ∷ []) (lem-comm-push-CX04-sw0-L c4)

-- resp CX04 at 3: 6 steps
lem-resp-CX04-at-3 : WsL → ⟪ (CX04 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX14 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CX04-at-3 c4 = derive (CX04 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CX14 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q2 c4) ∷
   rw 0 (q71 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw 1 (q72 c4) ∷
   rw⁻ 3 (q46 c4) ∷
   rw 2 (q73 c4) ∷ []) Eq.refl

-- comm SWAP03 BOX(2;41): 21 steps
lem-comm-SWAP03-BOX⟨2·41⟩ : WsL → ⟪ (Sw03 ∷ Bx2-41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-41 ∷ Sw03 ∷ []) ⟫ʷ
lem-comm-SWAP03-BOX⟨2·41⟩ c4 = derive (Sw03 ∷ Bx2-41 ∷ []) (Bx2-41 ∷ Sw03 ∷ [])
  (re 1 1 (CZ14 ∷ []) ∷
   re 1 1 (Sw34 ∷ Sw23 ∷ CZ12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 0 (q6 c4) ∷
   re 1 3 (Sw04 ∷ []) ∷
   rw 1 (q64 c4) ∷
   re 2 1 (Sw34 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ Sw34 ∷ []) ∷
   rw⁻ 8 (q65 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (CZ13 ∷ []) ∷
   rw⁻ 6 (q66 c4) ∷
   rw 5 (q67 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   re 4 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 2 (q65 c4) ∷
   re 3 7 (Sw04 ∷ []) ∷
   rw 3 (q64 c4) ∷
   re 4 1 (Sw34 ∷ Sw03 ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   re 0 5 (CZ14 ∷ []) ∷
   re 0 1 (Bx2-41 ∷ []) ∷ []) Eq.refl

private
  q74 : WsL → Eqn
  q74 c4 = eqn (Bx2-03 ∷ Sw12 ∷ []) (Sw12 ∷ Bx1-03 ∷ []) (lem-comm-push-BOX⟨2·03⟩-sw1-L c4)
  q75 : WsL → Eqn
  q75 c4 = eqn (CCZ012 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ012 ∷ []) (wl 101 c4)
  q76 : WsL → Eqn
  q76 c4 = eqn (Sw12 ∷ Toff012 ∷ []) (Toff012 ∷ Sw12 ∷ []) (wl 102 c4)

-- comm push BOX(0;213) sw1 L: 8 steps
lem-comm-push-BOX⟨0·213⟩-sw1-L : WsL → ⟪ (Bx0-213 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx0-123 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·213⟩-sw1-L c4 = derive (Bx0-213 ∷ Sw12 ∷ []) (Sw12 ∷ Bx0-123 ∷ [])
  (re 0 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   rw 5 (q74 c4) ∷
   rw 4 (q75 c4) ∷
   rw⁻ 3 (q76 c4) ∷
   rw 2 (q74 c4) ∷
   rw⁻ 1 (q76 c4) ∷
   rw 0 (q75 c4) ∷
   re 1 6 (Bx0-123 ∷ []) ∷ []) Eq.refl

private
  q77 : WsL → Eqn
  q77 c4 = eqn (Bx1-03 ∷ Sw01 ∷ []) (Sw01 ∷ Bx0-13 ∷ []) (lem-comm-push-BOX⟨1·03⟩-sw0-L c4)
  q78 : WsL → Eqn
  q78 c4 = eqn (CCZ012 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ012 ∷ []) (wl 103 c4)
  q79 : WsL → Eqn
  q79 c4 = eqn (Sw01 ∷ Toff102 ∷ []) (Toff012 ∷ Sw01 ∷ []) (wl 104 c4)

-- comm push BOX(0;123) sw0 L: 8 steps
lem-comm-push-BOX⟨0·123⟩-sw0-L : WsL → ⟪ (Bx0-123 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Bx1-023 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨0·123⟩-sw0-L c4 = derive (Bx0-123 ∷ Sw01 ∷ []) (Sw01 ∷ Bx1-023 ∷ [])
  (re 0 1 (CCZ012 ∷ Toff012 ∷ Bx1-03 ∷ Toff012 ∷ CCZ012 ∷ Bx1-03 ∷ []) ∷
   rw 5 (q77 c4) ∷
   rw 4 (q78 c4) ∷
   rw⁻ 3 (q79 c4) ∷
   rw 2 (q77 c4) ∷
   rw⁻ 1 (q79 c4) ∷
   rw 0 (q78 c4) ∷
   re 1 6 (Bx1-023 ∷ []) ∷ []) Eq.refl

private
  q80 : WsL → Eqn
  q80 c4 = eqn (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) (wl 107 c4)
  q81 : WsL → Eqn
  q81 c4 = eqn (CS14⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS04⁻ ∷ []) (lem-comm-push-CSd14-sw0-L c4)
  q82 : WsL → Eqn
  q82 c4 = eqn (CS14 ∷ Sw01 ∷ []) (Sw01 ∷ CS04 ∷ []) (lem-comm-push-CS14-sw0-L c4)
  q83 : WsL → Eqn
  q83 c4 = eqn (CX10 ∷ Sw34 ∷ []) (Sw34 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Swap ↑))
  q84 : WsL → Eqn
  q84 c4 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Swap))
  q85 : WsL → Eqn
  q85 c4 = eqn (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl 108 c4)

-- comm push CCZ014 sw0 L: 48 steps
lem-comm-push-CCZ014-sw0-L : WsL → ⟪ (CCZ014 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ014 ∷ []) ⟫ʷ
lem-comm-push-CCZ014-sw0-L c4 = derive (CCZ014 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ014 ∷ [])
  (re 0 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
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
   rw 4 (q31 c4) ∷
   rw 3 (q80 c4) ∷
   rw 2 (q81 c4) ∷
   rw 1 (q80 c4) ∷
   rw 0 (q82 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   re 3 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 2 (q6 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   re 5 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q83 c4) ∷
   re 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 4 (q84 c4) ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 (q2 c4) ∷
   rw⁻ 6 (q84 c4) ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 (q2 c4) ∷
   rw 3 (q85 c4) ∷
   re 3 5 (CCZ012 ∷ []) ∷
   re 2 3 (CCZ013 ∷ []) ∷
   re 1 3 (CCZ014 ∷ []) ∷ []) Eq.refl

private
  q86 : WsL → Eqn
  q86 c4 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wl 109 c4)
  q87 : WsL → Eqn
  q87 c4 = eqn (K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wl 110 c4)

-- comm push TOFF104 sw0 L: 63 steps
lem-comm-push-TOFF104-sw0-L : WsL → ⟪ (Toff104 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff014 ∷ []) ⟫ʷ
lem-comm-push-TOFF104-sw0-L c4 = derive (Toff104 ∷ Sw01 ∷ []) (Sw01 ∷ Toff014 ∷ [])
  (re 0 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) ∷
   re 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 1 (q42 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 (q3 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 (q42 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw 9 (q2 c4) ∷
   rw⁻ 0 (q43 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   re 1 3 (CS14 ∷ []) ∷
   rw⁻ 2 (q7 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (CS14⁻ ∷ []) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw⁻ 6 (q43 c4) ∷
   rw⁻ 7 (q8 c4) ∷
   rw 8 (q6 c4) ∷
   rw⁻ 7 (q29 c4) ∷
   rw 6 (q86 c4) ∷
   rw 5 (q31 c4) ∷
   rw 4 (q80 c4) ∷
   rw 3 (q81 c4) ∷
   rw 2 (q80 c4) ∷
   rw 1 (q82 c4) ∷
   rw 0 (q86 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw⁻ 2 (q39 c4) ∷
   re 4 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q83 c4) ∷
   re 6 1 (Sw34 ∷ CS03⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q83 c4) ∷
   re 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 7 (q6 c4) ∷
   rw⁻ 8 (q39 c4) ∷
   rw⁻ 9 (q8 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 (q2 c4) ∷
   rw⁻ 5 (q84 c4) ∷
   re 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q2 c4) ∷
   rw⁻ 7 (q84 c4) ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 (q2 c4) ∷
   rw⁻ 9 (q38 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw 3 (q87 c4) ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 2 3 (Toff013 ∷ []) ∷
   re 1 3 (Toff014 ∷ []) ∷ []) Eq.refl

private
  q88 : WsL → Eqn
  q88 c4 = eqn (Bx0-13 ∷ Sw23 ∷ []) (Sw23 ∷ Bx0-12 ∷ []) (lem-comm-push-BOX⟨0·13⟩-sw2-L c4)

-- comm push BOX(1;023) sw2 L: 12 steps
lem-comm-push-BOX⟨1·023⟩-sw2-L : WsL → ⟪ (Bx1-023 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Bx1-032 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·023⟩-sw2-L c4 = derive (Bx1-023 ∷ Sw23 ∷ []) (Sw23 ∷ Bx1-032 ∷ [])
  (re 0 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) ∷
   rw 5 (q88 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   re 5 3 (CCZ013 ∷ []) ∷
   rw⁻ 3 (q2 c4) ∷
   re 4 3 (Toff103 ∷ []) ∷
   rw 2 (q88 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   re 2 3 (Toff103 ∷ []) ∷
   rw⁻ 0 (q2 c4) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   re 1 6 (Bx1-032 ∷ []) ∷ []) Eq.refl

private
  q89 : WsL → Eqn
  q89 c4 = eqn (Bx0-12 ∷ Sw12 ∷ []) (Sw12 ∷ Bx0-21 ∷ []) (lem-comm-push-BOX⟨0·12⟩-sw1-L c4)

-- comm push BOX(1;032) sw1 L: 12 steps
lem-comm-push-BOX⟨1·032⟩-sw1-L : WsL → ⟪ (Bx1-032 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Bx2-031 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·032⟩-sw1-L c4 = derive (Bx1-032 ∷ Sw12 ∷ []) (Sw12 ∷ Bx2-031 ∷ [])
  (re 0 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) ∷
   rw 5 (q89 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   re 5 3 (CCZ023 ∷ []) ∷
   rw⁻ 3 (q11 c4) ∷
   re 4 3 (Toff203 ∷ []) ∷
   rw 2 (q89 c4) ∷
   rw⁻ 1 (q11 c4) ∷
   re 2 3 (Toff203 ∷ []) ∷
   rw⁻ 0 (q11 c4) ∷
   re 1 3 (CCZ023 ∷ []) ∷
   re 1 6 (Bx2-031 ∷ []) ∷ []) Eq.refl

private
  q90 : WsL → Eqn
  q90 c4 = eqn (Sw12 ∷ Bx0-21 ∷ []) (Bx0-12 ∷ Sw12 ∷ []) (lem-comm-push-BOX⟨0·21⟩-sw1-R c4)

-- comm push BOX(2;031) sw1 R: 12 steps
lem-comm-push-BOX⟨2·031⟩-sw1-R : WsL → ⟪ (Sw12 ∷ Bx2-031 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-032 ∷ Sw12 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨2·031⟩-sw1-R c4 = derive (Sw12 ∷ Bx2-031 ∷ []) (Bx1-032 ∷ Sw12 ∷ [])
  (re 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) ∷
   re 1 1 (Sw12 ∷ CCZ013 ∷ Sw12 ∷ []) ∷
   rw 0 (q11 c4) ∷
   re 2 1 (Sw12 ∷ Toff103 ∷ Sw12 ∷ []) ∷
   rw 1 (q11 c4) ∷
   rw 2 (q90 c4) ∷
   re 4 1 (Sw12 ∷ Toff103 ∷ Sw12 ∷ []) ∷
   rw 3 (q11 c4) ∷
   re 5 1 (Sw12 ∷ CCZ013 ∷ Sw12 ∷ []) ∷
   rw 4 (q11 c4) ∷
   rw 5 (q90 c4) ∷
   re 0 6 (Bx1-032 ∷ []) ∷ []) Eq.refl

-- comm push CCZ014 sw2 R: 47 steps
lem-comm-push-CCZ014-sw2-R : WsL → ⟪ (Sw23 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-CCZ014-sw2-R c4 = derive (Sw23 ∷ CCZ014 ∷ []) (CCZ014 ∷ Sw23 ∷ [])
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
   rw⁻ 0 (q35 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw⁻ 2 (q41 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw 4 (q18 c4) ∷
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

-- comm push TOFF014 sw2 R: 62 steps
lem-comm-push-TOFF014-sw2-R : WsL → ⟪ (Sw23 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-TOFF014-sw2-R c4 = derive (Sw23 ∷ Toff014 ∷ []) (Toff014 ∷ Sw23 ∷ [])
  (re 1 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   re 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 (q38 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 (q3 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q3 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 (q38 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw 10 (q2 c4) ∷
   rw⁻ 1 (q39 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (CS14 ∷ []) ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CS14⁻ ∷ []) ∷
   rw⁻ 5 (q7 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q39 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw 9 (q6 c4) ∷
   rw⁻ 0 (q38 c4) ∷
   rw⁻ 1 (q35 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 3 (q41 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   rw 5 (q18 c4) ∷
   rw⁻ 6 (q38 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   rw⁻ 1 (q39 c4) ∷
   re 3 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 2 (q6 c4) ∷
   rw⁻ 3 (q7 c4) ∷
   re 5 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   re 7 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q39 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw⁻ 1 (q2 c4) ∷
   rw⁻ 2 (q38 c4) ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 (q2 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 (q2 c4) ∷
   rw⁻ 8 (q38 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   re 0 3 (Toff014 ∷ []) ∷ []) Eq.refl

private
  q91 : WsL → Eqn
  q91 c4 = eqn (Sw23 ∷ Bx0-12 ∷ []) (Bx0-13 ∷ Sw23 ∷ []) (lem-comm-push-BOX⟨0·12⟩-sw2-R c4)

-- comm push BOX(1;032) sw2 R: 12 steps
lem-comm-push-BOX⟨1·032⟩-sw2-R : WsL → ⟪ (Sw23 ∷ Bx1-032 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-023 ∷ Sw23 ∷ []) ⟫ʷ
lem-comm-push-BOX⟨1·032⟩-sw2-R c4 = derive (Sw23 ∷ Bx1-032 ∷ []) (Bx1-023 ∷ Sw23 ∷ [])
  (re 1 1 (CCZ013 ∷ Toff103 ∷ Bx0-12 ∷ Toff103 ∷ CCZ013 ∷ Bx0-12 ∷ []) ∷
   re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   rw 0 (q2 c4) ∷
   re 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   rw 1 (q2 c4) ∷
   rw 2 (q91 c4) ∷
   re 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   rw 3 (q2 c4) ∷
   re 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   rw 4 (q2 c4) ∷
   rw 5 (q91 c4) ∷
   re 0 6 (Bx1-023 ∷ []) ∷ []) Eq.refl
