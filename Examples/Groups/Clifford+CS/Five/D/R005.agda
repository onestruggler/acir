{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.R005 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-push-CS04-sw0-L ; lem-comm-push-CS04-sw1-L ; lem-comm-push-CS04-sw1-R ; lem-comm-push-CS04-sw2-L ; lem-comm-push-CS04-sw2-R ; lem-comm-push-CSd04-sw0-L ; lem-comm-push-CSd04-sw1-L ; lem-comm-push-CSd04-sw2-L ; lem-comm-push-CX04-sw0-L ; lem-comm-push-CX04-sw1-L ; lem-comm-push-CZ04-sw0-L)

private
  q1 : WsL → Eqn
  q1 c4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wl 3 c4)
  q2 : WsL → Eqn
  q2 c4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap))
  q3 : WsL → Eqn
  q3 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl 4 c4)
  q4 : WsL → Eqn
  q4 c4 = eqn (CX01 ∷ Sw34 ∷ []) (Sw34 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap ↑))
  q5 : WsL → Eqn
  q5 c4 = eqn (CS24 ∷ Sw12 ∷ []) (Sw12 ∷ CS14 ∷ []) (wl 5 c4)
  q6 : WsL → Eqn
  q6 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl 6 c4)
  q7 : WsL → Eqn
  q7 c4 = eqn (CS24⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS14⁻ ∷ []) (wl 7 c4)
  q8 : WsL → Eqn
  q8 c4 = eqn (Sw12 ∷ CS04 ∷ []) (CS04 ∷ Sw12 ∷ []) (lem-comm-push-CS04-sw1-R c4)
  q9 : WsL → Eqn
  q9 c4 = eqn (CS34 ∷ Sw23 ∷ []) (Sw23 ∷ CS24 ∷ []) (wl 8 c4)
  q10 : WsL → Eqn
  q10 c4 = eqn (CS34⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS24⁻ ∷ []) (wl 9 c4)
  q11 : WsL → Eqn
  q11 c4 = eqn (Sw23 ∷ CS04 ∷ []) (CS04 ∷ Sw23 ∷ []) (lem-comm-push-CS04-sw2-R c4)
  q12 : WsL → Eqn
  q12 c4 = eqn (CS04 ∷ Sw12 ∷ []) (Sw12 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw1-L c4)
  q13 : WsL → Eqn
  q13 c4 = eqn (CX03 ∷ Sw12 ∷ []) (Sw12 ∷ CX03 ∷ []) (wl 10 c4)
  q14 : WsL → Eqn
  q14 c4 = eqn (Sw12 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS • CS • CS))
  q15 : WsL → Eqn
  q15 c4 = eqn (Sw12 ∷ CS34 ∷ []) (CS34 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CS))
  q16 : WsL → Eqn
  q16 c4 = eqn (CS24 ∷ Sw23 ∷ []) (Sw23 ∷ CS34 ∷ []) (wl 11 c4)
  q17 : WsL → Eqn
  q17 c4 = eqn (CS24⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS34⁻ ∷ []) (wl 12 c4)
  q18 : WsL → Eqn
  q18 c4 = eqn (CS14 ∷ Sw12 ∷ []) (Sw12 ∷ CS24 ∷ []) (wl 13 c4)
  q19 : WsL → Eqn
  q19 c4 = eqn (CS14⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS24⁻ ∷ []) (wl 14 c4)

-- comm push CCZ034 sw1 L: 83 steps
lem-comm-push-CCZ034-sw1-L : WsL → ⟪ (CCZ034 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ CCZ034 ∷ []) ⟫ʷ
lem-comm-push-CCZ034-sw1-L c4 = derive (CCZ034 ∷ Sw12 ∷ []) (Sw12 ∷ CCZ034 ∷ [])
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
   rw⁻ 1 (q5 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (CX02 ∷ []) ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 (q8 c4) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 0 (q9 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   re 1 3 (CX03 ∷ []) ∷
   rw⁻ 2 (q10 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CX03 ∷ []) ∷
   rw 4 (q11 c4) ∷
   rw 5 (q1 c4) ∷
   rw 4 (q12 c4) ∷
   rw 3 (q13 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw 1 (q13 c4) ∷
   rw⁻ 0 (q15 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q16 c4) ∷
   re 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q11 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw⁻ 3 (q18 c4) ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw 7 (q8 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   re 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q3 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   re 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 8 (q3 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 (q1 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 (q1 c4) ∷
   re 5 5 (CCZ012 ∷ []) ∷
   re 4 3 (CCZ013 ∷ []) ∷
   re 3 3 (CCZ014 ∷ []) ∷
   re 2 3 (CCZ024 ∷ []) ∷
   re 1 3 (CCZ034 ∷ []) ∷ []) Eq.refl

private
  q20 : WsL → Eqn
  q20 c4 = eqn (CS04 ∷ Sw01 ∷ []) (Sw01 ∷ CS14 ∷ []) (lem-comm-push-CS04-sw0-L c4)
  q21 : WsL → Eqn
  q21 c4 = eqn (CX03 ∷ Sw01 ∷ []) (Sw01 ∷ CX13 ∷ []) (wl 16 c4)
  q22 : WsL → Eqn
  q22 c4 = eqn (Sw01 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑))
  q23 : WsL → Eqn
  q23 c4 = eqn (Sw01 ∷ CS34 ∷ []) (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))
  q24 : WsL → Eqn
  q24 c4 = eqn (CS14 ∷ Sw23 ∷ []) (Sw23 ∷ CS14 ∷ []) (wl 17 c4)
  q25 : WsL → Eqn
  q25 c4 = eqn (CX12 ∷ Sw34 ∷ []) (Sw34 ∷ CX12 ∷ []) (c₃ (CX₀₁ ↑) (Swap))

-- comm push CCZ034 sw0 L: 64 steps
lem-comm-push-CCZ034-sw0-L : WsL → ⟪ (CCZ034 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ134 ∷ []) ⟫ʷ
lem-comm-push-CCZ034-sw0-L c4 = derive (CCZ034 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ134 ∷ [])
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
   rw⁻ 1 (q5 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (CX02 ∷ []) ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 (q8 c4) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 0 (q9 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   re 1 3 (CX03 ∷ []) ∷
   rw⁻ 2 (q10 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CX03 ∷ []) ∷
   rw 4 (q11 c4) ∷
   rw 5 (q1 c4) ∷
   rw 4 (q20 c4) ∷
   rw 3 (q21 c4) ∷
   rw⁻ 2 (q22 c4) ∷
   rw 1 (q21 c4) ∷
   rw⁻ 0 (q23 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q16 c4) ∷
   re 4 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   re 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 6 (q24 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   re 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 3 (q3 c4) ∷
   rw⁻ 4 (q25 c4) ∷
   re 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 6 (q25 c4) ∷
   re 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 7 (q3 c4) ∷
   re 3 5 (CCZ123 ∷ []) ∷
   re 2 3 (CCZ124 ∷ []) ∷
   re 1 3 (CCZ134 ∷ []) ∷ []) Eq.refl

private
  q26 : WsL → Eqn
  q26 c4 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (c₁ (K) (Swap ↑))
  q27 : WsL → Eqn
  q27 c4 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (c₁ (iI) (Swap ↑))
  q28 : WsL → Eqn
  q28 c4 = eqn (K0 ∷ Sw34 ∷ []) (Sw34 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑))
  q29 : WsL → Eqn
  q29 c4 = eqn (ι ∷ Sw34 ∷ []) (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑))
  q30 : WsL → Eqn
  q30 c4 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (c₁ (K) (Swap))
  q31 : WsL → Eqn
  q31 c4 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (c₁ (iI) (Swap))
  q32 : WsL → Eqn
  q32 c4 = eqn (Sw01 ∷ ι ∷ []) (ι ∷ Sw01 ∷ []) (wl 25 c4)
  q33 : WsL → Eqn
  q33 c4 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wl 26 c4)
  q34 : WsL → Eqn
  q34 c4 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (c₂ (K ↑) (Swap))
  q35 : WsL → Eqn
  q35 c4 = eqn (K1 ∷ Sw34 ∷ []) (Sw34 ∷ K1 ∷ []) (c₂ (K ↑) (Swap ↑))
  q36 : WsL → Eqn
  q36 c4 = eqn (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wl 27 c4)

-- comm push TOFF034 sw0 L: 86 steps
lem-comm-push-TOFF034-sw0-L : WsL → ⟪ (Toff034 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff134 ∷ []) ⟫ʷ
lem-comm-push-TOFF034-sw0-L c4 = derive (Toff034 ∷ Sw01 ∷ []) (Sw01 ∷ Toff134 ∷ [])
  (re 0 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) ∷
   re 1 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 (q26 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q2 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 (q26 c4) ∷
   rw⁻ 10 (q27 c4) ∷
   rw 11 (q1 c4) ∷
   rw⁻ 2 (q28 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q28 c4) ∷
   rw⁻ 9 (q29 c4) ∷
   rw 10 (q3 c4) ∷
   rw⁻ 1 (q30 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 (q8 c4) ∷
   rw⁻ 7 (q30 c4) ∷
   rw⁻ 8 (q31 c4) ∷
   rw 9 (q6 c4) ∷
   rw⁻ 0 (q26 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (CX03 ∷ []) ∷
   rw⁻ 3 (q10 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CX03 ∷ []) ∷
   rw 5 (q11 c4) ∷
   rw⁻ 6 (q26 c4) ∷
   rw⁻ 7 (q27 c4) ∷
   rw 8 (q1 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   rw 6 (q33 c4) ∷
   rw 5 (q20 c4) ∷
   rw 4 (q21 c4) ∷
   rw⁻ 3 (q22 c4) ∷
   rw 2 (q21 c4) ∷
   rw⁻ 1 (q23 c4) ∷
   rw 0 (q33 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q34 c4) ∷
   rw⁻ 3 (q16 c4) ∷
   re 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q17 c4) ∷
   re 7 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 7 (q24 c4) ∷
   rw⁻ 8 (q34 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 3 (q35 c4) ∷
   re 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q25 c4) ∷
   re 7 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q3 c4) ∷
   rw⁻ 7 (q25 c4) ∷
   re 9 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 8 (q3 c4) ∷
   rw⁻ 9 (q35 c4) ∷
   rw⁻ 10 (q29 c4) ∷
   rw 3 (q36 c4) ∷
   re 3 8 (Toff123 ∷ []) ∷
   re 2 3 (Toff124 ∷ []) ∷
   re 1 3 (Toff134 ∷ []) ∷ []) Eq.refl

-- comm push TOFF034 sw1 L: 110 steps
lem-comm-push-TOFF034-sw1-L : WsL → ⟪ (Toff034 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Toff034 ∷ []) ⟫ʷ
lem-comm-push-TOFF034-sw1-L c4 = derive (Toff034 ∷ Sw12 ∷ []) (Sw12 ∷ Toff034 ∷ [])
  (re 0 1 (Sw23 ∷ Toff024 ∷ Sw23 ∷ []) ∷
   re 1 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 (q26 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q2 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 (q26 c4) ∷
   rw⁻ 10 (q27 c4) ∷
   rw 11 (q1 c4) ∷
   rw⁻ 2 (q28 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q28 c4) ∷
   rw⁻ 9 (q29 c4) ∷
   rw 10 (q3 c4) ∷
   rw⁻ 1 (q30 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 (q8 c4) ∷
   rw⁻ 7 (q30 c4) ∷
   rw⁻ 8 (q31 c4) ∷
   rw 9 (q6 c4) ∷
   rw⁻ 0 (q26 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (CX03 ∷ []) ∷
   rw⁻ 3 (q10 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CX03 ∷ []) ∷
   rw 5 (q11 c4) ∷
   rw⁻ 6 (q26 c4) ∷
   rw⁻ 7 (q27 c4) ∷
   rw 8 (q1 c4) ∷
   rw 7 (q31 c4) ∷
   rw 6 (q30 c4) ∷
   rw 5 (q12 c4) ∷
   rw 4 (q13 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw 2 (q13 c4) ∷
   rw⁻ 1 (q15 c4) ∷
   rw 0 (q30 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q26 c4) ∷
   rw⁻ 3 (q16 c4) ∷
   re 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q17 c4) ∷
   re 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q11 c4) ∷
   rw⁻ 8 (q26 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw⁻ 3 (q30 c4) ∷
   rw⁻ 4 (q18 c4) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   re 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 7 (q6 c4) ∷
   rw 8 (q8 c4) ∷
   rw⁻ 9 (q30 c4) ∷
   rw⁻ 10 (q31 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 4 (q28 c4) ∷
   re 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   re 8 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 7 (q3 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   re 10 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 9 (q3 c4) ∷
   rw⁻ 10 (q28 c4) ∷
   rw⁻ 11 (q29 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 5 (q26 c4) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 (q1 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 (q1 c4) ∷
   rw⁻ 11 (q26 c4) ∷
   rw⁻ 12 (q27 c4) ∷
   re 5 8 (Toff012 ∷ []) ∷
   re 4 3 (Toff013 ∷ []) ∷
   re 3 3 (Toff014 ∷ []) ∷
   re 2 3 (Toff024 ∷ []) ∷
   re 1 3 (Toff034 ∷ []) ∷ []) Eq.refl

private
  q37 : WsL → Eqn
  q37 c4 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wl 39 c4)
  q38 : WsL → Eqn
  q38 c4 = eqn (Sw01 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q39 : WsL → Eqn
  q39 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))

-- comm push CCZ024 sw0 L: 46 steps
lem-comm-push-CCZ024-sw0-L : WsL → ⟪ (CCZ024 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CCZ124 ∷ []) ⟫ʷ
lem-comm-push-CCZ024-sw0-L c4 = derive (CCZ024 ∷ Sw01 ∷ []) (Sw01 ∷ CCZ124 ∷ [])
  (re 0 1 (Sw12 ∷ CCZ014 ∷ Sw12 ∷ []) ∷
   re 1 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
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
   rw⁻ 0 (q5 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   re 1 3 (CX02 ∷ []) ∷
   rw⁻ 2 (q7 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw 4 (q8 c4) ∷
   rw 5 (q6 c4) ∷
   rw 4 (q20 c4) ∷
   rw 3 (q37 c4) ∷
   rw⁻ 2 (q38 c4) ∷
   rw 1 (q37 c4) ∷
   rw⁻ 0 (q39 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   re 3 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 2 (q3 c4) ∷
   rw⁻ 3 (q25 c4) ∷
   re 5 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q25 c4) ∷
   re 7 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 6 (q3 c4) ∷
   re 2 5 (CCZ123 ∷ []) ∷
   re 1 3 (CCZ124 ∷ []) ∷ []) Eq.refl

private
  q40 : WsL → Eqn
  q40 c4 = eqn (K2 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ []) (wl 40 c4)
  q41 : WsL → Eqn
  q41 c4 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (c₂ (Swap) (K))
  q42 : WsL → Eqn
  q42 c4 = eqn (K2 ∷ Sw34 ∷ []) (Sw34 ∷ K2 ∷ []) (c₃ (K ↑ ↑) (Swap))
  q43 : WsL → Eqn
  q43 c4 = eqn (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (wl 41 c4)

-- comm push TOFF204 sw0 L: 62 steps
lem-comm-push-TOFF204-sw0-L : WsL → ⟪ (Toff204 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff214 ∷ []) ⟫ʷ
lem-comm-push-TOFF204-sw0-L c4 = derive (Toff204 ∷ Sw01 ∷ []) (Sw01 ∷ Toff214 ∷ [])
  (re 0 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) ∷
   re 1 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) ∷
   re 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 (q34 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 (q2 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 (q34 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw 10 (q1 c4) ∷
   rw⁻ 1 (q35 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 2 3 (CS14 ∷ []) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (CS14⁻ ∷ []) ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q35 c4) ∷
   rw⁻ 8 (q29 c4) ∷
   rw 9 (q3 c4) ∷
   rw⁻ 0 (q40 c4) ∷
   rw⁻ 1 (q5 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (CX02 ∷ []) ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 (q8 c4) ∷
   rw⁻ 6 (q40 c4) ∷
   rw⁻ 7 (q31 c4) ∷
   rw 8 (q6 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   rw⁻ 6 (q41 c4) ∷
   rw 5 (q20 c4) ∷
   rw 4 (q37 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   rw 2 (q37 c4) ∷
   rw⁻ 1 (q39 c4) ∷
   rw⁻ 0 (q41 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw⁻ 2 (q42 c4) ∷
   re 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 3 (q3 c4) ∷
   rw⁻ 4 (q25 c4) ∷
   re 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 6 (q25 c4) ∷
   re 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 7 (q3 c4) ∷
   rw⁻ 8 (q42 c4) ∷
   rw⁻ 9 (q29 c4) ∷
   rw 2 (q43 c4) ∷
   re 2 8 (Toff213 ∷ []) ∷
   re 1 3 (Toff214 ∷ []) ∷ []) Eq.refl

private
  q44 : WsL → Eqn
  q44 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl 18 c4)
  q45 : WsL → Eqn
  q45 c4 = eqn (CS04⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS14⁻ ∷ []) (lem-comm-push-CSd04-sw0-L c4)

-- resp CSd04 at 1: 2 steps
lem-resp-CSd04-at-1 : WsL → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS14⁻ ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CSd04-at-1 c4 = derive (CS04⁻ ∷ []) (Sw01 ∷ CS14⁻ ∷ Sw01 ∷ [])
  (rw⁻ 1 (q44 c4) ∷
   rw 0 (q45 c4) ∷ []) Eq.refl

private
  q46 : WsL → Eqn
  q46 c4 = eqn (CS04⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS04⁻ ∷ []) (lem-comm-push-CSd04-sw1-L c4)

-- resp CSd04 at 2: 4 steps
lem-resp-CSd04-at-2 : WsL → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS14⁻ ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CSd04-at-2 c4 = derive (CS04⁻ ∷ []) (Sw12 ∷ Sw01 ∷ CS14⁻ ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q6 c4) ∷
   rw 0 (q46 c4) ∷
   rw⁻ 2 (q44 c4) ∷
   rw 1 (q45 c4) ∷ []) Eq.refl

private
  q47 : WsL → Eqn
  q47 c4 = eqn (CX04 ∷ Sw01 ∷ []) (Sw01 ∷ CX14 ∷ []) (lem-comm-push-CX04-sw0-L c4)

-- resp CX04 at 1: 2 steps
lem-resp-CX04-at-1 : WsL → ⟪ (CX04 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CX14 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CX04-at-1 c4 = derive (CX04 ∷ []) (Sw01 ∷ CX14 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q44 c4) ∷
   rw 0 (q47 c4) ∷ []) Eq.refl

private
  q48 : WsL → Eqn
  q48 c4 = eqn (CS04 ∷ Sw23 ∷ []) (Sw23 ∷ CS04 ∷ []) (lem-comm-push-CS04-sw2-L c4)
  q49 : WsL → Eqn
  q49 c4 = eqn (CS14⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS14⁻ ∷ []) (wl 48 c4)

-- comm push CCZ014 sw2 L: 47 steps
lem-comm-push-CCZ014-sw2-L : WsL → ⟪ (CCZ014 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ CCZ014 ∷ []) ⟫ʷ
lem-comm-push-CCZ014-sw2-L c4 = derive (CCZ014 ∷ Sw23 ∷ []) (Sw23 ∷ CCZ014 ∷ [])
  (re 0 1 (Sw34 ∷ CCZ013 ∷ Sw34 ∷ []) ∷
   re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw⁻ 3 (q1 c4) ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 (q2 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 (q2 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   re 0 3 (CS14 ∷ []) ∷
   rw⁻ 1 (q4 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 2 3 (CS14⁻ ∷ []) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (CS04 ∷ []) ∷
   rw 5 (q3 c4) ∷
   rw 4 (q48 c4) ∷
   rw 3 (q2 c4) ∷
   rw 2 (q49 c4) ∷
   rw 1 (q2 c4) ∷
   rw 0 (q24 c4) ∷
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
   re 1 3 (CCZ014 ∷ []) ∷ []) Eq.refl

private
  q50 : WsL → Eqn
  q50 c4 = eqn (CX04 ∷ Sw12 ∷ []) (Sw12 ∷ CX04 ∷ []) (lem-comm-push-CX04-sw1-L c4)

-- resp CX04 at 2: 4 steps
lem-resp-CX04-at-2 : WsL → ⟪ (CX04 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CX14 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CX04-at-2 c4 = derive (CX04 ∷ []) (Sw12 ∷ Sw01 ∷ CX14 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q6 c4) ∷
   rw 0 (q50 c4) ∷
   rw⁻ 2 (q44 c4) ∷
   rw 1 (q47 c4) ∷ []) Eq.refl

private
  q51 : WsL → Eqn
  q51 c4 = eqn (CZ04 ∷ Sw01 ∷ []) (Sw01 ∷ CZ14 ∷ []) (lem-comm-push-CZ04-sw0-L c4)

-- resp CZ04 at 1: 2 steps
lem-resp-CZ04-at-1 : WsL → ⟪ (CZ04 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CZ14 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CZ04-at-1 c4 = derive (CZ04 ∷ []) (Sw01 ∷ CZ14 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q44 c4) ∷
   rw 0 (q51 c4) ∷ []) Eq.refl

-- comm push TOFF024 sw0 L: 62 steps
lem-comm-push-TOFF024-sw0-L : WsL → ⟪ (Toff024 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff124 ∷ []) ⟫ʷ
lem-comm-push-TOFF024-sw0-L c4 = derive (Toff024 ∷ Sw01 ∷ []) (Sw01 ∷ Toff124 ∷ [])
  (re 0 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) ∷
   re 1 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   re 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 (q26 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 (q2 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 (q26 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw 10 (q1 c4) ∷
   rw⁻ 1 (q28 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 2 3 (CS14 ∷ []) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (CS14⁻ ∷ []) ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q28 c4) ∷
   rw⁻ 8 (q29 c4) ∷
   rw 9 (q3 c4) ∷
   rw⁻ 0 (q30 c4) ∷
   rw⁻ 1 (q5 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (CX02 ∷ []) ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 (q8 c4) ∷
   rw⁻ 6 (q30 c4) ∷
   rw⁻ 7 (q31 c4) ∷
   rw 8 (q6 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   rw 6 (q33 c4) ∷
   rw 5 (q20 c4) ∷
   rw 4 (q37 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   rw 2 (q37 c4) ∷
   rw⁻ 1 (q39 c4) ∷
   rw 0 (q33 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   re 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 3 (q3 c4) ∷
   rw⁻ 4 (q25 c4) ∷
   re 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 6 (q25 c4) ∷
   re 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 7 (q3 c4) ∷
   rw⁻ 8 (q35 c4) ∷
   rw⁻ 9 (q29 c4) ∷
   rw 2 (q36 c4) ∷
   re 2 8 (Toff123 ∷ []) ∷
   re 1 3 (Toff124 ∷ []) ∷ []) Eq.refl

-- resp CS04 at 2: 4 steps
lem-resp-CS04-at-2 : WsL → ⟪ (CS04 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw01 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ []) ⟫ʷ
lem-resp-CS04-at-2 c4 = derive (CS04 ∷ []) (Sw12 ∷ Sw01 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ [])
  (rw⁻ 1 (q6 c4) ∷
   rw 0 (q12 c4) ∷
   rw⁻ 2 (q44 c4) ∷
   rw 1 (q20 c4) ∷ []) Eq.refl

-- resp CS04 at 1: 2 steps
lem-resp-CS04-at-1 : WsL → ⟪ (CS04 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ CS14 ∷ Sw01 ∷ []) ⟫ʷ
lem-resp-CS04-at-1 c4 = derive (CS04 ∷ []) (Sw01 ∷ CS14 ∷ Sw01 ∷ [])
  (rw⁻ 1 (q44 c4) ∷
   rw 0 (q20 c4) ∷ []) Eq.refl

private
  q52 : WsL → Eqn
  q52 c4 = eqn (CS04⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS04⁻ ∷ []) (lem-comm-push-CSd04-sw2-L c4)

-- resp CSd04 at 3: 6 steps
lem-resp-CSd04-at-3 : WsL → ⟪ (CS04⁻ ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS14⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CSd04-at-3 c4 = derive (CS04⁻ ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS14⁻ ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q1 c4) ∷
   rw 0 (q52 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw 1 (q46 c4) ∷
   rw⁻ 3 (q44 c4) ∷
   rw 2 (q45 c4) ∷ []) Eq.refl

-- resp CS04 at 3: 6 steps
lem-resp-CS04-at-3 : WsL → ⟪ (CS04 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ []) ⟫ʷ
lem-resp-CS04-at-3 c4 = derive (CS04 ∷ []) (Sw23 ∷ Sw12 ∷ Sw01 ∷ CS14 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ [])
  (rw⁻ 1 (q1 c4) ∷
   rw 0 (q48 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw 1 (q12 c4) ∷
   rw⁻ 3 (q44 c4) ∷
   rw 2 (q20 c4) ∷ []) Eq.refl

private
  q53 : WsL → Eqn
  q53 c4 = eqn (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ []) (wl 64 c4)
  q54 : WsL → Eqn
  q54 c4 = eqn (K4 ∷ Sw34 ∷ []) (Sw34 ∷ K3 ∷ []) (wl 65 c4)
  q55 : WsL → Eqn
  q55 c4 = eqn (Sw23 ∷ K4 ∷ []) (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K))
  q56 : WsL → Eqn
  q56 c4 = eqn (K3 ∷ Sw34 ∷ []) (Sw34 ∷ K4 ∷ []) (wl 66 c4)
  q57 : WsL → Eqn
  q57 c4 = eqn (K2 ∷ Sw23 ∷ []) (Sw23 ∷ K3 ∷ []) (wl 67 c4)

-- comm push TOFF401 sw2 L: 62 steps
lem-comm-push-TOFF401-sw2-L : WsL → ⟪ (Toff401 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sw23 ∷ Toff401 ∷ []) ⟫ʷ
lem-comm-push-TOFF401-sw2-L c4 = derive (Toff401 ∷ Sw23 ∷ []) (Sw23 ∷ Toff401 ∷ [])
  (re 0 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) ∷
   re 1 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 2 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw⁻ 1 (q53 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 (q53 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw 9 (q1 c4) ∷
   rw⁻ 0 (q54 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   re 1 3 (CS14 ∷ []) ∷
   rw⁻ 2 (q4 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (CS14⁻ ∷ []) ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (CS04 ∷ []) ∷
   rw⁻ 6 (q54 c4) ∷
   rw⁻ 7 (q29 c4) ∷
   rw 8 (q3 c4) ∷
   rw 7 (q27 c4) ∷
   rw⁻ 6 (q55 c4) ∷
   rw 5 (q48 c4) ∷
   rw 4 (q2 c4) ∷
   rw 3 (q49 c4) ∷
   rw 2 (q2 c4) ∷
   rw 1 (q24 c4) ∷
   rw⁻ 0 (q55 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw⁻ 2 (q56 c4) ∷
   re 4 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 3 (q3 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   re 6 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   re 8 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q3 c4) ∷
   rw⁻ 8 (q56 c4) ∷
   rw⁻ 9 (q29 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 3 (q57 c4) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 (q1 c4) ∷
   rw⁻ 9 (q57 c4) ∷
   rw⁻ 10 (q27 c4) ∷
   re 3 8 (Toff201 ∷ []) ∷
   re 2 3 (Toff301 ∷ []) ∷
   re 1 3 (Toff401 ∷ []) ∷ []) Eq.refl

private
  q58 : WsL → Eqn
  q58 c4 = eqn (Sw12 ∷ K4 ∷ []) (K4 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K ↑))
  q59 : WsL → Eqn
  q59 c4 = eqn (Sw01 ∷ K4 ∷ []) (K4 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑ ↑))
  q60 : WsL → Eqn
  q60 c4 = eqn (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (wl 68 c4)

-- comm push TOFF402 sw0 L: 62 steps
lem-comm-push-TOFF402-sw0-L : WsL → ⟪ (Toff402 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff412 ∷ []) ⟫ʷ
lem-comm-push-TOFF402-sw0-L c4 = derive (Toff402 ∷ Sw01 ∷ []) (Sw01 ∷ Toff412 ∷ [])
  (re 0 1 (Sw12 ∷ Toff401 ∷ Sw12 ∷ []) ∷
   re 1 1 (Sw34 ∷ Toff301 ∷ Sw34 ∷ []) ∷
   re 2 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw⁻ 2 (q53 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 (q2 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 (q53 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw 10 (q1 c4) ∷
   rw⁻ 1 (q54 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 2 3 (CS14 ∷ []) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (CS14⁻ ∷ []) ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q54 c4) ∷
   rw⁻ 8 (q29 c4) ∷
   rw 9 (q3 c4) ∷
   rw 0 (q58 c4) ∷
   rw⁻ 1 (q5 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (CX02 ∷ []) ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 (q8 c4) ∷
   rw 6 (q58 c4) ∷
   rw⁻ 7 (q31 c4) ∷
   rw 8 (q6 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   rw⁻ 6 (q59 c4) ∷
   rw 5 (q20 c4) ∷
   rw 4 (q37 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   rw 2 (q37 c4) ∷
   rw⁻ 1 (q39 c4) ∷
   rw⁻ 0 (q59 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   rw⁻ 2 (q56 c4) ∷
   re 4 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 3 (q3 c4) ∷
   rw⁻ 4 (q25 c4) ∷
   re 6 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 6 (q25 c4) ∷
   re 8 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 7 (q3 c4) ∷
   rw⁻ 8 (q56 c4) ∷
   rw⁻ 9 (q29 c4) ∷
   rw 2 (q60 c4) ∷
   re 2 8 (Toff312 ∷ []) ∷
   re 1 3 (Toff412 ∷ []) ∷ []) Eq.refl

private
  q61 : WsL → Eqn
  q61 c4 = eqn (Sw12 ∷ K3 ∷ []) (K3 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (K))
  q62 : WsL → Eqn
  q62 c4 = eqn (K1 ∷ Sw12 ∷ []) (Sw12 ∷ K2 ∷ []) (wl 73 c4)

-- comm push TOFF304 sw1 L: 110 steps
lem-comm-push-TOFF304-sw1-L : WsL → ⟪ (Toff304 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Toff304 ∷ []) ⟫ʷ
lem-comm-push-TOFF304-sw1-L c4 = derive (Toff304 ∷ Sw12 ∷ []) (Sw12 ∷ Toff304 ∷ [])
  (re 0 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) ∷
   re 1 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 3 (q34 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q2 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 (q34 c4) ∷
   rw⁻ 10 (q27 c4) ∷
   rw 11 (q1 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q35 c4) ∷
   rw⁻ 9 (q29 c4) ∷
   rw 10 (q3 c4) ∷
   rw⁻ 1 (q40 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 (q8 c4) ∷
   rw⁻ 7 (q40 c4) ∷
   rw⁻ 8 (q31 c4) ∷
   rw 9 (q6 c4) ∷
   rw⁻ 0 (q53 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (CX03 ∷ []) ∷
   rw⁻ 3 (q10 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CX03 ∷ []) ∷
   rw 5 (q11 c4) ∷
   rw⁻ 6 (q53 c4) ∷
   rw⁻ 7 (q27 c4) ∷
   rw 8 (q1 c4) ∷
   rw 7 (q31 c4) ∷
   rw⁻ 6 (q61 c4) ∷
   rw 5 (q12 c4) ∷
   rw 4 (q13 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw 2 (q13 c4) ∷
   rw⁻ 1 (q15 c4) ∷
   rw⁻ 0 (q61 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q57 c4) ∷
   rw⁻ 3 (q16 c4) ∷
   re 5 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q17 c4) ∷
   re 7 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q11 c4) ∷
   rw⁻ 8 (q57 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw⁻ 3 (q62 c4) ∷
   rw⁻ 4 (q18 c4) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   re 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 7 (q6 c4) ∷
   rw 8 (q8 c4) ∷
   rw⁻ 9 (q62 c4) ∷
   rw⁻ 10 (q31 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 4 (q35 c4) ∷
   re 6 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   re 8 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 7 (q3 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   re 10 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 9 (q3 c4) ∷
   rw⁻ 10 (q35 c4) ∷
   rw⁻ 11 (q29 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 5 (q34 c4) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 (q1 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 (q1 c4) ∷
   rw⁻ 11 (q34 c4) ∷
   rw⁻ 12 (q27 c4) ∷
   re 5 8 (Toff102 ∷ []) ∷
   re 4 3 (Toff103 ∷ []) ∷
   re 3 3 (Toff104 ∷ []) ∷
   re 2 3 (Toff204 ∷ []) ∷
   re 1 3 (Toff304 ∷ []) ∷ []) Eq.refl

private
  q63 : WsL → Eqn
  q63 c4 = eqn (Sw01 ∷ K3 ∷ []) (K3 ∷ Sw01 ∷ []) (c₂ (Swap) (K ↑))

-- comm push TOFF304 sw0 L: 86 steps
lem-comm-push-TOFF304-sw0-L : WsL → ⟪ (Toff304 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Toff314 ∷ []) ⟫ʷ
lem-comm-push-TOFF304-sw0-L c4 = derive (Toff304 ∷ Sw01 ∷ []) (Sw01 ∷ Toff314 ∷ [])
  (re 0 1 (Sw23 ∷ Toff204 ∷ Sw23 ∷ []) ∷
   re 1 1 (Sw12 ∷ Toff104 ∷ Sw12 ∷ []) ∷
   re 2 1 (Sw34 ∷ Toff103 ∷ Sw34 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 3 (q34 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q2 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 (q34 c4) ∷
   rw⁻ 10 (q27 c4) ∷
   rw 11 (q1 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 3 3 (CS14 ∷ []) ∷
   rw⁻ 4 (q4 c4) ∷
   rw⁻ 7 (q3 c4) ∷
   re 5 3 (CS14⁻ ∷ []) ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   re 7 3 (CS04 ∷ []) ∷
   rw⁻ 8 (q35 c4) ∷
   rw⁻ 9 (q29 c4) ∷
   rw 10 (q3 c4) ∷
   rw⁻ 1 (q40 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   re 3 3 (CX02 ∷ []) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 (q8 c4) ∷
   rw⁻ 7 (q40 c4) ∷
   rw⁻ 8 (q31 c4) ∷
   rw 9 (q6 c4) ∷
   rw⁻ 0 (q53 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (CX03 ∷ []) ∷
   rw⁻ 3 (q10 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CX03 ∷ []) ∷
   rw 5 (q11 c4) ∷
   rw⁻ 6 (q53 c4) ∷
   rw⁻ 7 (q27 c4) ∷
   rw 8 (q1 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   rw⁻ 6 (q63 c4) ∷
   rw 5 (q20 c4) ∷
   rw 4 (q21 c4) ∷
   rw⁻ 3 (q22 c4) ∷
   rw 2 (q21 c4) ∷
   rw⁻ 1 (q23 c4) ∷
   rw⁻ 0 (q63 c4) ∷
   rw⁻ 1 (q1 c4) ∷
   rw⁻ 2 (q57 c4) ∷
   rw⁻ 3 (q16 c4) ∷
   re 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q17 c4) ∷
   re 7 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 7 (q24 c4) ∷
   rw⁻ 8 (q57 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 3 (q42 c4) ∷
   re 5 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q25 c4) ∷
   re 7 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q3 c4) ∷
   rw⁻ 7 (q25 c4) ∷
   re 9 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 8 (q3 c4) ∷
   rw⁻ 9 (q42 c4) ∷
   rw⁻ 10 (q29 c4) ∷
   rw 3 (q43 c4) ∷
   re 3 8 (Toff213 ∷ []) ∷
   re 2 3 (Toff214 ∷ []) ∷
   re 1 3 (Toff314 ∷ []) ∷ []) Eq.refl

private
  q64 : WsL → Eqn
  q64 c4 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wl 47 c4)
  q65 : WsL → Eqn
  q65 c4 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wl 29 c4)
  q66 : WsL → Eqn
  q66 c4 = eqn (CS03 ∷ Sw12 ∷ []) (Sw12 ∷ CS03 ∷ []) (wl 1 c4)
  q67 : WsL → Eqn
  q67 c4 = eqn (CX02 ∷ Sw34 ∷ []) (Sw34 ∷ CX02 ∷ []) (c₃ (Swap ↑ • CX₀₁ • Swap ↑) (Swap))

-- comm push TOFF023 sw3 L: 76 steps
lem-comm-push-TOFF023-sw3-L : WsL → ⟪ (Toff023 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Toff024 ∷ []) ⟫ʷ
lem-comm-push-TOFF023-sw3-L c4 = derive (Toff023 ∷ Sw34 ∷ []) (Sw34 ∷ Toff024 ∷ [])
  (re 0 1 (Sw12 ∷ Toff013 ∷ Sw12 ∷ []) ∷
   re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 (q26 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 (q26 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw 9 (q1 c4) ∷
   rw⁻ 0 (q30 c4) ∷
   rw⁻ 1 (q64 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (CX02 ∷ []) ∷
   rw⁻ 3 (q65 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw⁻ 5 (q66 c4) ∷
   rw⁻ 6 (q30 c4) ∷
   rw⁻ 7 (q31 c4) ∷
   rw 8 (q6 c4) ∷
   rw 7 (q29 c4) ∷
   rw 6 (q28 c4) ∷
   rw⁻ 5 (q3 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw 4 (q67 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   re 4 3 (CS24⁻ ∷ []) ∷
   rw 2 (q67 c4) ∷
   rw⁻ 1 (q3 c4) ∷
   re 2 3 (CS24 ∷ []) ∷
   rw 0 (q28 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw⁻ 3 (q18 c4) ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw 7 (q8 c4) ∷
   rw⁻ 8 (q30 c4) ∷
   rw⁻ 9 (q31 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 3 (q28 c4) ∷
   re 5 1 (Sw34 ∷ CS13 ∷ Sw34 ∷ []) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   re 7 1 (Sw34 ∷ CS13⁻ ∷ Sw34 ∷ []) ∷
   rw 6 (q3 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   re 9 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 8 (q3 c4) ∷
   rw⁻ 9 (q28 c4) ∷
   rw⁻ 10 (q29 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw⁻ 4 (q26 c4) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 (q1 c4) ∷
   rw⁻ 8 (q2 c4) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 (q1 c4) ∷
   rw⁻ 10 (q26 c4) ∷
   rw⁻ 11 (q27 c4) ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 3 3 (Toff013 ∷ []) ∷
   re 2 3 (Toff014 ∷ []) ∷
   re 1 3 (Toff024 ∷ []) ∷ []) Eq.refl

private
  q68 : WsL → Eqn
  q68 c4 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wl 46 c4)
  q69 : WsL → Eqn
  q69 c4 = eqn (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) (wl 28 c4)

-- comm push TOFF024 sw3 L: 76 steps
lem-comm-push-TOFF024-sw3-L : WsL → ⟪ (Toff024 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Sw34 ∷ Toff023 ∷ []) ⟫ʷ
lem-comm-push-TOFF024-sw3-L c4 = derive (Toff024 ∷ Sw34 ∷ []) (Sw34 ∷ Toff023 ∷ [])
  (re 0 1 (Sw12 ∷ Toff014 ∷ Sw12 ∷ []) ∷
   re 1 1 (Sw34 ∷ Toff013 ∷ Sw34 ∷ []) ∷
   re 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 (q26 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 (q2 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 (q26 c4) ∷
   rw⁻ 9 (q27 c4) ∷
   rw 10 (q1 c4) ∷
   rw⁻ 1 (q28 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 2 3 (CS14 ∷ []) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 6 (q3 c4) ∷
   re 4 3 (CS14⁻ ∷ []) ∷
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   re 6 3 (CS04 ∷ []) ∷
   rw⁻ 7 (q28 c4) ∷
   rw⁻ 8 (q29 c4) ∷
   rw 9 (q3 c4) ∷
   rw⁻ 0 (q30 c4) ∷
   rw⁻ 1 (q5 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 2 3 (CX02 ∷ []) ∷
   rw⁻ 3 (q7 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 (q8 c4) ∷
   rw⁻ 6 (q30 c4) ∷
   rw⁻ 7 (q31 c4) ∷
   rw 8 (q6 c4) ∷
   rw 7 (q29 c4) ∷
   rw 6 (q28 c4) ∷
   re 5 1 (Sw34 ∷ CS03 ∷ Sw34 ∷ []) ∷
   rw 7 (q3 c4) ∷
   rw 4 (q67 c4) ∷
   re 3 1 (Sw34 ∷ CS23⁻ ∷ Sw34 ∷ []) ∷
   rw 5 (q3 c4) ∷
   rw 2 (q67 c4) ∷
   re 1 1 (Sw34 ∷ CS23 ∷ Sw34 ∷ []) ∷
   rw 3 (q3 c4) ∷
   rw 0 (q28 c4) ∷
   rw⁻ 1 (q6 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw⁻ 3 (q68 c4) ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q69 c4) ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q66 c4) ∷
   rw⁻ 8 (q30 c4) ∷
   rw⁻ 9 (q31 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 3 (q26 c4) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 (q1 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 (q1 c4) ∷
   rw⁻ 9 (q26 c4) ∷
   rw⁻ 10 (q27 c4) ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 2 3 (Toff013 ∷ []) ∷
   re 1 3 (Toff023 ∷ []) ∷ []) Eq.refl
