{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SR008 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.R008 (Sᴰ : SR008) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (WsL ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

-- The lemmas of other derivation modules (DSig).
private
  lem-comm-push-CS04-sw1-R : WsL → St 2005
  lem-comm-push-CS04-sw1-R = pickᴰ 0 Sᴰ
  lem-comm-push-CS04-sw2-R : WsL → St 2350
  lem-comm-push-CS04-sw2-R = pickᴰ 1 Sᴰ
  lem-comm-push-BOX⟨0·21⟩-sw0-R : WsL → St 2385
  lem-comm-push-BOX⟨0·21⟩-sw0-R = pickᴰ 2 Sᴰ
  lem-comm-push-BOX⟨1·20⟩-sw1-R : WsL → St 2386
  lem-comm-push-BOX⟨1·20⟩-sw1-R = pickᴰ 3 Sᴰ
  lem-comm-push-BOX⟨1·230⟩-sw2-R : WsL → St 2387
  lem-comm-push-BOX⟨1·230⟩-sw2-R = pickᴰ 4 Sᴰ
  lem-comm-push-BOX⟨1·320⟩-sw3-R : WsL → St 2388
  lem-comm-push-BOX⟨1·320⟩-sw3-R = pickᴰ 5 Sᴰ
  lem-comm-push-BOX⟨1·420⟩-sw2-R : WsL → St 2389
  lem-comm-push-BOX⟨1·420⟩-sw2-R = pickᴰ 6 Sᴰ
  lem-comm-push-BOX⟨2·03⟩-sw2-R : WsL → St 2390
  lem-comm-push-BOX⟨2·03⟩-sw2-R = pickᴰ 7 Sᴰ
  lem-comm-push-BOX⟨4·03⟩-sw1-R : WsL → St 2391
  lem-comm-push-BOX⟨4·03⟩-sw1-R = pickᴰ 8 Sᴰ
  lem-comm-push-BOX⟨4·103⟩-sw1-R : WsL → St 2392
  lem-comm-push-BOX⟨4·103⟩-sw1-R = pickᴰ 9 Sᴰ
  lem-comm-push-BOX⟨4·10⟩-sw1-R : WsL → St 2393
  lem-comm-push-BOX⟨4·10⟩-sw1-R = pickᴰ 10 Sᴰ
  lem-comm-push-BOX⟨4·20⟩-sw0-R : WsL → St 2394
  lem-comm-push-BOX⟨4·20⟩-sw0-R = pickᴰ 11 Sᴰ
  lem-comm-push-CS04-sw0-R : WsL → St 2381
  lem-comm-push-CS04-sw0-R = pickᴰ 12 Sᴰ
  lem-comm-push-CS14-sw0-R : WsL → St 2008
  lem-comm-push-CS14-sw0-R = pickᴰ 13 Sᴰ
  lem-comm-push-CSd14-sw0-R : WsL → St 2382
  lem-comm-push-CSd14-sw0-R = pickᴰ 14 Sᴰ
  lem-comm-push-CX04-sw1-R : WsL → St 2383
  lem-comm-push-CX04-sw1-R = pickᴰ 15 Sᴰ
  lem-comm-push-CX04-sw2-R : WsL → St 2384
  lem-comm-push-CX04-sw2-R = pickᴰ 16 Sᴰ

private
  q1 : WsL → Eqn
  q1 c4 = wlE 64 c4
  q2 : WsL → Eqn
  q2 c4 = wlE 3 c4
  q3 : WsL → Eqn
  q3 c4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap))
  q4 : WsL → Eqn
  q4 c4 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (c₁ (iI) (Swap ↑))
  q5 : WsL → Eqn
  q5 c4 = wlE 65 c4
  q6 : WsL → Eqn
  q6 c4 = wlE 4 c4
  q7 : WsL → Eqn
  q7 c4 = eqn (CX01 ∷ Sw34 ∷ []) (Sw34 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Swap ↑))
  q8 : WsL → Eqn
  q8 c4 = eqn (ι ∷ Sw34 ∷ []) (Sw34 ∷ ι ∷ []) (c₁ (iI) (Swap ↑ ↑))
  q9 : WsL → Eqn
  q9 c4 = eqn (Sw23 ∷ K4 ∷ []) (K4 ∷ Sw23 ∷ []) (c₄ (Swap ↑ ↑) (K))
  q10 : WsL → Eqn
  q10 c4 = wlE 17 c4
  q11 : WsL → Eqn
  q11 c4 = wlE 48 c4
  q12 : WsL → Eqn
  q12 c4 = sE 2350 (lem-comm-push-CS04-sw2-R c4)
  q13 : WsL → Eqn
  q13 c4 = wlE 66 c4
  q14 : WsL → Eqn
  q14 c4 = wlE 67 c4

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
  q15 c4 = wlE 5 c4
  q16 : WsL → Eqn
  q16 c4 = wlE 6 c4
  q17 : WsL → Eqn
  q17 c4 = wlE 7 c4
  q18 : WsL → Eqn
  q18 c4 = sE 2005 (lem-comm-push-CS04-sw1-R c4)
  q19 : WsL → Eqn
  q19 c4 = eqn (Sw01 ∷ CS24 ∷ []) (CS24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CS • Swap ↑))
  q20 : WsL → Eqn
  q20 c4 = wlE 117 c4
  q21 : WsL → Eqn
  q21 c4 = eqn (Sw01 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q22 : WsL → Eqn
  q22 c4 = sE 2381 (lem-comm-push-CS04-sw0-R c4)
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
  q28 c4 = wlE 109 c4
  q29 : WsL → Eqn
  q29 c4 = wlE 25 c4
  q30 : WsL → Eqn
  q30 c4 = eqn (K1 ∷ Sw34 ∷ []) (Sw34 ∷ K1 ∷ []) (c₂ (K ↑) (Swap ↑))
  q31 : WsL → Eqn
  q31 c4 = wlE 27 c4

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
  q33 c4 = sE 2008 (lem-comm-push-CS14-sw0-R c4)
  q34 : WsL → Eqn
  q34 c4 = wlE 115 c4
  q35 : WsL → Eqn
  q35 c4 = sE 2382 (lem-comm-push-CSd14-sw0-R c4)
  q36 : WsL → Eqn
  q36 c4 = eqn (CX10 ∷ Sw34 ∷ []) (Sw34 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Swap ↑))
  q37 : WsL → Eqn
  q37 c4 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Swap))
  q38 : WsL → Eqn
  q38 c4 = wlE 124 c4

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
  q39 c4 = wlE 122 c4
  q40 : WsL → Eqn
  q40 c4 = wlE 123 c4
  q41 : WsL → Eqn
  q41 c4 = sE 2392 (lem-comm-push-BOX⟨4·103⟩-sw1-R c4)

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
  q42 c4 = wlE 39 c4
  q43 : WsL → Eqn
  q43 c4 = wlE 13 c4
  q44 : WsL → Eqn
  q44 c4 = wlE 14 c4

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
  q48 c4 = wlE 118 c4
  q49 : WsL → Eqn
  q49 c4 = wlE 73 c4
  q50 : WsL → Eqn
  q50 c4 = wlE 119 c4
  q51 : WsL → Eqn
  q51 c4 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (c₂ (K ↑) (Swap))
  q52 : WsL → Eqn
  q52 c4 = eqn (ι1 ∷ Sw23 ∷ []) (Sw23 ∷ ι1 ∷ []) (c₂ (iI ↑) (Swap))
  q53 : WsL → Eqn
  q53 c4 = wlE 134 c4

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
  q55 c4 = wlE 68 c4

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
  q56 c4 = wlE 135 c4
  q57 : WsL → Eqn
  q57 c4 = wlE 136 c4
  q58 : WsL → Eqn
  q58 c4 = sE 2385 (lem-comm-push-BOX⟨0·21⟩-sw0-R c4)

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
  q59 c4 = wlE 8 c4
  q60 : WsL → Eqn
  q60 c4 = wlE 9 c4
  q61 : WsL → Eqn
  q61 c4 = wlE 26 c4
  q62 : WsL → Eqn
  q62 c4 = eqn (Sw01 ∷ CS34 ∷ []) (CS34 ∷ Sw01 ∷ []) (c₂ (Swap) (CS ↑))
  q63 : WsL → Eqn
  q63 c4 = wlE 16 c4
  q64 : WsL → Eqn
  q64 c4 = eqn (Sw01 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Sw01 ∷ []) (c₂ (Swap) ((CS • CS • CS) ↑))
  q65 : WsL → Eqn
  q65 c4 = wlE 11 c4
  q66 : WsL → Eqn
  q66 c4 = wlE 12 c4
  q67 : WsL → Eqn
  q67 c4 = wlE 125 c4

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
  q68 c4 = wlE 137 c4
  q69 : WsL → Eqn
  q69 c4 = wlE 138 c4
  q70 : WsL → Eqn
  q70 c4 = sE 2386 (lem-comm-push-BOX⟨1·20⟩-sw1-R c4)

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
  q71 c4 = sE 2387 (lem-comm-push-BOX⟨1·230⟩-sw2-R c4)

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
  q72 c4 = wlE 141 c4
  q73 : WsL → Eqn
  q73 c4 = wlE 142 c4
  q74 : WsL → Eqn
  q74 c4 = sE 2388 (lem-comm-push-BOX⟨1·320⟩-sw3-R c4)

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
  q76 c4 = wlE 46 c4
  q77 : WsL → Eqn
  q77 c4 = wlE 28 c4
  q78 : WsL → Eqn
  q78 c4 = wlE 1 c4

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
  q79 c4 = sE 2389 (lem-comm-push-BOX⟨1·420⟩-sw2-R c4)

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
  q80 c4 = wlE 44 c4
  q81 : WsL → Eqn
  q81 c4 = wlE 83 c4
  q82 : WsL → Eqn
  q82 c4 = sE 2393 (lem-comm-push-BOX⟨4·10⟩-sw1-R c4)

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
  q83 c4 = wlE 120 c4

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
  q86 c4 = sE 2394 (lem-comm-push-BOX⟨4·20⟩-sw0-R c4)

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
  q87 c4 = sE 2390 (lem-comm-push-BOX⟨2·03⟩-sw2-R c4)

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
  q88 c4 = wlE 40 c4
  q89 : WsL → Eqn
  q89 c4 = wlE 129 c4
  q90 : WsL → Eqn
  q90 c4 = wlE 128 c4
  q91 : WsL → Eqn
  q91 c4 = sE 2384 (lem-comm-push-CX04-sw2-R c4)
  q92 : WsL → Eqn
  q92 c4 = sE 2383 (lem-comm-push-CX04-sw1-R c4)
  q93 : WsL → Eqn
  q93 c4 = eqn (CS01 ∷ Sw34 ∷ []) (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑))
  q94 : WsL → Eqn
  q94 c4 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (c₂ (CS) (Swap))
  q95 : WsL → Eqn
  q95 c4 = wlE 149 c4

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
  q96 c4 = sE 2391 (lem-comm-push-BOX⟨4·03⟩-sw1-R c4)

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
