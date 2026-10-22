{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD758 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D758 (W : Ws) (Sᴰ : SD758) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

-- The lemmas of other derivation modules (DSig).
private
  lem-CA-CS20-Gad⟨t≡0-W≡⟨1⟩-d≡Sd-e≡1⟩ : St 2864
  lem-CA-CS20-Gad⟨t≡0-W≡⟨1⟩-d≡Sd-e≡1⟩ = pickᴰ 0 Sᴰ
  lem-CA-CSd20-Gad⟨t≡0-W≡⟨1⟩-d≡1-e≡1⟩ : St 2865
  lem-CA-CSd20-Gad⟨t≡0-W≡⟨1⟩-d≡1-e≡1⟩ = pickᴰ 1 Sᴰ
  lem-CA-CS30-Gad⟨t≡0-W≡⟨1⟩-d≡Sd-e≡1⟩ : St 2866
  lem-CA-CS30-Gad⟨t≡0-W≡⟨1⟩-d≡Sd-e≡1⟩ = pickᴰ 2 Sᴰ
  lem-CA-CSd30-Gad⟨t≡0-W≡⟨1⟩-d≡1-e≡1⟩ : St 2867
  lem-CA-CSd30-Gad⟨t≡0-W≡⟨1⟩-d≡1-e≡1⟩ = pickᴰ 3 Sᴰ
  lem-pass-CK10-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : St 2868
  lem-pass-CK10-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = pickᴰ 4 Sᴰ
  lem-merge3 : St 2674
  lem-merge3 = pickᴰ 5 Sᴰ
  lem-pass-CKd10-vs-X1-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X1 : St 2869
  lem-pass-CKd10-vs-X1-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X1 = pickᴰ 6 Sᴰ

private
  q1 : Eqn
  q1 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q2 : Eqn
  q2 = eqn (X1 ∷ Sw12 ∷ []) (Sw12 ∷ X2 ∷ []) (wn 2535 W)
  q3 : Eqn
  q3 = eqn (Sw01 ∷ K1 ∷ []) (K0 ∷ Sw01 ∷ []) (wn 121 W)
  q4 : Eqn
  q4 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q5 : Eqn
  q5 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q6 : Eqn
  q6 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ ι1 ∷ []) (ι ∷ Sw01 ∷ []) (wn 122 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q11 : Eqn
  q11 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q12 : Eqn
  q12 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap))
  q13 : Eqn
  q13 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q14 : Eqn
  q14 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q15 : Eqn
  q15 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q16 : Eqn
  q16 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q17 : Eqn
  q17 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wn 47 W)
  q18 : Eqn
  q18 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wn 48 W)
  q19 : Eqn
  q19 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q20 : Eqn
  q20 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q21 : Eqn
  q21 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q22 : Eqn
  q22 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q23 : Eqn
  q23 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q24 : Eqn
  q24 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 56 W)
  q25 : Eqn
  q25 = eqn (X2 ∷ Sw23 ∷ []) (Sw23 ∷ X3 ∷ []) (wn 1609 W)
  q26 : Eqn
  q26 = eqn (Sw12 ∷ X3 ∷ []) (X3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (X))
  q27 : Eqn
  q27 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q28 : Eqn
  q28 = eqn (CS12⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS12⁻ ∷ []) (wn 15 W)
  q29 : Eqn
  q29 = eqn (CS12 ∷ Sw12 ∷ []) (Sw12 ∷ CS12 ∷ []) (wn 16 W)
  q30 : Eqn
  q30 = eqn (K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 46 W)
  q31 : Eqn
  q31 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) (CS12 ∷ CCZ012 ∷ []) (lem-merge3)
  q32 : Eqn
  q32 = eqn (Sw12 ∷ CS12 ∷ []) (CS12 ∷ Sw12 ∷ []) (wn 18 W)
  q33 : Eqn
  q33 = eqn (Sw12 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Sw12 ∷ []) (wn 19 W)
  q34 : Eqn
  q34 = eqn (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 17 W)
  q35 : Eqn
  q35 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 43 W)
  q36 : Eqn
  q36 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q37 : Eqn
  q37 = eqn (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) (wn 21 W)
  q38 : Eqn
  q38 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q39 : Eqn
  q39 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q40 : Eqn
  q40 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q41 : Eqn
  q41 = eqn (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 26 W)

-- merge3 @0321: 460 steps
lem-merge3-at0321 : ⟪ (Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ X1 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ023 ∷ []) ⟫ʷ
lem-merge3-at0321 = derive (Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ X1 ∷ Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ X1 ∷ []) (CS23 ∷ CCZ023 ∷ [])
  (rw 10 q1 ∷
   rw 9 q2 ∷
   rw 8 q1 ∷
   re 9 3 (CS02⁻ ∷ []) ∷
   re 7 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 8 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 7 q3 ∷
   rw 8 q4 ∷
   rw 9 q5 ∷
   rw 10 q6 ∷
   rw 11 q5 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q7 ∷
   rw 13 q8 ∷
   rw 14 q7 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q3 ∷
   rw 14 q9 ∷
   rw 15 q10 ∷
   rw 14 q11 ∷
   rw 13 q12 ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q13 ∷
   rw 14 q14 ∷
   rw 12 q15 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 11 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 13 q16 ∷
   rw 10 q17 ∷
   re 9 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 11 q16 ∷
   rw 8 q18 ∷
   rw 7 q12 ∷
   rw 8 q19 ∷
   rw⁻ 9 q20 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q21 ∷
   rw⁻ 11 q22 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q21 ∷
   rw⁻ 13 q22 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q21 ∷
   rw⁻ 15 q20 ∷
   rw⁻ 16 q23 ∷
   rw 9 q24 ∷
   re 9 8 (Toff012 ∷ []) ∷
   re 8 3 (Toff013 ∷ []) ∷
   rw 6 q1 ∷
   re 7 3 (CS02 ∷ []) ∷
   re 5 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 6 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 5 q3 ∷
   rw 6 q4 ∷
   rw 7 q5 ∷
   rw 8 q6 ∷
   rw 9 q5 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q7 ∷
   rw 11 q8 ∷
   rw 12 q7 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q3 ∷
   rw 12 q9 ∷
   rw 13 q10 ∷
   rw 12 q11 ∷
   rw 11 q12 ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 13 q13 ∷
   rw 12 q14 ∷
   rw 10 q15 ∷
   re 11 5 (CS03 ∷ []) ∷
   re 9 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 11 q16 ∷
   rw 8 q17 ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 9 q16 ∷
   rw 6 q18 ∷
   rw 5 q12 ∷
   rw 6 q19 ∷
   rw⁻ 7 q20 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q21 ∷
   rw⁻ 9 q22 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q21 ∷
   rw⁻ 11 q22 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q21 ∷
   rw⁻ 13 q20 ∷
   rw⁻ 14 q23 ∷
   rw 7 q24 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 6 3 (Toff013 ∷ []) ∷
   rw 4 q2 ∷
   rw 3 q1 ∷
   re 4 3 (CS02⁻ ∷ []) ∷
   re 2 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 3 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw 8 q8 ∷
   rw 9 q7 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q3 ∷
   rw 9 q9 ∷
   rw 10 q10 ∷
   rw 9 q11 ∷
   rw 8 q12 ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 10 q13 ∷
   rw 9 q14 ∷
   rw 7 q15 ∷
   re 8 5 (CS03 ∷ []) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 8 q16 ∷
   rw 5 q17 ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 q16 ∷
   rw 3 q18 ∷
   rw 2 q12 ∷
   rw 3 q19 ∷
   rw⁻ 4 q20 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q21 ∷
   rw⁻ 6 q22 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q21 ∷
   rw⁻ 8 q22 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q21 ∷
   rw⁻ 10 q20 ∷
   rw⁻ 11 q23 ∷
   rw 4 q24 ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 3 3 (Toff013 ∷ []) ∷
   rw 1 q1 ∷
   re 2 3 (CS02 ∷ []) ∷
   re 0 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 1 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 0 q3 ∷
   rw 1 q4 ∷
   rw 2 q5 ∷
   rw 3 q6 ∷
   rw 4 q5 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw 6 q8 ∷
   rw 7 q7 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q3 ∷
   rw 7 q9 ∷
   rw 8 q10 ∷
   rw 7 q11 ∷
   rw 6 q12 ∷
   re 5 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q13 ∷
   rw 7 q14 ∷
   rw 5 q15 ∷
   re 6 5 (CS03 ∷ []) ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 q16 ∷
   rw 3 q17 ∷
   re 2 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 q16 ∷
   rw 1 q18 ∷
   rw 0 q12 ∷
   rw 1 q19 ∷
   rw⁻ 2 q20 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q21 ∷
   rw⁻ 4 q22 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q21 ∷
   rw⁻ 6 q22 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q21 ∷
   rw⁻ 8 q20 ∷
   rw⁻ 9 q23 ∷
   rw 2 q24 ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   rw 11 q19 ∷
   rw 10 q25 ∷
   rw 9 q19 ∷
   re 10 3 (CS03⁻ ∷ []) ∷
   re 8 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 8 q20 ∷
   rw 11 q19 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 10 q22 ∷
   rw 13 q19 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q22 ∷
   rw 15 q19 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw⁻ 14 q20 ∷
   rw⁻ 15 q23 ∷
   rw 16 q21 ∷
   rw 15 q23 ∷
   rw 14 q20 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q21 ∷
   rw 12 q22 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q21 ∷
   rw 10 q22 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q21 ∷
   rw 8 q20 ∷
   rw 9 q24 ∷
   re 9 8 (Toff012 ∷ []) ∷
   rw 7 q19 ∷
   re 8 3 (CS03 ∷ []) ∷
   re 6 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 6 q20 ∷
   rw 9 q19 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q22 ∷
   rw 11 q19 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q22 ∷
   rw 13 q19 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q20 ∷
   rw⁻ 13 q23 ∷
   rw 14 q21 ∷
   rw 13 q23 ∷
   rw 12 q20 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q21 ∷
   rw 10 q22 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q21 ∷
   rw 8 q22 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q21 ∷
   rw 6 q20 ∷
   rw 7 q24 ∷
   re 7 8 (Toff012 ∷ []) ∷
   rw 5 q25 ∷
   rw 4 q19 ∷
   re 5 3 (CS03⁻ ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q20 ∷
   rw 6 q19 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q22 ∷
   rw 8 q19 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q22 ∷
   rw 10 q19 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q20 ∷
   rw⁻ 10 q23 ∷
   rw 11 q21 ∷
   rw 10 q23 ∷
   rw 9 q20 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q21 ∷
   rw 7 q22 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q21 ∷
   rw 5 q22 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q21 ∷
   rw 3 q20 ∷
   rw 4 q24 ∷
   re 4 8 (Toff012 ∷ []) ∷
   rw 2 q19 ∷
   re 3 3 (CS03 ∷ []) ∷
   re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q20 ∷
   rw 4 q19 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q22 ∷
   rw 6 q19 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q22 ∷
   rw 8 q19 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q20 ∷
   rw⁻ 8 q23 ∷
   rw 9 q21 ∷
   rw 8 q23 ∷
   rw 7 q20 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q21 ∷
   rw 5 q22 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q21 ∷
   rw 3 q22 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q21 ∷
   rw 1 q20 ∷
   rw 2 q24 ∷
   re 2 8 (Toff012 ∷ []) ∷
   rw 12 q1 ∷
   rw⁻ 11 q26 ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 13 q13 ∷
   rw 12 q27 ∷
   rw 10 q15 ∷
   re 11 5 (CS03⁻ ∷ []) ∷
   re 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 16 q11 ∷
   rw 15 q12 ∷
   re 14 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 16 q16 ∷
   rw 13 q1 ∷
   re 14 3 (CX02 ∷ []) ∷
   rw 12 q28 ∷
   rw 11 q1 ∷
   re 12 3 (CX02 ∷ []) ∷
   rw 10 q29 ∷
   rw 9 q12 ∷
   rw 10 q30 ∷
   re 10 8 (Toff012 ∷ []) ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 11 q13 ∷
   rw 10 q14 ∷
   rw 8 q15 ∷
   re 9 5 (CS03 ∷ []) ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 14 q11 ∷
   rw 13 q12 ∷
   re 12 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 14 q16 ∷
   rw 11 q1 ∷
   re 12 3 (CX02 ∷ []) ∷
   rw 10 q28 ∷
   rw 9 q1 ∷
   re 10 3 (CX02 ∷ []) ∷
   rw 8 q29 ∷
   rw 7 q12 ∷
   rw 8 q30 ∷
   re 8 8 (Toff012 ∷ []) ∷
   rw⁻ 6 q26 ∷
   re 5 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q13 ∷
   rw 7 q27 ∷
   rw 5 q15 ∷
   re 6 5 (CS03⁻ ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 11 q11 ∷
   rw 10 q12 ∷
   re 9 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 11 q16 ∷
   rw 8 q1 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 7 q28 ∷
   rw 6 q1 ∷
   re 7 3 (CX02 ∷ []) ∷
   rw 5 q29 ∷
   rw 4 q12 ∷
   rw 5 q30 ∷
   re 5 8 (Toff012 ∷ []) ∷
   re 3 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 6 q13 ∷
   rw 5 q14 ∷
   rw 3 q15 ∷
   re 4 5 (CS03 ∷ []) ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 9 q11 ∷
   rw 8 q12 ∷
   re 7 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 9 q16 ∷
   rw 6 q1 ∷
   re 7 3 (CX02 ∷ []) ∷
   rw 5 q28 ∷
   rw 4 q1 ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 3 q29 ∷
   rw 2 q12 ∷
   rw 3 q30 ∷
   re 3 8 (Toff012 ∷ []) ∷
   rw 3 q31 ∷
   rw 2 q32 ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q32 ∷
   rw 6 q1 ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 q33 ∷
   rw 8 q1 ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 7 q16 ∷
   rw 3 q34 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   rw 4 q16 ∷
   rw 3 q19 ∷
   re 1 3 (CS13 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q19 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q22 ∷
   rw 6 q19 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q22 ∷
   rw 8 q19 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 2 q19 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q21 ∷
   rw⁻ 4 q22 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q21 ∷
   rw⁻ 6 q22 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q21 ∷
   rw 3 q35 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   re 2 3 (CCZ013 ∷ []) ∷
   rw 3 q21 ∷
   rw 0 q36 ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q19 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q22 ∷
   rw 6 q19 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q22 ∷
   rw 8 q19 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q21 ∷
   rw 1 q36 ∷
   rw 4 q1 ∷
   re 2 3 (CX02 ∷ []) ∷
   rw 3 q37 ∷
   rw 6 q1 ∷
   re 4 3 (CX02 ∷ []) ∷
   re 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 5 q13 ∷
   rw⁻ 7 q14 ∷
   rw 8 q15 ∷
   re 5 5 (CS03 ∷ []) ∷
   rw 1 q38 ∷
   rw 2 q4 ∷
   rw 3 q39 ∷
   rw 4 q6 ∷
   rw 5 q39 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 7 q40 ∷
   rw 8 q7 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 2 q41 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   re 1 3 (CCZ023 ∷ []) ∷
   rw 2 q16 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q43 : Eqn
  q43 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q44 : Eqn
  q44 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (CK10 ∷ CS02 ∷ CK10⁻ ∷ CS02⁻ ∷ []) (wn 1416 W)
  q45 : Eqn
  q45 = eqn (CK10⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap))
  q46 : Eqn
  q46 = eqn (CS03⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X1 ∷ CS03⁻ ∷ []) (lem-CA-CSd30-Gad⟨t≡0-W≡⟨1⟩-d≡1-e≡1⟩)
  q47 : Eqn
  q47 = eqn (CK10⁻ ∷ X1 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X1 ∷ []) (X1 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X1 ∷ CK10⁻ ∷ []) (lem-pass-CKd10-vs-X1-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X1)
  q48 : Eqn
  q48 = eqn (CS03 ∷ X1 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X1 ∷ []) (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS03 ∷ []) (lem-CA-CS30-Gad⟨t≡0-W≡⟨1⟩-d≡Sd-e≡1⟩)
  q49 : Eqn
  q49 = eqn (CK10 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK10 ∷ []) (lem-pass-CK10-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1)
  q50 : Eqn
  q50 = eqn (CK10 ∷ CS02 ∷ CK10⁻ ∷ CS02⁻ ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (wn 1417 W)
  q51 : Eqn
  q51 = eqn (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) (wn 151 W)

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [X1 TOFF012 CS03 TOFF012 CSd03 X1]: 120 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 29 q19 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 30 q21 ∷
   re 27 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 29 q21 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q21 ∷
   re 25 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 27 q21 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q21 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q21 ∷
   re 22 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 24 q21 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q21 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q21 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q21 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q21 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q21 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q21 ∷
   rw 15 q42 ∷
   re 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 16 q21 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q21 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q21 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q21 ∷
   rw 10 q42 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 11 q21 ∷
   rw 8 q42 ∷
   re 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 9 q21 ∷
   re 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 8 q21 ∷
   rw 5 q43 ∷
   rw 4 q43 ∷
   rw 3 q14 ∷
   rw 2 q43 ∷
   rw 1 q14 ∷
   rw 0 q14 ∷
   rw 1 q44 ∷
   rw⁻ 0 q43 ∷
   rw 3 q19 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw⁻ 2 q45 ∷
   rw 5 q19 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 4 q21 ∷
   rw 3 q46 ∷
   rw 2 q47 ∷
   rw 1 q48 ∷
   rw 0 q49 ∷
   rw 10 q19 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q21 ∷
   rw 8 q45 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q21 ∷
   rw 6 q43 ∷
   rw 7 q50 ∷
   rw⁻ 6 q14 ∷
   rw⁻ 7 q14 ∷
   rw⁻ 8 q43 ∷
   rw⁻ 9 q14 ∷
   rw⁻ 10 q43 ∷
   rw⁻ 11 q43 ∷
   rw 14 q19 ∷
   re 12 3 (CX13 ∷ []) ∷
   rw 15 q19 ∷
   re 13 3 (CK30 ∷ []) ∷
   rw 14 q51 ∷
   rw 17 q19 ∷
   re 15 3 (CK30 ∷ []) ∷
   rw 16 q51 ∷
   rw 19 q19 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 20 q19 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 21 q19 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 22 q19 ∷
   re 20 3 (CK30 ∷ []) ∷
   rw 21 q51 ∷
   rw 24 q19 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 25 q19 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 26 q19 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 27 q19 ∷
   re 25 3 (CS03 ∷ []) ∷
   rw 28 q19 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 29 q19 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 30 q19 ∷
   re 28 3 (CX13 ∷ []) ∷
   rw 31 q19 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 32 q19 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 33 q19 ∷
   re 31 3 (CK30 ∷ []) ∷
   rw 34 q19 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 35 q19 ∷
   re 33 3 (CK30 ∷ []) ∷
   rw 36 q19 ∷
   re 34 3 (CK30 ∷ []) ∷
   rw 35 q21 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = eqn (CS02⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X1 ∷ CS02⁻ ∷ []) (lem-CA-CSd20-Gad⟨t≡0-W≡⟨1⟩-d≡1-e≡1⟩)
  q53 : Eqn
  q53 = eqn (CS02 ∷ X1 ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ X1 ∷ []) (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS02 ∷ []) (lem-CA-CS20-Gad⟨t≡0-W≡⟨1⟩-d≡Sd-e≡1⟩)

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20] [X1 TOFF012 CS03 TOFF012 CSd03 X1]: 6 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 0 q44 ∷
   rw 3 q52 ∷
   rw 2 q47 ∷
   rw 1 q53 ∷
   rw 0 q49 ∷
   rw 6 q50 ∷ []) Eq.refl

-- L87 merge-p 0123 3: 1 steps
lem-L87-merge-p-0123-3 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ012 ∷ []) ⟫ʷ
lem-L87-merge-p-0123-3 = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) (CS12 ∷ CCZ012 ∷ [])
  (rw 0 q31 ∷ []) Eq.refl
