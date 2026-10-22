{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D304 (W : Ws) where

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

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 21 W
  q3 : Eqn
  q3 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS)))
  q4 : Eqn
  q4 = wE 51 W
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 211 W
  q7 : Eqn
  q7 = eqn (CK10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((CS • CS • CS)))
  q8 : Eqn
  q8 = wE 696 W
  q9 : Eqn
  q9 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q10 : Eqn
  q10 = wE 200 W
  q11 : Eqn
  q11 = wE 307 W
  q12 : Eqn
  q12 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q13 : Eqn
  q13 = wE 609 W

-- pass [CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX12 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 S2 S2 S2 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 S2 S2 S2 CK20 S2 S2 S2 S2 CK20 S2 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02] [CSd13]: 758 steps
lem-pass-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-S2-S2-S2-CK20-S2-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-vs-CSd13 : ⟪ (CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-S2-S2-S2-CK20-S2-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-vs-CSd13 = derive (CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ [])
  (re 74 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 73 q1 ∷
   re 74 3 (CS03 ∷ []) ∷
   re 74 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 80 q1 ∷
   re 78 3 (CS13⁻ ∷ []) ∷
   rw 77 q2 ∷
   rw 76 q3 ∷
   rw 75 q4 ∷
   re 75 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 74 q5 ∷
   re 75 5 (CS03 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q5 ∷
   re 73 3 (CS13⁻ ∷ []) ∷
   re 73 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 72 q1 ∷
   re 73 3 (CS03 ∷ []) ∷
   re 73 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 79 q1 ∷
   re 77 3 (CS13⁻ ∷ []) ∷
   rw 76 q2 ∷
   rw 75 q3 ∷
   rw 74 q4 ∷
   re 74 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 73 q5 ∷
   re 74 5 (CS03 ∷ []) ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q5 ∷
   re 72 3 (CS13⁻ ∷ []) ∷
   re 72 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 71 q1 ∷
   re 72 3 (CS03 ∷ []) ∷
   re 72 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 78 q1 ∷
   re 76 3 (CS13⁻ ∷ []) ∷
   rw 75 q2 ∷
   rw 74 q3 ∷
   rw 73 q4 ∷
   re 73 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 72 q5 ∷
   re 73 5 (CS03 ∷ []) ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q5 ∷
   re 71 3 (CS13⁻ ∷ []) ∷
   re 71 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 70 q1 ∷
   re 71 3 (CS03 ∷ []) ∷
   re 71 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 77 q1 ∷
   re 75 3 (CS13⁻ ∷ []) ∷
   rw 74 q2 ∷
   rw 73 q3 ∷
   rw 72 q4 ∷
   re 72 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 71 q5 ∷
   re 72 5 (CS03 ∷ []) ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q5 ∷
   re 70 3 (CS13⁻ ∷ []) ∷
   re 70 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 69 q1 ∷
   re 70 3 (CS03 ∷ []) ∷
   re 70 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 76 q1 ∷
   re 74 3 (CS13⁻ ∷ []) ∷
   rw 73 q2 ∷
   rw 72 q3 ∷
   rw 71 q4 ∷
   re 71 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 70 q5 ∷
   re 71 5 (CS03 ∷ []) ∷
   re 71 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 73 q5 ∷
   re 69 3 (CS13⁻ ∷ []) ∷
   re 69 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 68 q1 ∷
   re 69 3 (CS03 ∷ []) ∷
   re 69 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 75 q1 ∷
   re 73 3 (CS13⁻ ∷ []) ∷
   rw 72 q2 ∷
   rw 71 q3 ∷
   rw 70 q4 ∷
   re 70 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 69 q5 ∷
   re 70 5 (CS03 ∷ []) ∷
   re 70 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 72 q5 ∷
   re 68 3 (CS13⁻ ∷ []) ∷
   rw 67 q6 ∷
   re 67 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 66 q1 ∷
   re 67 3 (CK30 ∷ []) ∷
   re 67 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 73 q1 ∷
   re 71 3 (CS13⁻ ∷ []) ∷
   rw 70 q2 ∷
   rw 69 q7 ∷
   rw 68 q4 ∷
   re 68 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 67 q5 ∷
   re 68 5 (CK30 ∷ []) ∷
   re 68 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 70 q5 ∷
   re 66 3 (CS13⁻ ∷ []) ∷
   re 66 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 65 q1 ∷
   re 66 3 (CS03 ∷ []) ∷
   re 66 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 72 q1 ∷
   re 70 3 (CS13⁻ ∷ []) ∷
   rw 69 q2 ∷
   rw 68 q3 ∷
   rw 67 q4 ∷
   re 67 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 66 q5 ∷
   re 67 5 (CS03 ∷ []) ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 69 q5 ∷
   re 65 3 (CS13⁻ ∷ []) ∷
   re 65 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 64 q1 ∷
   re 65 3 (CS03 ∷ []) ∷
   re 65 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 71 q1 ∷
   re 69 3 (CS13⁻ ∷ []) ∷
   rw 68 q2 ∷
   rw 67 q3 ∷
   rw 66 q4 ∷
   re 66 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 65 q5 ∷
   re 66 5 (CS03 ∷ []) ∷
   re 66 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 68 q5 ∷
   re 64 3 (CS13⁻ ∷ []) ∷
   re 64 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 63 q1 ∷
   re 64 3 (CS03 ∷ []) ∷
   re 64 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 70 q1 ∷
   re 68 3 (CS13⁻ ∷ []) ∷
   rw 67 q2 ∷
   rw 66 q3 ∷
   rw 65 q4 ∷
   re 65 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 64 q5 ∷
   re 65 5 (CS03 ∷ []) ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 67 q5 ∷
   re 63 3 (CS13⁻ ∷ []) ∷
   rw 62 q6 ∷
   re 62 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 61 q1 ∷
   re 62 3 (CK30 ∷ []) ∷
   re 62 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 68 q1 ∷
   re 66 3 (CS13⁻ ∷ []) ∷
   rw 65 q2 ∷
   rw 64 q7 ∷
   rw 63 q4 ∷
   re 63 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 62 q5 ∷
   re 63 5 (CK30 ∷ []) ∷
   re 63 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 65 q5 ∷
   re 61 3 (CS13⁻ ∷ []) ∷
   rw 60 q6 ∷
   re 60 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 59 q1 ∷
   re 60 3 (CK30 ∷ []) ∷
   re 60 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 66 q1 ∷
   re 64 3 (CS13⁻ ∷ []) ∷
   rw 63 q2 ∷
   rw 62 q7 ∷
   rw 61 q4 ∷
   re 61 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 60 q5 ∷
   re 61 5 (CK30 ∷ []) ∷
   re 61 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 63 q5 ∷
   re 59 3 (CS13⁻ ∷ []) ∷
   rw 58 q8 ∷
   rw 57 q6 ∷
   re 57 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 56 q1 ∷
   re 57 3 (CK30 ∷ []) ∷
   re 57 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 63 q1 ∷
   re 61 3 (CS13⁻ ∷ []) ∷
   rw 60 q2 ∷
   rw 59 q7 ∷
   rw 58 q4 ∷
   re 58 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 57 q5 ∷
   re 58 5 (CK30 ∷ []) ∷
   re 58 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 60 q5 ∷
   re 56 3 (CS13⁻ ∷ []) ∷
   rw 55 q6 ∷
   rw 54 q6 ∷
   rw 53 q6 ∷
   rw 52 q6 ∷
   re 52 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 51 q1 ∷
   re 52 3 (CK30 ∷ []) ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 58 q1 ∷
   re 56 3 (CS13⁻ ∷ []) ∷
   rw 55 q2 ∷
   rw 54 q7 ∷
   rw 53 q4 ∷
   re 53 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 52 q5 ∷
   re 53 5 (CK30 ∷ []) ∷
   re 53 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 55 q5 ∷
   re 51 3 (CS13⁻ ∷ []) ∷
   rw 50 q6 ∷
   rw 49 q6 ∷
   rw 48 q6 ∷
   re 48 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 47 q1 ∷
   re 48 3 (CS03 ∷ []) ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q1 ∷
   re 52 3 (CS13⁻ ∷ []) ∷
   rw 51 q2 ∷
   rw 50 q3 ∷
   rw 49 q4 ∷
   re 49 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 48 q5 ∷
   re 49 5 (CS03 ∷ []) ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q5 ∷
   re 47 3 (CS13⁻ ∷ []) ∷
   re 47 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 46 q1 ∷
   re 47 3 (CS03 ∷ []) ∷
   re 47 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q1 ∷
   re 51 3 (CS13⁻ ∷ []) ∷
   rw 50 q2 ∷
   rw 49 q3 ∷
   rw 48 q4 ∷
   re 48 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 47 q5 ∷
   re 48 5 (CS03 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q5 ∷
   re 46 3 (CS13⁻ ∷ []) ∷
   re 46 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 45 q1 ∷
   re 46 3 (CS03 ∷ []) ∷
   re 46 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q1 ∷
   re 50 3 (CS13⁻ ∷ []) ∷
   rw 49 q2 ∷
   rw 48 q3 ∷
   rw 47 q4 ∷
   re 47 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 46 q5 ∷
   re 47 5 (CS03 ∷ []) ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 49 q5 ∷
   re 45 3 (CS13⁻ ∷ []) ∷
   re 45 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 44 q1 ∷
   re 45 3 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q1 ∷
   re 49 3 (CS13⁻ ∷ []) ∷
   rw 48 q2 ∷
   rw 47 q3 ∷
   rw 46 q4 ∷
   re 46 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 45 q5 ∷
   re 46 5 (CS03 ∷ []) ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q5 ∷
   re 44 3 (CS13⁻ ∷ []) ∷
   re 44 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 43 q1 ∷
   re 44 3 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q1 ∷
   re 48 3 (CS13⁻ ∷ []) ∷
   rw 47 q2 ∷
   rw 46 q3 ∷
   rw 45 q4 ∷
   re 45 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 44 q5 ∷
   re 45 5 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q5 ∷
   re 43 3 (CS13⁻ ∷ []) ∷
   re 43 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 42 q1 ∷
   re 43 3 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q1 ∷
   re 47 3 (CS13⁻ ∷ []) ∷
   rw 46 q2 ∷
   rw 45 q3 ∷
   rw 44 q4 ∷
   re 44 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 43 q5 ∷
   re 44 5 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q5 ∷
   re 42 3 (CS13⁻ ∷ []) ∷
   re 42 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 41 q1 ∷
   re 42 3 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q1 ∷
   re 46 3 (CS13⁻ ∷ []) ∷
   rw 45 q2 ∷
   rw 44 q3 ∷
   rw 43 q4 ∷
   re 43 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 42 q5 ∷
   re 43 5 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q5 ∷
   re 41 3 (CS13⁻ ∷ []) ∷
   re 41 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 40 q1 ∷
   re 41 3 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q1 ∷
   re 45 3 (CS13⁻ ∷ []) ∷
   rw 44 q2 ∷
   rw 43 q3 ∷
   rw 42 q4 ∷
   re 42 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 41 q5 ∷
   re 42 5 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q5 ∷
   re 40 3 (CS13⁻ ∷ []) ∷
   re 40 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 39 q1 ∷
   re 40 3 (CS03 ∷ []) ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q1 ∷
   re 44 3 (CS13⁻ ∷ []) ∷
   rw 43 q2 ∷
   rw 42 q3 ∷
   rw 41 q4 ∷
   re 41 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 40 q5 ∷
   re 41 5 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 43 q5 ∷
   re 39 3 (CS13⁻ ∷ []) ∷
   rw 38 q6 ∷
   re 38 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 37 q1 ∷
   re 38 3 (CK30 ∷ []) ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q1 ∷
   re 42 3 (CS13⁻ ∷ []) ∷
   rw 41 q2 ∷
   rw 40 q7 ∷
   rw 39 q4 ∷
   re 39 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 38 q5 ∷
   re 39 5 (CK30 ∷ []) ∷
   re 39 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 41 q5 ∷
   re 37 3 (CS13⁻ ∷ []) ∷
   rw 36 q6 ∷
   rw 35 q6 ∷
   rw 34 q6 ∷
   re 34 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   re 34 3 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q1 ∷
   re 38 3 (CS13⁻ ∷ []) ∷
   rw 37 q2 ∷
   rw 36 q3 ∷
   rw 35 q4 ∷
   re 35 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 34 q5 ∷
   re 35 5 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q5 ∷
   re 33 3 (CS13⁻ ∷ []) ∷
   re 33 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   re 33 3 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q1 ∷
   re 37 3 (CS13⁻ ∷ []) ∷
   rw 36 q2 ∷
   rw 35 q3 ∷
   rw 34 q4 ∷
   re 34 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 33 q5 ∷
   re 34 5 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q5 ∷
   re 32 3 (CS13⁻ ∷ []) ∷
   re 32 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   re 32 3 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q1 ∷
   re 36 3 (CS13⁻ ∷ []) ∷
   rw 35 q2 ∷
   rw 34 q3 ∷
   rw 33 q4 ∷
   re 33 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 32 q5 ∷
   re 33 5 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q5 ∷
   re 31 3 (CS13⁻ ∷ []) ∷
   re 31 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 30 q1 ∷
   re 31 3 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q1 ∷
   re 35 3 (CS13⁻ ∷ []) ∷
   rw 34 q2 ∷
   rw 33 q3 ∷
   rw 32 q4 ∷
   re 32 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 31 q5 ∷
   re 32 5 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q5 ∷
   re 30 3 (CS13⁻ ∷ []) ∷
   re 30 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   re 30 3 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q1 ∷
   re 34 3 (CS13⁻ ∷ []) ∷
   rw 33 q2 ∷
   rw 32 q3 ∷
   rw 31 q4 ∷
   re 31 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 30 q5 ∷
   re 31 5 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q5 ∷
   re 29 3 (CS13⁻ ∷ []) ∷
   re 29 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   re 29 3 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q1 ∷
   re 33 3 (CS13⁻ ∷ []) ∷
   rw 32 q2 ∷
   rw 31 q3 ∷
   rw 30 q4 ∷
   re 30 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 29 q5 ∷
   re 30 5 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q5 ∷
   re 28 3 (CS13⁻ ∷ []) ∷
   re 28 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   re 32 3 (CS13⁻ ∷ []) ∷
   rw 31 q2 ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   re 29 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 28 q5 ∷
   re 29 5 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q5 ∷
   re 27 3 (CS13⁻ ∷ []) ∷
   re 27 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   re 27 3 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   re 31 3 (CS13⁻ ∷ []) ∷
   rw 30 q2 ∷
   rw 29 q3 ∷
   rw 28 q4 ∷
   re 28 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 27 q5 ∷
   re 28 5 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q5 ∷
   re 26 3 (CS13⁻ ∷ []) ∷
   re 26 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   re 30 3 (CS13⁻ ∷ []) ∷
   rw 29 q2 ∷
   rw 28 q3 ∷
   rw 27 q4 ∷
   re 27 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 26 q5 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q5 ∷
   re 25 3 (CS13⁻ ∷ []) ∷
   re 25 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   re 29 3 (CS13⁻ ∷ []) ∷
   rw 28 q2 ∷
   rw 27 q3 ∷
   rw 26 q4 ∷
   re 26 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 25 q5 ∷
   re 26 5 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q5 ∷
   re 24 3 (CS13⁻ ∷ []) ∷
   re 24 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 23 q1 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q1 ∷
   re 28 3 (CS13⁻ ∷ []) ∷
   rw 27 q2 ∷
   rw 26 q3 ∷
   rw 25 q4 ∷
   re 25 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 24 q5 ∷
   re 25 5 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q5 ∷
   re 23 3 (CS13⁻ ∷ []) ∷
   re 23 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 22 q1 ∷
   re 23 3 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   re 27 3 (CS13⁻ ∷ []) ∷
   rw 26 q2 ∷
   rw 25 q3 ∷
   rw 24 q4 ∷
   re 24 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 23 q5 ∷
   re 24 5 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q5 ∷
   re 22 3 (CS13⁻ ∷ []) ∷
   re 22 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 21 q1 ∷
   re 22 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   re 26 3 (CS13⁻ ∷ []) ∷
   rw 25 q2 ∷
   rw 24 q3 ∷
   rw 23 q4 ∷
   re 23 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 22 q5 ∷
   re 23 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q5 ∷
   re 21 3 (CS13⁻ ∷ []) ∷
   re 21 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q1 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   re 25 3 (CS13⁻ ∷ []) ∷
   rw 24 q2 ∷
   rw 23 q3 ∷
   rw 22 q4 ∷
   re 22 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 21 q5 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q5 ∷
   re 20 3 (CS13⁻ ∷ []) ∷
   re 20 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q1 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   re 24 3 (CS13⁻ ∷ []) ∷
   rw 23 q2 ∷
   rw 22 q3 ∷
   rw 21 q4 ∷
   re 21 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q5 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q5 ∷
   re 19 3 (CS13⁻ ∷ []) ∷
   re 19 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q1 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   re 23 3 (CS13⁻ ∷ []) ∷
   rw 22 q2 ∷
   rw 21 q3 ∷
   rw 20 q4 ∷
   re 20 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q5 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q5 ∷
   re 18 3 (CS13⁻ ∷ []) ∷
   re 18 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q1 ∷
   re 18 3 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   re 22 3 (CS13⁻ ∷ []) ∷
   rw 21 q2 ∷
   rw 20 q3 ∷
   rw 19 q4 ∷
   re 19 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q5 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q5 ∷
   re 17 3 (CS13⁻ ∷ []) ∷
   re 17 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q1 ∷
   re 17 3 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q1 ∷
   re 21 3 (CS13⁻ ∷ []) ∷
   rw 20 q2 ∷
   rw 19 q3 ∷
   rw 18 q4 ∷
   re 18 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q5 ∷
   re 18 5 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q5 ∷
   re 16 3 (CS13⁻ ∷ []) ∷
   rw 15 q8 ∷
   rw 16 q1 ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q5 ∷
   rw 14 q9 ∷
   rw 15 q10 ∷
   rw 16 q1 ∷
   re 14 3 (CS13⁻ ∷ []) ∷
   rw⁻ 15 q9 ∷
   rw 16 q5 ∷
   rw 15 q1 ∷
   re 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q5 ∷
   rw 13 q9 ∷
   rw 14 q10 ∷
   rw 15 q1 ∷
   re 13 3 (CS13⁻ ∷ []) ∷
   rw⁻ 14 q9 ∷
   rw 15 q5 ∷
   rw 14 q1 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   rw 12 q9 ∷
   rw 13 q10 ∷
   rw 14 q1 ∷
   re 12 3 (CS13⁻ ∷ []) ∷
   rw⁻ 13 q9 ∷
   rw 14 q5 ∷
   rw 13 q1 ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q5 ∷
   rw 11 q9 ∷
   rw 12 q10 ∷
   rw 13 q1 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q9 ∷
   rw 13 q5 ∷
   rw 12 q1 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   rw 10 q9 ∷
   rw 11 q10 ∷
   rw 12 q1 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q9 ∷
   rw 12 q5 ∷
   rw 11 q1 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q5 ∷
   rw 9 q9 ∷
   rw 10 q10 ∷
   rw 11 q1 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q9 ∷
   rw 11 q5 ∷
   rw 8 q11 ∷
   rw 9 q1 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw 7 q12 ∷
   rw 8 q13 ∷
   rw 9 q1 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q12 ∷
   rw 9 q5 ∷
   rw 8 q1 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 6 q9 ∷
   rw 7 q10 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q9 ∷
   rw 8 q5 ∷
   rw 7 q1 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 5 q9 ∷
   rw 6 q10 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q9 ∷
   rw 7 q5 ∷
   rw 6 q1 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 4 q9 ∷
   rw 5 q10 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q9 ∷
   rw 6 q5 ∷
   rw 3 q11 ∷
   rw 4 q1 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 2 q12 ∷
   rw 3 q13 ∷
   rw 4 q1 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q12 ∷
   rw 4 q5 ∷
   rw 1 q11 ∷
   rw 2 q1 ∷
   re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q12 ∷
   rw 1 q13 ∷
   rw 2 q1 ∷
   re 0 3 (CS13⁻ ∷ []) ∷
   rw⁻ 1 q12 ∷
   rw 2 q5 ∷ []) Eq.refl
