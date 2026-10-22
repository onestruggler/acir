{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD691 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D691 (W : Ws) (Sᴰ : SD691) where

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
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~30-⟶2⟩ : St 1833
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~30-⟶2⟩ = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = wE 772 W
  q4 : Eqn
  q4 = wE 7 W
  q5 : Eqn
  q5 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q6 : Eqn
  q6 = wE 6 W
  q7 : Eqn
  q7 = wE 481 W
  q8 : Eqn
  q8 = eqn (Sw01 ∷ CK32 ∷ []) (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀))
  q9 : Eqn
  q9 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q10 : Eqn
  q10 = wE 2024 W
  q11 : Eqn
  q11 = wE 121 W
  q12 : Eqn
  q12 = wE 30 W
  q13 : Eqn
  q13 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q14 : Eqn
  q14 = wE 27 W
  q15 : Eqn
  q15 = wE 122 W
  q16 : Eqn
  q16 = wE 123 W
  q17 : Eqn
  q17 = wE 24 W
  q18 : Eqn
  q18 = wE 25 W
  q19 : Eqn
  q19 = wE 124 W
  q20 : Eqn
  q20 = wE 125 W
  q21 : Eqn
  q21 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K))
  q22 : Eqn
  q22 = wE 334 W
  q23 : Eqn
  q23 = wE 142 W
  q24 : Eqn
  q24 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q25 : Eqn
  q25 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q26 : Eqn
  q26 = wE 31 W
  q27 : Eqn
  q27 = sE 1833 lem-Bar⟨SSSKSS31-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~30-⟶2⟩
  q28 : Eqn
  q28 = wE 127 W
  q29 : Eqn
  q29 = wE 118 W
  q30 : Eqn
  q30 = wE 74 W
  q31 : Eqn
  q31 = wE 140 W
  q32 : Eqn
  q32 = wE 2025 W
  q33 : Eqn
  q33 = wE 39 W
  q34 : Eqn
  q34 = wE 329 W
  q35 : Eqn
  q35 = wE 315 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X3 CS23 CS23 CK32 CS23 CK32 CK32 CX30 CK02 S0 CK02 S0 CS02 CS02 CS02 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 CX30 CS02 CS02 CK02 CS02 CK02 CK02 X3]: 567 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X3 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X3 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw 62 q1 ∷
   rw⁻ 61 q2 ∷
   rw 60 q3 ∷
   rw 59 q3 ∷
   rw 58 q4 ∷
   rw 57 q3 ∷
   rw 56 q4 ∷
   rw 55 q4 ∷
   re 54 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 56 q5 ∷
   rw 55 q6 ∷
   rw⁻ 54 q5 ∷
   re 55 3 (CX31 ∷ []) ∷
   rw 53 q4 ∷
   rw 52 q4 ∷
   rw 51 q4 ∷
   rw 50 q4 ∷
   rw 49 q4 ∷
   rw 48 q4 ∷
   rw 47 q7 ∷
   rw 46 q3 ∷
   rw 45 q4 ∷
   rw 44 q4 ∷
   rw 43 q4 ∷
   rw 42 q7 ∷
   rw 41 q3 ∷
   rw 40 q7 ∷
   rw 39 q3 ∷
   re 38 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q5 ∷
   rw 39 q6 ∷
   rw⁻ 38 q5 ∷
   re 39 3 (CX31 ∷ []) ∷
   rw⁻ 37 q8 ∷
   rw⁻ 36 q8 ∷
   rw⁻ 35 q9 ∷
   rw⁻ 34 q8 ∷
   rw⁻ 33 q9 ∷
   rw⁻ 32 q9 ∷
   rw⁻ 31 q2 ∷
   rw 32 q10 ∷
   rw 31 q2 ∷
   re 33 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 32 q11 ∷
   rw 33 q9 ∷
   rw 34 q12 ∷
   rw 35 q13 ∷
   rw 36 q12 ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q5 ∷
   rw 38 q14 ∷
   rw 39 q5 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 38 q11 ∷
   rw 39 q15 ∷
   rw 32 q1 ∷
   rw 33 q16 ∷
   rw 34 q9 ∷
   rw 35 q17 ∷
   rw 36 q13 ∷
   rw 37 q17 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q5 ∷
   rw 39 q18 ∷
   rw 40 q5 ∷
   re 38 3 (CS13 ∷ []) ∷
   rw 39 q16 ∷
   rw 40 q19 ∷
   rw 33 q20 ∷
   re 33 8 (Toff123 ∷ []) ∷
   re 32 3 (Toff023 ∷ []) ∷
   rw 33 q2 ∷
   rw 34 q2 ∷
   re 36 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 35 q21 ∷
   rw 36 q9 ∷
   rw 37 q12 ∷
   rw 38 q13 ∷
   rw 39 q12 ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q5 ∷
   rw 41 q14 ∷
   rw 42 q5 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 41 q21 ∷
   rw 42 q15 ∷
   rw 35 q1 ∷
   rw 36 q21 ∷
   rw 37 q9 ∷
   rw 38 q17 ∷
   rw 39 q13 ∷
   rw 40 q17 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q5 ∷
   rw 42 q18 ∷
   rw 43 q5 ∷
   re 41 3 (CS13 ∷ []) ∷
   rw 42 q21 ∷
   rw 43 q19 ∷
   rw 36 q22 ∷
   re 36 8 (Toff213 ∷ []) ∷
   re 35 3 (Toff203 ∷ []) ∷
   rw 36 q2 ∷
   rw 37 q2 ∷
   re 39 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 38 q11 ∷
   rw 39 q9 ∷
   rw 40 q12 ∷
   rw 41 q13 ∷
   rw 42 q12 ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q5 ∷
   rw 44 q14 ∷
   rw 45 q5 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw 44 q11 ∷
   rw 45 q15 ∷
   rw 38 q1 ∷
   rw 39 q16 ∷
   rw 40 q9 ∷
   rw 41 q17 ∷
   rw 42 q13 ∷
   rw 43 q17 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q5 ∷
   rw 45 q18 ∷
   rw 46 q5 ∷
   re 44 3 (CS13 ∷ []) ∷
   rw 45 q16 ∷
   rw 46 q19 ∷
   rw 39 q20 ∷
   re 39 8 (Toff123 ∷ []) ∷
   re 38 3 (Toff023 ∷ []) ∷
   rw 39 q2 ∷
   rw 40 q2 ∷
   re 42 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 41 q5 ∷
   rw 42 q14 ∷
   rw 43 q5 ∷
   re 41 3 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 42 q5 ∷
   rw 43 q14 ∷
   rw 44 q5 ∷
   re 42 3 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 43 q5 ∷
   rw 44 q23 ∷
   rw 45 q5 ∷
   re 43 3 (CK30 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 44 q5 ∷
   rw 45 q14 ∷
   rw 46 q5 ∷
   re 44 3 (CS03 ∷ []) ∷
   re 46 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 45 q5 ∷
   rw 46 q23 ∷
   rw 47 q5 ∷
   re 45 3 (CK30 ∷ []) ∷
   re 47 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 46 q5 ∷
   rw 47 q23 ∷
   rw 48 q5 ∷
   re 46 3 (CK30 ∷ []) ∷
   rw 47 q24 ∷
   rw 48 q23 ∷
   rw 49 q25 ∷
   rw 50 q23 ∷
   rw 51 q25 ∷
   rw 52 q14 ∷
   rw 53 q14 ∷
   rw 54 q14 ∷
   rw 55 q23 ∷
   rw 56 q25 ∷
   rw 57 q14 ∷
   rw 58 q14 ∷
   rw 59 q14 ∷
   rw 60 q14 ∷
   rw 61 q14 ∷
   rw 62 q14 ∷
   rw 63 q24 ∷
   rw 64 q14 ∷
   rw 65 q14 ∷
   rw 66 q23 ∷
   rw 67 q14 ∷
   rw 68 q23 ∷
   rw 69 q23 ∷
   rw 70 q2 ∷
   rw 71 q2 ∷
   re 73 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 72 q11 ∷
   rw 73 q9 ∷
   rw 74 q12 ∷
   rw 75 q13 ∷
   rw 76 q12 ∷
   re 78 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 77 q5 ∷
   rw 78 q14 ∷
   rw 79 q5 ∷
   re 77 3 (CS03 ∷ []) ∷
   rw 78 q11 ∷
   rw 79 q15 ∷
   rw 72 q1 ∷
   rw 73 q16 ∷
   rw 74 q9 ∷
   rw 75 q17 ∷
   rw 76 q13 ∷
   rw 77 q17 ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 78 q5 ∷
   rw 79 q18 ∷
   rw 80 q5 ∷
   re 78 3 (CS13 ∷ []) ∷
   rw 79 q16 ∷
   rw 80 q19 ∷
   rw 73 q20 ∷
   re 73 8 (Toff123 ∷ []) ∷
   re 72 3 (Toff023 ∷ []) ∷
   rw 73 q2 ∷
   rw 74 q2 ∷
   re 76 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 75 q21 ∷
   rw 76 q9 ∷
   rw 77 q12 ∷
   rw 78 q13 ∷
   rw 79 q12 ∷
   re 81 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 80 q5 ∷
   rw 81 q14 ∷
   rw 82 q5 ∷
   re 80 3 (CS03 ∷ []) ∷
   rw 81 q21 ∷
   rw 82 q15 ∷
   rw 75 q1 ∷
   rw 76 q21 ∷
   rw 77 q9 ∷
   rw 78 q17 ∷
   rw 79 q13 ∷
   rw 80 q17 ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 81 q5 ∷
   rw 82 q18 ∷
   rw 83 q5 ∷
   re 81 3 (CS13 ∷ []) ∷
   rw 82 q21 ∷
   rw 83 q19 ∷
   rw 76 q22 ∷
   re 76 8 (Toff213 ∷ []) ∷
   re 75 3 (Toff203 ∷ []) ∷
   rw 76 q2 ∷
   rw 77 q2 ∷
   re 79 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 78 q11 ∷
   rw 79 q9 ∷
   rw 80 q12 ∷
   rw 81 q13 ∷
   rw 82 q12 ∷
   re 84 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 83 q5 ∷
   rw 84 q14 ∷
   rw 85 q5 ∷
   re 83 3 (CS03 ∷ []) ∷
   rw 84 q11 ∷
   rw 85 q15 ∷
   rw 78 q1 ∷
   rw 79 q16 ∷
   rw 80 q9 ∷
   rw 81 q17 ∷
   rw 82 q13 ∷
   rw 83 q17 ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 84 q5 ∷
   rw 85 q18 ∷
   rw 86 q5 ∷
   re 84 3 (CS13 ∷ []) ∷
   rw 85 q16 ∷
   rw 86 q19 ∷
   rw 79 q20 ∷
   re 79 8 (Toff123 ∷ []) ∷
   re 78 3 (Toff023 ∷ []) ∷
   rw 79 q2 ∷
   rw 80 q26 ∷
   rw 0 q27 ∷
   rw 49 q1 ∷
   rw⁻ 48 q2 ∷
   re 47 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 48 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 47 q11 ∷
   rw 48 q9 ∷
   rw 49 q12 ∷
   rw 50 q13 ∷
   rw 51 q12 ∷
   re 53 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 52 q5 ∷
   rw 53 q14 ∷
   rw 54 q5 ∷
   re 52 3 (CS03 ∷ []) ∷
   rw 53 q11 ∷
   rw 54 q15 ∷
   rw 55 q26 ∷
   rw 54 q28 ∷
   rw 53 q29 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 54 q5 ∷
   rw 53 q4 ∷
   rw⁻ 52 q5 ∷
   re 53 3 (CS13 ∷ []) ∷
   rw 51 q30 ∷
   rw⁻ 50 q13 ∷
   rw 49 q30 ∷
   rw⁻ 48 q9 ∷
   rw 47 q29 ∷
   rw 48 q20 ∷
   re 48 8 (Toff123 ∷ []) ∷
   rw⁻ 46 q2 ∷
   rw⁻ 45 q2 ∷
   re 44 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 45 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 44 q21 ∷
   rw 45 q9 ∷
   rw 46 q12 ∷
   rw 47 q13 ∷
   rw 48 q12 ∷
   re 50 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 49 q5 ∷
   rw 50 q14 ∷
   rw 51 q5 ∷
   re 49 3 (CS03 ∷ []) ∷
   rw 50 q21 ∷
   rw 51 q15 ∷
   rw 52 q26 ∷
   rw 51 q28 ∷
   rw⁻ 50 q21 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 51 q5 ∷
   rw 50 q4 ∷
   rw⁻ 49 q5 ∷
   re 50 3 (CS13 ∷ []) ∷
   rw 48 q30 ∷
   rw⁻ 47 q13 ∷
   rw 46 q30 ∷
   rw⁻ 45 q9 ∷
   rw⁻ 44 q21 ∷
   rw 45 q22 ∷
   re 45 8 (Toff213 ∷ []) ∷
   rw⁻ 43 q2 ∷
   rw⁻ 42 q2 ∷
   re 41 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 42 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 41 q11 ∷
   rw 42 q9 ∷
   rw 43 q12 ∷
   rw 44 q13 ∷
   rw 45 q12 ∷
   re 47 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 46 q5 ∷
   rw 47 q14 ∷
   rw 48 q5 ∷
   re 46 3 (CS03 ∷ []) ∷
   rw 47 q11 ∷
   rw 48 q15 ∷
   rw 49 q26 ∷
   rw 48 q28 ∷
   rw 47 q29 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q5 ∷
   rw 47 q4 ∷
   rw⁻ 46 q5 ∷
   re 47 3 (CS13 ∷ []) ∷
   rw 45 q30 ∷
   rw⁻ 44 q13 ∷
   rw 43 q30 ∷
   rw⁻ 42 q9 ∷
   rw 41 q29 ∷
   rw 42 q20 ∷
   re 42 8 (Toff123 ∷ []) ∷
   rw⁻ 40 q2 ∷
   rw⁻ 39 q2 ∷
   rw 38 q31 ∷
   rw 37 q31 ∷
   rw 36 q4 ∷
   rw 35 q31 ∷
   rw 34 q4 ∷
   rw 33 q4 ∷
   rw⁻ 32 q24 ∷
   rw 31 q4 ∷
   rw 30 q4 ∷
   rw 29 q4 ∷
   rw 28 q4 ∷
   rw 27 q4 ∷
   rw 26 q4 ∷
   rw⁻ 25 q25 ∷
   rw 24 q31 ∷
   rw 23 q4 ∷
   rw 22 q4 ∷
   rw 21 q4 ∷
   rw⁻ 20 q25 ∷
   rw 19 q31 ∷
   rw⁻ 18 q25 ∷
   rw 17 q31 ∷
   rw⁻ 16 q24 ∷
   re 15 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q5 ∷
   rw 16 q31 ∷
   rw⁻ 15 q5 ∷
   re 16 3 (CK31 ∷ []) ∷
   re 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q5 ∷
   rw 15 q31 ∷
   rw⁻ 14 q5 ∷
   re 15 3 (CK31 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q5 ∷
   rw 14 q4 ∷
   rw⁻ 13 q5 ∷
   re 14 3 (CS13 ∷ []) ∷
   re 12 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q5 ∷
   rw 13 q31 ∷
   rw⁻ 12 q5 ∷
   re 13 3 (CK31 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q5 ∷
   rw 12 q4 ∷
   rw⁻ 11 q5 ∷
   re 12 3 (CS13 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q5 ∷
   rw 11 q4 ∷
   rw⁻ 10 q5 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw⁻ 9 q2 ∷
   rw⁻ 8 q2 ∷
   re 7 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 8 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 7 q11 ∷
   rw 8 q9 ∷
   rw 9 q12 ∷
   rw 10 q13 ∷
   rw 11 q12 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q5 ∷
   rw 13 q14 ∷
   rw 14 q5 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q11 ∷
   rw 14 q15 ∷
   rw 15 q26 ∷
   rw 14 q28 ∷
   rw 13 q29 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q5 ∷
   rw 13 q4 ∷
   rw⁻ 12 q5 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 11 q30 ∷
   rw⁻ 10 q13 ∷
   rw 9 q30 ∷
   rw⁻ 8 q9 ∷
   rw 7 q29 ∷
   rw 8 q20 ∷
   re 8 8 (Toff123 ∷ []) ∷
   rw⁻ 6 q2 ∷
   rw⁻ 5 q2 ∷
   re 4 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 5 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 4 q21 ∷
   rw 5 q9 ∷
   rw 6 q12 ∷
   rw 7 q13 ∷
   rw 8 q12 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 10 q14 ∷
   rw 11 q5 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q21 ∷
   rw 11 q15 ∷
   rw 12 q26 ∷
   rw 11 q28 ∷
   rw⁻ 10 q21 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q5 ∷
   rw 10 q4 ∷
   rw⁻ 9 q5 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 8 q30 ∷
   rw⁻ 7 q13 ∷
   rw 6 q30 ∷
   rw⁻ 5 q9 ∷
   rw⁻ 4 q21 ∷
   rw 5 q22 ∷
   re 5 8 (Toff213 ∷ []) ∷
   rw⁻ 3 q2 ∷
   rw⁻ 2 q2 ∷
   re 1 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 1 q11 ∷
   rw 2 q9 ∷
   rw 3 q12 ∷
   rw 4 q13 ∷
   rw 5 q12 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 7 q14 ∷
   rw 8 q5 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q11 ∷
   rw 8 q15 ∷
   rw 9 q26 ∷
   rw 8 q28 ∷
   rw 7 q29 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q5 ∷
   rw 7 q4 ∷
   rw⁻ 6 q5 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 5 q30 ∷
   rw⁻ 4 q13 ∷
   rw 3 q30 ∷
   rw⁻ 2 q9 ∷
   rw 1 q29 ∷
   rw 2 q20 ∷
   re 2 8 (Toff123 ∷ []) ∷
   rw⁻ 0 q2 ∷
   rw 1 q32 ∷
   rw 0 q2 ∷
   rw 1 q9 ∷
   rw 2 q9 ∷
   rw 3 q8 ∷
   rw 4 q9 ∷
   rw 5 q8 ∷
   rw 6 q8 ∷
   re 8 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 8 q33 ∷
   rw 9 q5 ∷
   re 7 3 (CX30 ∷ []) ∷
   rw 8 q34 ∷
   rw 9 q35 ∷
   rw 10 q34 ∷
   rw 11 q35 ∷
   rw 12 q14 ∷
   rw 13 q14 ∷
   rw 14 q14 ∷
   rw 15 q34 ∷
   rw 16 q35 ∷
   rw 17 q14 ∷
   rw 18 q14 ∷
   rw 19 q14 ∷
   rw 20 q14 ∷
   rw 21 q14 ∷
   rw 22 q14 ∷
   re 24 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 23 q5 ∷
   rw 24 q33 ∷
   rw 25 q5 ∷
   re 23 3 (CX30 ∷ []) ∷
   rw 24 q14 ∷
   rw 25 q14 ∷
   rw 26 q34 ∷
   rw 27 q14 ∷
   rw 28 q34 ∷
   rw 29 q34 ∷
   rw 30 q2 ∷
   rw 31 q26 ∷ []) Eq.refl
