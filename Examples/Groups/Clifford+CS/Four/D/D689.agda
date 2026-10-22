{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD689 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D689 (W : Ws) (Sᴰ : SD689) where

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
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~30-⟶2⟩ : St 1831
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~30-⟶2⟩ = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = eqn (CK02 ∷ Sw01 ∷ []) (Sw01 ∷ CK12 ∷ []) (wn 772 W)
  q4 : Eqn
  q4 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q5 : Eqn
  q5 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q6 : Eqn
  q6 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q7 : Eqn
  q7 = eqn (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) (wn 481 W)
  q8 : Eqn
  q8 = eqn (Sw01 ∷ CK32 ∷ []) (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀))
  q9 : Eqn
  q9 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q10 : Eqn
  q10 = eqn (X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X3 ∷ []) (X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) (wn 2024 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ K1 ∷ []) (K0 ∷ Sw01 ∷ []) (wn 121 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q13 : Eqn
  q13 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q14 : Eqn
  q14 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q15 : Eqn
  q15 = eqn (Sw01 ∷ ι1 ∷ []) (ι ∷ Sw01 ∷ []) (wn 122 W)
  q16 : Eqn
  q16 = eqn (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) (wn 123 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q18 : Eqn
  q18 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q19 : Eqn
  q19 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)
  q20 : Eqn
  q20 = eqn (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wn 125 W)
  q21 : Eqn
  q21 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K))
  q22 : Eqn
  q22 = eqn (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (wn 334 W)
  q23 : Eqn
  q23 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q24 : Eqn
  q24 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q25 : Eqn
  q25 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q26 : Eqn
  q26 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q27 : Eqn
  q27 = eqn (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ Toff023 ∷ X3 ∷ X3 ∷ Toff203 ∷ X3 ∷ X3 ∷ Toff023 ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ X3 ∷ Toff023 ∷ X3 ∷ X3 ∷ Toff203 ∷ X3 ∷ X3 ∷ Toff023 ∷ X3 ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ X3 ∷ Toff203 ∷ X3 ∷ X3 ∷ Toff023 ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ X3 ∷ Toff023 ∷ X3 ∷ X3 ∷ Toff203 ∷ X3 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-Bar⟨SSKSKK31-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~30-⟶2⟩)
  q28 : Eqn
  q28 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q29 : Eqn
  q29 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wn 118 W)
  q30 : Eqn
  q30 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q31 : Eqn
  q31 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q32 : Eqn
  q32 = eqn (X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X3 ∷ []) (wn 2025 W)
  q33 : Eqn
  q33 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q34 : Eqn
  q34 = eqn (Sw01 ∷ CK12 ∷ []) (CK02 ∷ Sw01 ∷ []) (wn 329 W)
  q35 : Eqn
  q35 = eqn (Sw01 ∷ S1 ∷ []) (S0 ∷ Sw01 ∷ []) (wn 315 W)

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CS23 CS23 CK32 CS23 CK32 CK32 CX30 CK02 S0 CK02 S0 CS02 CS02 CS02 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 CX30 CS02 CS02 CK02 CS02 CK02 CK02 X3]: 567 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 60 q1 ∷
   rw⁻ 59 q2 ∷
   rw 58 q3 ∷
   rw 57 q3 ∷
   rw 56 q4 ∷
   rw 55 q3 ∷
   rw 54 q4 ∷
   rw 53 q4 ∷
   re 52 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 54 q5 ∷
   rw 53 q6 ∷
   rw⁻ 52 q5 ∷
   re 53 3 (CX31 ∷ []) ∷
   rw 51 q4 ∷
   rw 50 q4 ∷
   rw 49 q4 ∷
   rw 48 q4 ∷
   rw 47 q4 ∷
   rw 46 q4 ∷
   rw 45 q7 ∷
   rw 44 q3 ∷
   rw 43 q4 ∷
   rw 42 q4 ∷
   rw 41 q4 ∷
   rw 40 q7 ∷
   rw 39 q3 ∷
   rw 38 q7 ∷
   rw 37 q3 ∷
   re 36 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q5 ∷
   rw 37 q6 ∷
   rw⁻ 36 q5 ∷
   re 37 3 (CX31 ∷ []) ∷
   rw⁻ 35 q8 ∷
   rw⁻ 34 q8 ∷
   rw⁻ 33 q9 ∷
   rw⁻ 32 q8 ∷
   rw⁻ 31 q9 ∷
   rw⁻ 30 q9 ∷
   rw⁻ 29 q2 ∷
   rw 30 q10 ∷
   rw 29 q2 ∷
   re 31 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 30 q11 ∷
   rw 31 q9 ∷
   rw 32 q12 ∷
   rw 33 q13 ∷
   rw 34 q12 ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q5 ∷
   rw 36 q14 ∷
   rw 37 q5 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 36 q11 ∷
   rw 37 q15 ∷
   rw 30 q1 ∷
   rw 31 q16 ∷
   rw 32 q9 ∷
   rw 33 q17 ∷
   rw 34 q13 ∷
   rw 35 q17 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q5 ∷
   rw 37 q18 ∷
   rw 38 q5 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw 37 q16 ∷
   rw 38 q19 ∷
   rw 31 q20 ∷
   re 31 8 (Toff123 ∷ []) ∷
   re 30 3 (Toff023 ∷ []) ∷
   rw 31 q2 ∷
   rw 32 q2 ∷
   re 34 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 33 q21 ∷
   rw 34 q9 ∷
   rw 35 q12 ∷
   rw 36 q13 ∷
   rw 37 q12 ∷
   re 39 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q5 ∷
   rw 39 q14 ∷
   rw 40 q5 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 39 q21 ∷
   rw 40 q15 ∷
   rw 33 q1 ∷
   rw 34 q21 ∷
   rw 35 q9 ∷
   rw 36 q17 ∷
   rw 37 q13 ∷
   rw 38 q17 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q5 ∷
   rw 40 q18 ∷
   rw 41 q5 ∷
   re 39 3 (CS13 ∷ []) ∷
   rw 40 q21 ∷
   rw 41 q19 ∷
   rw 34 q22 ∷
   re 34 8 (Toff213 ∷ []) ∷
   re 33 3 (Toff203 ∷ []) ∷
   rw 34 q2 ∷
   rw 35 q2 ∷
   re 37 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 36 q11 ∷
   rw 37 q9 ∷
   rw 38 q12 ∷
   rw 39 q13 ∷
   rw 40 q12 ∷
   re 42 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 41 q5 ∷
   rw 42 q14 ∷
   rw 43 q5 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 42 q11 ∷
   rw 43 q15 ∷
   rw 36 q1 ∷
   rw 37 q16 ∷
   rw 38 q9 ∷
   rw 39 q17 ∷
   rw 40 q13 ∷
   rw 41 q17 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q5 ∷
   rw 43 q18 ∷
   rw 44 q5 ∷
   re 42 3 (CS13 ∷ []) ∷
   rw 43 q16 ∷
   rw 44 q19 ∷
   rw 37 q20 ∷
   re 37 8 (Toff123 ∷ []) ∷
   re 36 3 (Toff023 ∷ []) ∷
   rw 37 q2 ∷
   rw 38 q2 ∷
   re 40 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 39 q5 ∷
   rw 40 q14 ∷
   rw 41 q5 ∷
   re 39 3 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q5 ∷
   rw 41 q14 ∷
   rw 42 q5 ∷
   re 40 3 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 41 q5 ∷
   rw 42 q23 ∷
   rw 43 q5 ∷
   re 41 3 (CK30 ∷ []) ∷
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
   re 45 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 44 q5 ∷
   rw 45 q23 ∷
   rw 46 q5 ∷
   re 44 3 (CK30 ∷ []) ∷
   rw 45 q24 ∷
   rw 46 q23 ∷
   rw 47 q25 ∷
   rw 48 q23 ∷
   rw 49 q25 ∷
   rw 50 q14 ∷
   rw 51 q14 ∷
   rw 52 q14 ∷
   rw 53 q23 ∷
   rw 54 q25 ∷
   rw 55 q14 ∷
   rw 56 q14 ∷
   rw 57 q14 ∷
   rw 58 q14 ∷
   rw 59 q14 ∷
   rw 60 q14 ∷
   rw 61 q24 ∷
   rw 62 q14 ∷
   rw 63 q14 ∷
   rw 64 q23 ∷
   rw 65 q14 ∷
   rw 66 q23 ∷
   rw 67 q23 ∷
   rw 68 q2 ∷
   rw 69 q2 ∷
   re 71 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 70 q11 ∷
   rw 71 q9 ∷
   rw 72 q12 ∷
   rw 73 q13 ∷
   rw 74 q12 ∷
   re 76 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 75 q5 ∷
   rw 76 q14 ∷
   rw 77 q5 ∷
   re 75 3 (CS03 ∷ []) ∷
   rw 76 q11 ∷
   rw 77 q15 ∷
   rw 70 q1 ∷
   rw 71 q16 ∷
   rw 72 q9 ∷
   rw 73 q17 ∷
   rw 74 q13 ∷
   rw 75 q17 ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q5 ∷
   rw 77 q18 ∷
   rw 78 q5 ∷
   re 76 3 (CS13 ∷ []) ∷
   rw 77 q16 ∷
   rw 78 q19 ∷
   rw 71 q20 ∷
   re 71 8 (Toff123 ∷ []) ∷
   re 70 3 (Toff023 ∷ []) ∷
   rw 71 q2 ∷
   rw 72 q2 ∷
   re 74 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 73 q21 ∷
   rw 74 q9 ∷
   rw 75 q12 ∷
   rw 76 q13 ∷
   rw 77 q12 ∷
   re 79 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 78 q5 ∷
   rw 79 q14 ∷
   rw 80 q5 ∷
   re 78 3 (CS03 ∷ []) ∷
   rw 79 q21 ∷
   rw 80 q15 ∷
   rw 73 q1 ∷
   rw 74 q21 ∷
   rw 75 q9 ∷
   rw 76 q17 ∷
   rw 77 q13 ∷
   rw 78 q17 ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 79 q5 ∷
   rw 80 q18 ∷
   rw 81 q5 ∷
   re 79 3 (CS13 ∷ []) ∷
   rw 80 q21 ∷
   rw 81 q19 ∷
   rw 74 q22 ∷
   re 74 8 (Toff213 ∷ []) ∷
   re 73 3 (Toff203 ∷ []) ∷
   rw 74 q2 ∷
   rw 75 q2 ∷
   re 77 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 76 q11 ∷
   rw 77 q9 ∷
   rw 78 q12 ∷
   rw 79 q13 ∷
   rw 80 q12 ∷
   re 82 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 81 q5 ∷
   rw 82 q14 ∷
   rw 83 q5 ∷
   re 81 3 (CS03 ∷ []) ∷
   rw 82 q11 ∷
   rw 83 q15 ∷
   rw 76 q1 ∷
   rw 77 q16 ∷
   rw 78 q9 ∷
   rw 79 q17 ∷
   rw 80 q13 ∷
   rw 81 q17 ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 82 q5 ∷
   rw 83 q18 ∷
   rw 84 q5 ∷
   re 82 3 (CS13 ∷ []) ∷
   rw 83 q16 ∷
   rw 84 q19 ∷
   rw 77 q20 ∷
   re 77 8 (Toff123 ∷ []) ∷
   re 76 3 (Toff023 ∷ []) ∷
   rw 77 q2 ∷
   rw 78 q26 ∷
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
