{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D695 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D656 W using (lem-Bar⟨SSSKSS31-⟶0⟩-passes-Fredkin-WBar⟨KiKiSSSKiSSSSSS~30-⟶2⟩)

private
  q1 : Eqn
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q4 : Eqn
  q4 = eqn (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) (wn 481 W)
  q5 : Eqn
  q5 = eqn (CK02 ∷ Sw01 ∷ []) (Sw01 ∷ CK12 ∷ []) (wn 772 W)
  q6 : Eqn
  q6 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q8 : Eqn
  q8 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q9 : Eqn
  q9 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CK32 ∷ []) (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀))
  q11 : Eqn
  q11 = eqn (X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ S1 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) (X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) (wn 2028 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ K1 ∷ []) (K0 ∷ Sw01 ∷ []) (wn 121 W)
  q13 : Eqn
  q13 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q15 : Eqn
  q15 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q16 : Eqn
  q16 = eqn (Sw01 ∷ ι1 ∷ []) (ι ∷ Sw01 ∷ []) (wn 122 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) (wn 123 W)
  q18 : Eqn
  q18 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q19 : Eqn
  q19 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q20 : Eqn
  q20 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)
  q21 : Eqn
  q21 = eqn (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wn 125 W)
  q22 : Eqn
  q22 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K))
  q23 : Eqn
  q23 = eqn (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (wn 334 W)
  q24 : Eqn
  q24 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q25 : Eqn
  q25 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q26 : Eqn
  q26 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q27 : Eqn
  q27 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q28 : Eqn
  q28 = eqn (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ Toff023 ∷ X3 ∷ X3 ∷ Toff203 ∷ X3 ∷ X3 ∷ Toff023 ∷ X3 ∷ X3 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ X3 ∷ Toff023 ∷ X3 ∷ X3 ∷ Toff203 ∷ X3 ∷ X3 ∷ Toff023 ∷ X3 ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ X3 ∷ Toff203 ∷ X3 ∷ X3 ∷ Toff023 ∷ X3 ∷ X3 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ X3 ∷ Toff023 ∷ X3 ∷ X3 ∷ Toff203 ∷ X3 ∷ X3 ∷ Toff023 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (lem-Bar⟨SSSKSS31-⟶0⟩-passes-Fredkin-WBar⟨KiKiSSSKiSSSSSS~30-⟶2⟩)
  q29 : Eqn
  q29 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q30 : Eqn
  q30 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wn 118 W)
  q31 : Eqn
  q31 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q32 : Eqn
  q32 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q33 : Eqn
  q33 = eqn (X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) (X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ S1 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) (wn 2029 W)
  q34 : Eqn
  q34 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q35 : Eqn
  q35 = eqn (Sw01 ∷ S1 ∷ []) (S0 ∷ Sw01 ∷ []) (wn 315 W)
  q36 : Eqn
  q36 = eqn (Sw01 ∷ CK12 ∷ []) (CK02 ∷ Sw01 ∷ []) (wn 329 W)

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X3 CK32 S3 CK32 S3 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CX30 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 S0 S0 S0 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 S0 S0 S0 CK02 S0 S0 S0 S0 CK02 S0 CX30 CK02 S0 CK02 S0 CS02 CS02 CS02 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 X3]: 795 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-X3 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-X3 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ []) (X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw 107 q1 ∷
   rw⁻ 106 q2 ∷
   rw 105 q3 ∷
   rw 104 q3 ∷
   rw 103 q3 ∷
   rw 102 q3 ∷
   rw 101 q3 ∷
   rw 100 q3 ∷
   rw 99 q4 ∷
   rw 98 q5 ∷
   rw 97 q3 ∷
   rw 96 q3 ∷
   rw 95 q3 ∷
   rw 94 q4 ∷
   rw 93 q5 ∷
   rw 92 q4 ∷
   rw 91 q5 ∷
   re 90 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 92 q6 ∷
   rw 91 q7 ∷
   rw⁻ 90 q6 ∷
   re 91 3 (CX31 ∷ []) ∷
   rw 89 q4 ∷
   rw 88 q5 ∷
   rw 87 q4 ∷
   rw 86 q4 ∷
   rw 85 q4 ∷
   rw 84 q4 ∷
   rw 83 q5 ∷
   rw 82 q4 ∷
   rw 81 q4 ∷
   rw 80 q4 ∷
   rw 79 q3 ∷
   rw 78 q3 ∷
   rw 77 q3 ∷
   rw 76 q3 ∷
   rw 75 q3 ∷
   rw 74 q3 ∷
   rw 73 q3 ∷
   rw 72 q3 ∷
   rw 71 q3 ∷
   rw 70 q4 ∷
   rw 69 q5 ∷
   rw 68 q4 ∷
   rw 67 q4 ∷
   rw 66 q4 ∷
   rw 65 q3 ∷
   rw 64 q3 ∷
   rw 63 q3 ∷
   rw 62 q3 ∷
   rw 61 q3 ∷
   rw 60 q3 ∷
   rw 59 q3 ∷
   rw 58 q3 ∷
   rw 57 q3 ∷
   rw 56 q3 ∷
   rw 55 q3 ∷
   rw 54 q3 ∷
   rw 53 q3 ∷
   rw 52 q3 ∷
   rw 51 q3 ∷
   rw 50 q3 ∷
   rw 49 q3 ∷
   rw 48 q3 ∷
   re 47 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q6 ∷
   rw 48 q7 ∷
   rw⁻ 47 q6 ∷
   re 48 3 (CX31 ∷ []) ∷
   rw⁻ 46 q8 ∷
   rw⁻ 45 q8 ∷
   rw⁻ 44 q8 ∷
   rw⁻ 43 q8 ∷
   rw⁻ 42 q8 ∷
   rw⁻ 41 q8 ∷
   rw⁻ 40 q9 ∷
   rw⁻ 39 q10 ∷
   rw⁻ 38 q8 ∷
   rw⁻ 37 q8 ∷
   rw⁻ 36 q8 ∷
   rw⁻ 35 q9 ∷
   rw⁻ 34 q10 ∷
   rw⁻ 33 q9 ∷
   rw⁻ 32 q10 ∷
   rw⁻ 31 q2 ∷
   rw 32 q11 ∷
   rw 31 q2 ∷
   re 33 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 32 q12 ∷
   rw 33 q8 ∷
   rw 34 q13 ∷
   rw 35 q14 ∷
   rw 36 q13 ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q6 ∷
   rw 38 q15 ∷
   rw 39 q6 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 38 q12 ∷
   rw 39 q16 ∷
   rw 32 q1 ∷
   rw 33 q17 ∷
   rw 34 q8 ∷
   rw 35 q18 ∷
   rw 36 q14 ∷
   rw 37 q18 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q6 ∷
   rw 39 q19 ∷
   rw 40 q6 ∷
   re 38 3 (CS13 ∷ []) ∷
   rw 39 q17 ∷
   rw 40 q20 ∷
   rw 33 q21 ∷
   re 33 8 (Toff123 ∷ []) ∷
   re 32 3 (Toff023 ∷ []) ∷
   rw 33 q2 ∷
   rw 34 q2 ∷
   re 36 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 35 q22 ∷
   rw 36 q8 ∷
   rw 37 q13 ∷
   rw 38 q14 ∷
   rw 39 q13 ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q6 ∷
   rw 41 q15 ∷
   rw 42 q6 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 41 q22 ∷
   rw 42 q16 ∷
   rw 35 q1 ∷
   rw 36 q22 ∷
   rw 37 q8 ∷
   rw 38 q18 ∷
   rw 39 q14 ∷
   rw 40 q18 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q6 ∷
   rw 42 q19 ∷
   rw 43 q6 ∷
   re 41 3 (CS13 ∷ []) ∷
   rw 42 q22 ∷
   rw 43 q20 ∷
   rw 36 q23 ∷
   re 36 8 (Toff213 ∷ []) ∷
   re 35 3 (Toff203 ∷ []) ∷
   rw 36 q2 ∷
   rw 37 q2 ∷
   re 39 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 38 q12 ∷
   rw 39 q8 ∷
   rw 40 q13 ∷
   rw 41 q14 ∷
   rw 42 q13 ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q6 ∷
   rw 44 q15 ∷
   rw 45 q6 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw 44 q12 ∷
   rw 45 q16 ∷
   rw 38 q1 ∷
   rw 39 q17 ∷
   rw 40 q8 ∷
   rw 41 q18 ∷
   rw 42 q14 ∷
   rw 43 q18 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q6 ∷
   rw 45 q19 ∷
   rw 46 q6 ∷
   re 44 3 (CS13 ∷ []) ∷
   rw 45 q17 ∷
   rw 46 q20 ∷
   rw 39 q21 ∷
   re 39 8 (Toff123 ∷ []) ∷
   re 38 3 (Toff023 ∷ []) ∷
   rw 39 q2 ∷
   rw 40 q2 ∷
   re 42 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 41 q6 ∷
   rw 42 q24 ∷
   rw 43 q6 ∷
   re 41 3 (CK30 ∷ []) ∷
   rw 42 q9 ∷
   re 44 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 43 q6 ∷
   rw 44 q24 ∷
   rw 45 q6 ∷
   re 43 3 (CK30 ∷ []) ∷
   rw 44 q9 ∷
   re 46 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 45 q6 ∷
   rw 46 q15 ∷
   rw 47 q6 ∷
   re 45 3 (CS03 ∷ []) ∷
   re 47 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 46 q6 ∷
   rw 47 q15 ∷
   rw 48 q6 ∷
   re 46 3 (CS03 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 47 q6 ∷
   rw 48 q15 ∷
   rw 49 q6 ∷
   re 47 3 (CS03 ∷ []) ∷
   re 49 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 48 q6 ∷
   rw 49 q24 ∷
   rw 50 q6 ∷
   re 48 3 (CK30 ∷ []) ∷
   rw 49 q9 ∷
   re 51 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 50 q6 ∷
   rw 51 q15 ∷
   rw 52 q6 ∷
   re 50 3 (CS03 ∷ []) ∷
   re 52 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 51 q6 ∷
   rw 52 q15 ∷
   rw 53 q6 ∷
   re 51 3 (CS03 ∷ []) ∷
   re 53 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 52 q6 ∷
   rw 53 q15 ∷
   rw 54 q6 ∷
   re 52 3 (CS03 ∷ []) ∷
   re 54 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 53 q6 ∷
   rw 54 q15 ∷
   rw 55 q6 ∷
   re 53 3 (CS03 ∷ []) ∷
   re 55 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 54 q6 ∷
   rw 55 q15 ∷
   rw 56 q6 ∷
   re 54 3 (CS03 ∷ []) ∷
   re 56 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 55 q6 ∷
   rw 56 q15 ∷
   rw 57 q6 ∷
   re 55 3 (CS03 ∷ []) ∷
   rw 56 q25 ∷
   rw 57 q15 ∷
   rw 58 q15 ∷
   rw 59 q15 ∷
   rw 60 q15 ∷
   rw 61 q15 ∷
   rw 62 q15 ∷
   rw 63 q15 ∷
   rw 64 q15 ∷
   rw 65 q15 ∷
   rw 66 q15 ∷
   rw 67 q15 ∷
   rw 68 q15 ∷
   rw 69 q15 ∷
   rw 70 q15 ∷
   rw 71 q15 ∷
   rw 72 q15 ∷
   rw 73 q15 ∷
   rw 74 q15 ∷
   rw 75 q26 ∷
   rw 76 q26 ∷
   rw 77 q26 ∷
   rw 78 q24 ∷
   rw 79 q26 ∷
   rw 80 q15 ∷
   rw 81 q15 ∷
   rw 82 q15 ∷
   rw 83 q15 ∷
   rw 84 q15 ∷
   rw 85 q15 ∷
   rw 86 q15 ∷
   rw 87 q15 ∷
   rw 88 q15 ∷
   rw 89 q26 ∷
   rw 90 q26 ∷
   rw 91 q26 ∷
   rw 92 q24 ∷
   rw 93 q26 ∷
   rw 94 q26 ∷
   rw 95 q26 ∷
   rw 96 q26 ∷
   rw 97 q24 ∷
   rw 98 q26 ∷
   rw 99 q25 ∷
   rw 100 q24 ∷
   rw 101 q26 ∷
   rw 102 q24 ∷
   rw 103 q26 ∷
   rw 104 q15 ∷
   rw 105 q15 ∷
   rw 106 q15 ∷
   rw 107 q24 ∷
   rw 108 q26 ∷
   rw 109 q15 ∷
   rw 110 q15 ∷
   rw 111 q15 ∷
   rw 112 q15 ∷
   rw 113 q15 ∷
   rw 114 q15 ∷
   rw 115 q2 ∷
   rw 116 q2 ∷
   re 118 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 117 q12 ∷
   rw 118 q8 ∷
   rw 119 q13 ∷
   rw 120 q14 ∷
   rw 121 q13 ∷
   re 123 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 122 q6 ∷
   rw 123 q15 ∷
   rw 124 q6 ∷
   re 122 3 (CS03 ∷ []) ∷
   rw 123 q12 ∷
   rw 124 q16 ∷
   rw 117 q1 ∷
   rw 118 q17 ∷
   rw 119 q8 ∷
   rw 120 q18 ∷
   rw 121 q14 ∷
   rw 122 q18 ∷
   re 124 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 123 q6 ∷
   rw 124 q19 ∷
   rw 125 q6 ∷
   re 123 3 (CS13 ∷ []) ∷
   rw 124 q17 ∷
   rw 125 q20 ∷
   rw 118 q21 ∷
   re 118 8 (Toff123 ∷ []) ∷
   re 117 3 (Toff023 ∷ []) ∷
   rw 118 q2 ∷
   rw 119 q2 ∷
   re 121 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 120 q22 ∷
   rw 121 q8 ∷
   rw 122 q13 ∷
   rw 123 q14 ∷
   rw 124 q13 ∷
   re 126 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 125 q6 ∷
   rw 126 q15 ∷
   rw 127 q6 ∷
   re 125 3 (CS03 ∷ []) ∷
   rw 126 q22 ∷
   rw 127 q16 ∷
   rw 120 q1 ∷
   rw 121 q22 ∷
   rw 122 q8 ∷
   rw 123 q18 ∷
   rw 124 q14 ∷
   rw 125 q18 ∷
   re 127 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 126 q6 ∷
   rw 127 q19 ∷
   rw 128 q6 ∷
   re 126 3 (CS13 ∷ []) ∷
   rw 127 q22 ∷
   rw 128 q20 ∷
   rw 121 q23 ∷
   re 121 8 (Toff213 ∷ []) ∷
   re 120 3 (Toff203 ∷ []) ∷
   rw 121 q2 ∷
   rw 122 q2 ∷
   re 124 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 123 q12 ∷
   rw 124 q8 ∷
   rw 125 q13 ∷
   rw 126 q14 ∷
   rw 127 q13 ∷
   re 129 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 128 q6 ∷
   rw 129 q15 ∷
   rw 130 q6 ∷
   re 128 3 (CS03 ∷ []) ∷
   rw 129 q12 ∷
   rw 130 q16 ∷
   rw 123 q1 ∷
   rw 124 q17 ∷
   rw 125 q8 ∷
   rw 126 q18 ∷
   rw 127 q14 ∷
   rw 128 q18 ∷
   re 130 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 129 q6 ∷
   rw 130 q19 ∷
   rw 131 q6 ∷
   re 129 3 (CS13 ∷ []) ∷
   rw 130 q17 ∷
   rw 131 q20 ∷
   rw 124 q21 ∷
   re 124 8 (Toff123 ∷ []) ∷
   re 123 3 (Toff023 ∷ []) ∷
   rw 124 q2 ∷
   rw 125 q27 ∷
   rw 0 q28 ∷
   rw 94 q1 ∷
   rw⁻ 93 q2 ∷
   re 92 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 93 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 92 q12 ∷
   rw 93 q8 ∷
   rw 94 q13 ∷
   rw 95 q14 ∷
   rw 96 q13 ∷
   re 98 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 97 q6 ∷
   rw 98 q15 ∷
   rw 99 q6 ∷
   re 97 3 (CS03 ∷ []) ∷
   rw 98 q12 ∷
   rw 99 q16 ∷
   rw 100 q27 ∷
   rw 99 q29 ∷
   rw 98 q30 ∷
   re 97 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 99 q6 ∷
   rw 98 q3 ∷
   rw⁻ 97 q6 ∷
   re 98 3 (CS13 ∷ []) ∷
   rw 96 q31 ∷
   rw⁻ 95 q14 ∷
   rw 94 q31 ∷
   rw⁻ 93 q8 ∷
   rw 92 q30 ∷
   rw 93 q21 ∷
   re 93 8 (Toff123 ∷ []) ∷
   rw⁻ 91 q2 ∷
   rw⁻ 90 q2 ∷
   re 89 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 90 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 89 q22 ∷
   rw 90 q8 ∷
   rw 91 q13 ∷
   rw 92 q14 ∷
   rw 93 q13 ∷
   re 95 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 94 q6 ∷
   rw 95 q15 ∷
   rw 96 q6 ∷
   re 94 3 (CS03 ∷ []) ∷
   rw 95 q22 ∷
   rw 96 q16 ∷
   rw 97 q27 ∷
   rw 96 q29 ∷
   rw⁻ 95 q22 ∷
   re 94 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 96 q6 ∷
   rw 95 q3 ∷
   rw⁻ 94 q6 ∷
   re 95 3 (CS13 ∷ []) ∷
   rw 93 q31 ∷
   rw⁻ 92 q14 ∷
   rw 91 q31 ∷
   rw⁻ 90 q8 ∷
   rw⁻ 89 q22 ∷
   rw 90 q23 ∷
   re 90 8 (Toff213 ∷ []) ∷
   rw⁻ 88 q2 ∷
   rw⁻ 87 q2 ∷
   re 86 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 87 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 86 q12 ∷
   rw 87 q8 ∷
   rw 88 q13 ∷
   rw 89 q14 ∷
   rw 90 q13 ∷
   re 92 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 91 q6 ∷
   rw 92 q15 ∷
   rw 93 q6 ∷
   re 91 3 (CS03 ∷ []) ∷
   rw 92 q12 ∷
   rw 93 q16 ∷
   rw 94 q27 ∷
   rw 93 q29 ∷
   rw 92 q30 ∷
   re 91 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 93 q6 ∷
   rw 92 q3 ∷
   rw⁻ 91 q6 ∷
   re 92 3 (CS13 ∷ []) ∷
   rw 90 q31 ∷
   rw⁻ 89 q14 ∷
   rw 88 q31 ∷
   rw⁻ 87 q8 ∷
   rw 86 q30 ∷
   rw 87 q21 ∷
   re 87 8 (Toff123 ∷ []) ∷
   rw⁻ 85 q2 ∷
   rw⁻ 84 q2 ∷
   rw 83 q3 ∷
   rw 82 q3 ∷
   rw 81 q3 ∷
   rw 80 q3 ∷
   rw 79 q3 ∷
   rw 78 q3 ∷
   rw⁻ 77 q26 ∷
   rw 76 q32 ∷
   rw 75 q3 ∷
   rw 74 q3 ∷
   rw 73 q3 ∷
   rw⁻ 72 q26 ∷
   rw 71 q32 ∷
   rw⁻ 70 q26 ∷
   rw 69 q32 ∷
   rw⁻ 68 q25 ∷
   rw⁻ 67 q26 ∷
   rw 66 q32 ∷
   rw⁻ 65 q26 ∷
   rw⁻ 64 q26 ∷
   rw⁻ 63 q26 ∷
   rw⁻ 62 q26 ∷
   rw 61 q32 ∷
   rw⁻ 60 q26 ∷
   rw⁻ 59 q26 ∷
   rw⁻ 58 q26 ∷
   rw 57 q3 ∷
   rw 56 q3 ∷
   rw 55 q3 ∷
   rw 54 q3 ∷
   rw 53 q3 ∷
   rw 52 q3 ∷
   rw 51 q3 ∷
   rw 50 q3 ∷
   rw 49 q3 ∷
   rw⁻ 48 q26 ∷
   rw 47 q32 ∷
   rw⁻ 46 q26 ∷
   rw⁻ 45 q26 ∷
   rw⁻ 44 q26 ∷
   rw 43 q3 ∷
   rw 42 q3 ∷
   rw 41 q3 ∷
   rw 40 q3 ∷
   rw 39 q3 ∷
   rw 38 q3 ∷
   rw 37 q3 ∷
   rw 36 q3 ∷
   rw 35 q3 ∷
   rw 34 q3 ∷
   rw 33 q3 ∷
   rw 32 q3 ∷
   rw 31 q3 ∷
   rw 30 q3 ∷
   rw 29 q3 ∷
   rw 28 q3 ∷
   rw 27 q3 ∷
   rw 26 q3 ∷
   rw⁻ 25 q25 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q6 ∷
   rw 25 q3 ∷
   rw⁻ 24 q6 ∷
   re 25 3 (CS13 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q6 ∷
   rw 24 q3 ∷
   rw⁻ 23 q6 ∷
   re 24 3 (CS13 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q6 ∷
   rw 23 q3 ∷
   rw⁻ 22 q6 ∷
   re 23 3 (CS13 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q6 ∷
   rw 22 q3 ∷
   rw⁻ 21 q6 ∷
   re 22 3 (CS13 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q6 ∷
   rw 21 q3 ∷
   rw⁻ 20 q6 ∷
   re 21 3 (CS13 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q6 ∷
   rw 20 q3 ∷
   rw⁻ 19 q6 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw⁻ 18 q9 ∷
   re 17 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q6 ∷
   rw 18 q32 ∷
   rw⁻ 17 q6 ∷
   re 18 3 (CK31 ∷ []) ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q6 ∷
   rw 17 q3 ∷
   rw⁻ 16 q6 ∷
   re 17 3 (CS13 ∷ []) ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q6 ∷
   rw 16 q3 ∷
   rw⁻ 15 q6 ∷
   re 16 3 (CS13 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q6 ∷
   rw 15 q3 ∷
   rw⁻ 14 q6 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw⁻ 13 q9 ∷
   re 12 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q6 ∷
   rw 13 q32 ∷
   rw⁻ 12 q6 ∷
   re 13 3 (CK31 ∷ []) ∷
   rw⁻ 11 q9 ∷
   re 10 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q6 ∷
   rw 11 q32 ∷
   rw⁻ 10 q6 ∷
   re 11 3 (CK31 ∷ []) ∷
   rw⁻ 9 q2 ∷
   rw⁻ 8 q2 ∷
   re 7 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 8 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 7 q12 ∷
   rw 8 q8 ∷
   rw 9 q13 ∷
   rw 10 q14 ∷
   rw 11 q13 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   rw 13 q15 ∷
   rw 14 q6 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q12 ∷
   rw 14 q16 ∷
   rw 15 q27 ∷
   rw 14 q29 ∷
   rw 13 q30 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q6 ∷
   rw 13 q3 ∷
   rw⁻ 12 q6 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 11 q31 ∷
   rw⁻ 10 q14 ∷
   rw 9 q31 ∷
   rw⁻ 8 q8 ∷
   rw 7 q30 ∷
   rw 8 q21 ∷
   re 8 8 (Toff123 ∷ []) ∷
   rw⁻ 6 q2 ∷
   rw⁻ 5 q2 ∷
   re 4 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 5 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 4 q22 ∷
   rw 5 q8 ∷
   rw 6 q13 ∷
   rw 7 q14 ∷
   rw 8 q13 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 10 q15 ∷
   rw 11 q6 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q22 ∷
   rw 11 q16 ∷
   rw 12 q27 ∷
   rw 11 q29 ∷
   rw⁻ 10 q22 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q6 ∷
   rw 10 q3 ∷
   rw⁻ 9 q6 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 8 q31 ∷
   rw⁻ 7 q14 ∷
   rw 6 q31 ∷
   rw⁻ 5 q8 ∷
   rw⁻ 4 q22 ∷
   rw 5 q23 ∷
   re 5 8 (Toff213 ∷ []) ∷
   rw⁻ 3 q2 ∷
   rw⁻ 2 q2 ∷
   re 1 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 1 q12 ∷
   rw 2 q8 ∷
   rw 3 q13 ∷
   rw 4 q14 ∷
   rw 5 q13 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 7 q15 ∷
   rw 8 q6 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q12 ∷
   rw 8 q16 ∷
   rw 9 q27 ∷
   rw 8 q29 ∷
   rw 7 q30 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q6 ∷
   rw 7 q3 ∷
   rw⁻ 6 q6 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 5 q31 ∷
   rw⁻ 4 q14 ∷
   rw 3 q31 ∷
   rw⁻ 2 q8 ∷
   rw 1 q30 ∷
   rw 2 q21 ∷
   re 2 8 (Toff123 ∷ []) ∷
   rw⁻ 0 q2 ∷
   rw 1 q33 ∷
   rw 0 q2 ∷
   rw 1 q10 ∷
   rw 2 q9 ∷
   rw 3 q10 ∷
   rw 4 q9 ∷
   rw 5 q8 ∷
   rw 6 q8 ∷
   rw 7 q8 ∷
   rw 8 q10 ∷
   rw 9 q9 ∷
   rw 10 q8 ∷
   rw 11 q8 ∷
   rw 12 q8 ∷
   rw 13 q8 ∷
   rw 14 q8 ∷
   rw 15 q8 ∷
   re 17 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 16 q6 ∷
   rw 17 q34 ∷
   rw 18 q6 ∷
   re 16 3 (CX30 ∷ []) ∷
   rw 17 q15 ∷
   rw 18 q15 ∷
   rw 19 q15 ∷
   rw 20 q15 ∷
   rw 21 q15 ∷
   rw 22 q15 ∷
   rw 23 q15 ∷
   rw 24 q15 ∷
   rw 25 q15 ∷
   rw 26 q15 ∷
   rw 27 q15 ∷
   rw 28 q15 ∷
   rw 29 q15 ∷
   rw 30 q15 ∷
   rw 31 q15 ∷
   rw 32 q15 ∷
   rw 33 q15 ∷
   rw 34 q15 ∷
   rw 35 q35 ∷
   rw 36 q35 ∷
   rw 37 q35 ∷
   rw 38 q36 ∷
   rw 39 q35 ∷
   rw 40 q15 ∷
   rw 41 q15 ∷
   rw 42 q15 ∷
   rw 43 q15 ∷
   rw 44 q15 ∷
   rw 45 q15 ∷
   rw 46 q15 ∷
   rw 47 q15 ∷
   rw 48 q15 ∷
   rw 49 q35 ∷
   rw 50 q35 ∷
   rw 51 q35 ∷
   rw 52 q36 ∷
   rw 53 q35 ∷
   rw 54 q35 ∷
   rw 55 q35 ∷
   rw 56 q35 ∷
   rw 57 q36 ∷
   rw 58 q35 ∷
   re 60 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 59 q6 ∷
   rw 60 q34 ∷
   rw 61 q6 ∷
   re 59 3 (CX30 ∷ []) ∷
   rw 60 q36 ∷
   rw 61 q35 ∷
   rw 62 q36 ∷
   rw 63 q35 ∷
   rw 64 q15 ∷
   rw 65 q15 ∷
   rw 66 q15 ∷
   rw 67 q36 ∷
   rw 68 q35 ∷
   rw 69 q15 ∷
   rw 70 q15 ∷
   rw 71 q15 ∷
   rw 72 q15 ∷
   rw 73 q15 ∷
   rw 74 q15 ∷
   rw 75 q2 ∷
   rw 76 q27 ∷ []) Eq.refl
