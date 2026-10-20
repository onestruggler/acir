{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D558 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D522 W using (lem-Bar⟨SSKSKK21-⟶0⟩-passes-white-iX-via-V2-conjugates-3)

private
  q1 : Eqn
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
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
  q11 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q12 : Eqn
  q12 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wn 118 W)
  q13 : Eqn
  q13 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q14 : Eqn
  q14 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q15 : Eqn
  q15 = eqn (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wn 125 W)
  q16 : Eqn
  q16 = eqn (X2 ∷ Toff123 ∷ X2 ∷ []) (X2 ∷ CS23⁻ ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ []) (wn 1591 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q18 : Eqn
  q18 = eqn (Sw01 ∷ CK21⁻ ∷ []) (CK20⁻ ∷ Sw01 ∷ []) (wn 139 W)
  q19 : Eqn
  q19 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q20 : Eqn
  q20 = eqn (Sw01 ∷ S3⁻ ∷ []) (S3⁻ ∷ Sw01 ∷ []) (low-comm (Swap) (((S • S • S) ↑)))
  q21 : Eqn
  q21 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CS23⁻ ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS23⁻ ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ S3⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-Bar⟨SSKSKK21-⟶0⟩-passes-white-iX-via-V2-conjugates-3)
  q22 : Eqn
  q22 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q23 : Eqn
  q23 = eqn (CK20⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK21⁻ ∷ []) (wn 137 W)
  q24 : Eqn
  q24 = eqn (X2 ∷ CS23⁻ ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X2 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ S3⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X2 ∷ CX23 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ Toff123 ∷ X2 ∷ []) (wn 1592 W)
  q25 : Eqn
  q25 = eqn (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) (wn 123 W)
  q26 : Eqn
  q26 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q27 : Eqn
  q27 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q28 : Eqn
  q28 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X2 TOFF023 X2]: 427 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-TOFF023-X2 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ Toff023 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff023 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-TOFF023-X2 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ Toff023 ∷ X2 ∷ []) (X2 ∷ Toff023 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 32 q1 ∷
   rw⁻ 31 q2 ∷
   re 30 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 31 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 30 q3 ∷
   rw 31 q4 ∷
   rw 32 q5 ∷
   rw 33 q6 ∷
   rw 34 q5 ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q7 ∷
   rw 36 q8 ∷
   rw 37 q7 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 36 q3 ∷
   rw 37 q9 ∷
   rw 38 q10 ∷
   rw 37 q11 ∷
   rw 36 q12 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q7 ∷
   rw 36 q13 ∷
   rw⁻ 35 q7 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw 34 q14 ∷
   rw⁻ 33 q6 ∷
   rw 32 q14 ∷
   rw⁻ 31 q4 ∷
   rw 30 q12 ∷
   rw 31 q15 ∷
   re 31 8 (Toff123 ∷ []) ∷
   rw⁻ 29 q2 ∷
   rw 30 q16 ∷
   rw 29 q2 ∷
   rw 30 q6 ∷
   rw 31 q2 ∷
   re 33 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 32 q7 ∷
   rw 33 q17 ∷
   rw 34 q7 ∷
   re 32 3 (CS03⁻ ∷ []) ∷
   re 34 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 33 q7 ∷
   rw 34 q18 ∷
   rw 35 q7 ∷
   re 33 3 (CK30⁻ ∷ []) ∷
   re 35 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 34 q7 ∷
   rw 35 q17 ∷
   rw 36 q7 ∷
   re 34 3 (CS03⁻ ∷ []) ∷
   re 36 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 35 q7 ∷
   rw 36 q17 ∷
   rw 37 q7 ∷
   re 35 3 (CS03⁻ ∷ []) ∷
   rw 36 q2 ∷
   rw 37 q19 ∷
   rw 38 q2 ∷
   re 40 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 39 q7 ∷
   rw 40 q17 ∷
   rw 41 q7 ∷
   re 39 3 (CS03⁻ ∷ []) ∷
   re 41 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 40 q7 ∷
   rw 41 q17 ∷
   rw 42 q7 ∷
   re 40 3 (CS03⁻ ∷ []) ∷
   re 42 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 41 q7 ∷
   rw 42 q17 ∷
   rw 43 q7 ∷
   re 41 3 (CS03⁻ ∷ []) ∷
   re 43 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 42 q7 ∷
   rw 43 q17 ∷
   rw 44 q7 ∷
   re 42 3 (CS03⁻ ∷ []) ∷
   re 44 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 43 q7 ∷
   rw 44 q17 ∷
   rw 45 q7 ∷
   re 43 3 (CS03⁻ ∷ []) ∷
   re 45 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 44 q7 ∷
   rw 45 q17 ∷
   rw 46 q7 ∷
   re 44 3 (CS03⁻ ∷ []) ∷
   rw 45 q20 ∷
   re 47 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 46 q7 ∷
   rw 47 q18 ∷
   rw 48 q7 ∷
   re 46 3 (CK30⁻ ∷ []) ∷
   re 48 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 47 q7 ∷
   rw 48 q17 ∷
   rw 49 q7 ∷
   re 47 3 (CS03⁻ ∷ []) ∷
   re 49 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 48 q7 ∷
   rw 49 q17 ∷
   rw 50 q7 ∷
   re 48 3 (CS03⁻ ∷ []) ∷
   re 50 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 49 q7 ∷
   rw 50 q17 ∷
   rw 51 q7 ∷
   re 49 3 (CS03⁻ ∷ []) ∷
   rw 50 q2 ∷
   rw 51 q19 ∷
   rw 52 q2 ∷
   rw 53 q2 ∷
   rw 54 q17 ∷
   rw 55 q18 ∷
   rw 56 q17 ∷
   rw 57 q17 ∷
   rw 58 q2 ∷
   rw 59 q2 ∷
   rw 60 q8 ∷
   rw 61 q8 ∷
   rw 62 q8 ∷
   rw 63 q2 ∷
   re 65 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 64 q7 ∷
   rw 65 q17 ∷
   rw 66 q7 ∷
   re 64 3 (CS03⁻ ∷ []) ∷
   re 66 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 65 q7 ∷
   rw 66 q18 ∷
   rw 67 q7 ∷
   re 65 3 (CK30⁻ ∷ []) ∷
   re 67 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 66 q7 ∷
   rw 67 q17 ∷
   rw 68 q7 ∷
   re 66 3 (CS03⁻ ∷ []) ∷
   re 68 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 67 q7 ∷
   rw 68 q17 ∷
   rw 69 q7 ∷
   re 67 3 (CS03⁻ ∷ []) ∷
   rw 68 q2 ∷
   rw 69 q19 ∷
   rw 70 q2 ∷
   re 72 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 71 q7 ∷
   rw 72 q17 ∷
   rw 73 q7 ∷
   re 71 3 (CS03⁻ ∷ []) ∷
   re 73 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 72 q7 ∷
   rw 73 q17 ∷
   rw 74 q7 ∷
   re 72 3 (CS03⁻ ∷ []) ∷
   re 74 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 73 q7 ∷
   rw 74 q17 ∷
   rw 75 q7 ∷
   re 73 3 (CS03⁻ ∷ []) ∷
   re 75 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 74 q7 ∷
   rw 75 q17 ∷
   rw 76 q7 ∷
   re 74 3 (CS03⁻ ∷ []) ∷
   re 76 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 75 q7 ∷
   rw 76 q17 ∷
   rw 77 q7 ∷
   re 75 3 (CS03⁻ ∷ []) ∷
   re 77 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 76 q7 ∷
   rw 77 q17 ∷
   rw 78 q7 ∷
   re 76 3 (CS03⁻ ∷ []) ∷
   rw 77 q20 ∷
   re 79 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 78 q7 ∷
   rw 79 q18 ∷
   rw 80 q7 ∷
   re 78 3 (CK30⁻ ∷ []) ∷
   re 80 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 79 q7 ∷
   rw 80 q17 ∷
   rw 81 q7 ∷
   re 79 3 (CS03⁻ ∷ []) ∷
   re 81 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 80 q7 ∷
   rw 81 q17 ∷
   rw 82 q7 ∷
   re 80 3 (CS03⁻ ∷ []) ∷
   re 82 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 81 q7 ∷
   rw 82 q17 ∷
   rw 83 q7 ∷
   re 81 3 (CS03⁻ ∷ []) ∷
   rw 82 q2 ∷
   rw 83 q19 ∷
   rw 84 q2 ∷
   rw 85 q2 ∷
   rw 86 q17 ∷
   rw 87 q18 ∷
   rw 88 q17 ∷
   rw 89 q17 ∷
   rw 90 q2 ∷
   rw 91 q2 ∷
   rw 92 q17 ∷
   rw 93 q17 ∷
   rw 94 q17 ∷
   rw 95 q2 ∷
   rw 96 q10 ∷
   rw 0 q21 ∷
   rw 67 q1 ∷
   rw⁻ 66 q2 ∷
   rw 65 q22 ∷
   rw 64 q22 ∷
   rw 63 q22 ∷
   rw⁻ 62 q2 ∷
   rw⁻ 61 q2 ∷
   rw 60 q22 ∷
   rw 59 q22 ∷
   rw 58 q23 ∷
   rw 57 q22 ∷
   rw⁻ 56 q2 ∷
   rw⁻ 55 q2 ∷
   rw⁻ 54 q19 ∷
   rw⁻ 53 q2 ∷
   re 52 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 54 q7 ∷
   rw 53 q22 ∷
   rw⁻ 52 q7 ∷
   re 53 3 (CS13⁻ ∷ []) ∷
   re 51 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 53 q7 ∷
   rw 52 q22 ∷
   rw⁻ 51 q7 ∷
   re 52 3 (CS13⁻ ∷ []) ∷
   re 50 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 52 q7 ∷
   rw 51 q22 ∷
   rw⁻ 50 q7 ∷
   re 51 3 (CS13⁻ ∷ []) ∷
   re 49 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 51 q7 ∷
   rw 50 q23 ∷
   rw⁻ 49 q7 ∷
   re 50 3 (CK31⁻ ∷ []) ∷
   rw⁻ 48 q20 ∷
   re 47 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q7 ∷
   rw 48 q22 ∷
   rw⁻ 47 q7 ∷
   re 48 3 (CS13⁻ ∷ []) ∷
   re 46 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q7 ∷
   rw 47 q22 ∷
   rw⁻ 46 q7 ∷
   re 47 3 (CS13⁻ ∷ []) ∷
   re 45 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 47 q7 ∷
   rw 46 q22 ∷
   rw⁻ 45 q7 ∷
   re 46 3 (CS13⁻ ∷ []) ∷
   re 44 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q7 ∷
   rw 45 q22 ∷
   rw⁻ 44 q7 ∷
   re 45 3 (CS13⁻ ∷ []) ∷
   re 43 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q7 ∷
   rw 44 q22 ∷
   rw⁻ 43 q7 ∷
   re 44 3 (CS13⁻ ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q7 ∷
   rw 43 q22 ∷
   rw⁻ 42 q7 ∷
   re 43 3 (CS13⁻ ∷ []) ∷
   rw⁻ 41 q2 ∷
   rw⁻ 40 q19 ∷
   rw⁻ 39 q2 ∷
   re 38 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q7 ∷
   rw 39 q22 ∷
   rw⁻ 38 q7 ∷
   re 39 3 (CS13⁻ ∷ []) ∷
   re 37 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q7 ∷
   rw 38 q22 ∷
   rw⁻ 37 q7 ∷
   re 38 3 (CS13⁻ ∷ []) ∷
   re 36 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q7 ∷
   rw 37 q23 ∷
   rw⁻ 36 q7 ∷
   re 37 3 (CK31⁻ ∷ []) ∷
   re 35 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q7 ∷
   rw 36 q22 ∷
   rw⁻ 35 q7 ∷
   re 36 3 (CS13⁻ ∷ []) ∷
   rw⁻ 34 q2 ∷
   rw 33 q13 ∷
   rw 32 q13 ∷
   rw 31 q13 ∷
   rw⁻ 30 q2 ∷
   rw⁻ 29 q2 ∷
   rw 28 q22 ∷
   rw 27 q22 ∷
   rw 26 q23 ∷
   rw 25 q22 ∷
   rw⁻ 24 q2 ∷
   rw⁻ 23 q2 ∷
   rw⁻ 22 q19 ∷
   rw⁻ 21 q2 ∷
   re 20 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q7 ∷
   rw 21 q22 ∷
   rw⁻ 20 q7 ∷
   re 21 3 (CS13⁻ ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q7 ∷
   rw 20 q22 ∷
   rw⁻ 19 q7 ∷
   re 20 3 (CS13⁻ ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q7 ∷
   rw 19 q22 ∷
   rw⁻ 18 q7 ∷
   re 19 3 (CS13⁻ ∷ []) ∷
   re 17 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q7 ∷
   rw 18 q23 ∷
   rw⁻ 17 q7 ∷
   re 18 3 (CK31⁻ ∷ []) ∷
   rw⁻ 16 q20 ∷
   re 15 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q7 ∷
   rw 16 q22 ∷
   rw⁻ 15 q7 ∷
   re 16 3 (CS13⁻ ∷ []) ∷
   re 14 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q7 ∷
   rw 15 q22 ∷
   rw⁻ 14 q7 ∷
   re 15 3 (CS13⁻ ∷ []) ∷
   re 13 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q7 ∷
   rw 14 q22 ∷
   rw⁻ 13 q7 ∷
   re 14 3 (CS13⁻ ∷ []) ∷
   re 12 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q7 ∷
   rw 13 q22 ∷
   rw⁻ 12 q7 ∷
   re 13 3 (CS13⁻ ∷ []) ∷
   re 11 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q7 ∷
   rw 12 q22 ∷
   rw⁻ 11 q7 ∷
   re 12 3 (CS13⁻ ∷ []) ∷
   re 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q7 ∷
   rw 11 q22 ∷
   rw⁻ 10 q7 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q2 ∷
   rw⁻ 8 q19 ∷
   rw⁻ 7 q2 ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q7 ∷
   rw 7 q22 ∷
   rw⁻ 6 q7 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   re 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q7 ∷
   rw 6 q22 ∷
   rw⁻ 5 q7 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   re 4 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q7 ∷
   rw 5 q23 ∷
   rw⁻ 4 q7 ∷
   re 5 3 (CK31⁻ ∷ []) ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q7 ∷
   rw 4 q22 ∷
   rw⁻ 3 q7 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 2 q2 ∷
   rw⁻ 1 q6 ∷
   rw⁻ 0 q2 ∷
   rw 1 q24 ∷
   rw 0 q2 ∷
   re 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q6 ∷
   rw 5 q5 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 7 q8 ∷
   rw 8 q7 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q3 ∷
   rw 8 q9 ∷
   rw 1 q1 ∷
   rw 2 q25 ∷
   rw 3 q4 ∷
   rw 4 q26 ∷
   rw 5 q6 ∷
   rw 6 q26 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw 8 q27 ∷
   rw 9 q7 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 8 q25 ∷
   rw 9 q28 ∷
   rw 2 q15 ∷
   re 2 8 (Toff123 ∷ []) ∷
   re 1 3 (Toff023 ∷ []) ∷
   rw 2 q2 ∷
   rw 3 q10 ∷ []) Eq.refl
