{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD551 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D551 (W : Ws) (Sᴰ : SD551) where

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
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-white-iX-via-V2-conjugates-2 : St 931
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-white-iX-via-V2-conjugates-2 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
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
  q16 = eqn (X3 ∷ Toff123 ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ []) (wn 1575 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q18 : Eqn
  q18 = eqn (Sw01 ∷ CK21⁻ ∷ []) (CK20⁻ ∷ Sw01 ∷ []) (wn 139 W)
  q19 : Eqn
  q19 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q20 : Eqn
  q20 = eqn (Sw01 ∷ S2⁻ ∷ []) (S2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S • S • S)))
  q21 : Eqn
  q21 = eqn (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (lem-Bar⟨SSKSKK31-⟶0⟩-passes-white-iX-via-V2-conjugates-2)
  q22 : Eqn
  q22 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q23 : Eqn
  q23 = eqn (CK20⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK21⁻ ∷ []) (wn 137 W)
  q24 : Eqn
  q24 = eqn (X3 ∷ CS23⁻ ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S2⁻ ∷ CK21⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CK31⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ X3 ∷ CS13⁻ ∷ CS13⁻ ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff123 ∷ X3 ∷ []) (wn 1576 W)
  q25 : Eqn
  q25 = eqn (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) (wn 123 W)
  q26 : Eqn
  q26 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q27 : Eqn
  q27 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q28 : Eqn
  q28 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 TOFF023 X3]: 315 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF023-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ Toff023 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff023 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF023-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ Toff023 ∷ X3 ∷ []) (X3 ∷ Toff023 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
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
   rw 32 q17 ∷
   rw 33 q18 ∷
   rw 34 q17 ∷
   rw 35 q17 ∷
   rw 36 q2 ∷
   rw 37 q19 ∷
   rw 38 q2 ∷
   rw 39 q17 ∷
   rw 40 q17 ∷
   rw 41 q17 ∷
   rw 42 q17 ∷
   rw 43 q17 ∷
   rw 44 q17 ∷
   rw 45 q20 ∷
   rw 46 q18 ∷
   rw 47 q17 ∷
   rw 48 q17 ∷
   rw 49 q17 ∷
   rw 50 q2 ∷
   rw 51 q19 ∷
   rw 52 q2 ∷
   rw 53 q2 ∷
   re 55 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 54 q7 ∷
   rw 55 q17 ∷
   rw 56 q7 ∷
   re 54 3 (CS03⁻ ∷ []) ∷
   re 56 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 55 q7 ∷
   rw 56 q18 ∷
   rw 57 q7 ∷
   re 55 3 (CK30⁻ ∷ []) ∷
   re 57 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 56 q7 ∷
   rw 57 q17 ∷
   rw 58 q7 ∷
   re 56 3 (CS03⁻ ∷ []) ∷
   re 58 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 57 q7 ∷
   rw 58 q17 ∷
   rw 59 q7 ∷
   re 57 3 (CS03⁻ ∷ []) ∷
   rw 58 q2 ∷
   rw 59 q2 ∷
   re 61 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 60 q7 ∷
   rw 61 q8 ∷
   rw 62 q7 ∷
   re 60 3 (CS03 ∷ []) ∷
   re 62 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 61 q7 ∷
   rw 62 q8 ∷
   rw 63 q7 ∷
   re 61 3 (CS03 ∷ []) ∷
   re 63 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 62 q7 ∷
   rw 63 q8 ∷
   rw 64 q7 ∷
   re 62 3 (CS03 ∷ []) ∷
   rw 63 q2 ∷
   rw 64 q17 ∷
   rw 65 q18 ∷
   rw 66 q17 ∷
   rw 67 q17 ∷
   rw 68 q2 ∷
   rw 69 q19 ∷
   rw 70 q2 ∷
   rw 71 q17 ∷
   rw 72 q17 ∷
   rw 73 q17 ∷
   rw 74 q17 ∷
   rw 75 q17 ∷
   rw 76 q17 ∷
   rw 77 q20 ∷
   rw 78 q18 ∷
   rw 79 q17 ∷
   rw 80 q17 ∷
   rw 81 q17 ∷
   rw 82 q2 ∷
   rw 83 q19 ∷
   rw 84 q2 ∷
   rw 85 q2 ∷
   re 87 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 86 q7 ∷
   rw 87 q17 ∷
   rw 88 q7 ∷
   re 86 3 (CS03⁻ ∷ []) ∷
   re 88 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 87 q7 ∷
   rw 88 q18 ∷
   rw 89 q7 ∷
   re 87 3 (CK30⁻ ∷ []) ∷
   re 89 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 88 q7 ∷
   rw 89 q17 ∷
   rw 90 q7 ∷
   re 88 3 (CS03⁻ ∷ []) ∷
   re 90 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 89 q7 ∷
   rw 90 q17 ∷
   rw 91 q7 ∷
   re 89 3 (CS03⁻ ∷ []) ∷
   rw 90 q2 ∷
   rw 91 q2 ∷
   re 93 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 92 q7 ∷
   rw 93 q17 ∷
   rw 94 q7 ∷
   re 92 3 (CS03⁻ ∷ []) ∷
   re 94 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 93 q7 ∷
   rw 94 q17 ∷
   rw 95 q7 ∷
   re 93 3 (CS03⁻ ∷ []) ∷
   re 95 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 94 q7 ∷
   rw 95 q17 ∷
   rw 96 q7 ∷
   re 94 3 (CS03⁻ ∷ []) ∷
   rw 95 q2 ∷
   rw 96 q10 ∷
   rw 0 q21 ∷
   rw 67 q1 ∷
   rw⁻ 66 q2 ∷
   re 65 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 67 q7 ∷
   rw 66 q22 ∷
   rw⁻ 65 q7 ∷
   re 66 3 (CS13⁻ ∷ []) ∷
   re 64 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 66 q7 ∷
   rw 65 q22 ∷
   rw⁻ 64 q7 ∷
   re 65 3 (CS13⁻ ∷ []) ∷
   re 63 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 65 q7 ∷
   rw 64 q22 ∷
   rw⁻ 63 q7 ∷
   re 64 3 (CS13⁻ ∷ []) ∷
   rw⁻ 62 q2 ∷
   rw⁻ 61 q2 ∷
   re 60 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 62 q7 ∷
   rw 61 q22 ∷
   rw⁻ 60 q7 ∷
   re 61 3 (CS13⁻ ∷ []) ∷
   re 59 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 61 q7 ∷
   rw 60 q22 ∷
   rw⁻ 59 q7 ∷
   re 60 3 (CS13⁻ ∷ []) ∷
   re 58 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 60 q7 ∷
   rw 59 q23 ∷
   rw⁻ 58 q7 ∷
   re 59 3 (CK31⁻ ∷ []) ∷
   re 57 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 59 q7 ∷
   rw 58 q22 ∷
   rw⁻ 57 q7 ∷
   re 58 3 (CS13⁻ ∷ []) ∷
   rw⁻ 56 q2 ∷
   rw⁻ 55 q2 ∷
   rw⁻ 54 q19 ∷
   rw⁻ 53 q2 ∷
   rw 52 q22 ∷
   rw 51 q22 ∷
   rw 50 q22 ∷
   rw 49 q23 ∷
   rw⁻ 48 q20 ∷
   rw 47 q22 ∷
   rw 46 q22 ∷
   rw 45 q22 ∷
   rw 44 q22 ∷
   rw 43 q22 ∷
   rw 42 q22 ∷
   rw⁻ 41 q2 ∷
   rw⁻ 40 q19 ∷
   rw⁻ 39 q2 ∷
   rw 38 q22 ∷
   rw 37 q22 ∷
   rw 36 q23 ∷
   rw 35 q22 ∷
   rw⁻ 34 q2 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q7 ∷
   rw 34 q13 ∷
   rw⁻ 33 q7 ∷
   re 34 3 (CS13 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q7 ∷
   rw 33 q13 ∷
   rw⁻ 32 q7 ∷
   re 33 3 (CS13 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q7 ∷
   rw 32 q13 ∷
   rw⁻ 31 q7 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw⁻ 30 q2 ∷
   rw⁻ 29 q2 ∷
   re 28 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q7 ∷
   rw 29 q22 ∷
   rw⁻ 28 q7 ∷
   re 29 3 (CS13⁻ ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q7 ∷
   rw 28 q22 ∷
   rw⁻ 27 q7 ∷
   re 28 3 (CS13⁻ ∷ []) ∷
   re 26 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q7 ∷
   rw 27 q23 ∷
   rw⁻ 26 q7 ∷
   re 27 3 (CK31⁻ ∷ []) ∷
   re 25 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q7 ∷
   rw 26 q22 ∷
   rw⁻ 25 q7 ∷
   re 26 3 (CS13⁻ ∷ []) ∷
   rw⁻ 24 q2 ∷
   rw⁻ 23 q2 ∷
   rw⁻ 22 q19 ∷
   rw⁻ 21 q2 ∷
   rw 20 q22 ∷
   rw 19 q22 ∷
   rw 18 q22 ∷
   rw 17 q23 ∷
   rw⁻ 16 q20 ∷
   rw 15 q22 ∷
   rw 14 q22 ∷
   rw 13 q22 ∷
   rw 12 q22 ∷
   rw 11 q22 ∷
   rw 10 q22 ∷
   rw⁻ 9 q2 ∷
   rw⁻ 8 q19 ∷
   rw⁻ 7 q2 ∷
   rw 6 q22 ∷
   rw 5 q22 ∷
   rw 4 q23 ∷
   rw 3 q22 ∷
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
