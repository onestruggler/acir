{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D074 (W : Ws) where

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
  q1 = wE 3 W
  q2 : Eqn
  q2 = wE 578 W
  q3 : Eqn
  q3 = wE 175 W
  q4 : Eqn
  q4 = wE 1 W
  q5 : Eqn
  q5 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q6 : Eqn
  q6 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q7 : Eqn
  q7 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q8 : Eqn
  q8 = wE 173 W
  q9 : Eqn
  q9 = wE 580 W

-- Bar(SSKSKK;3,1->0) passes white iX via V2 conjugates 2 part3: 154 steps
lem-Bar⟨SSKSKK31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part3 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ Sw23 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part3 = derive (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ Sw23 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ Sw23 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (re 61 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 63 q1 ∷
   re 60 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 62 q1 ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 61 q1 ∷
   re 58 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 60 q1 ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 59 q1 ∷
   re 56 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 58 q1 ∷
   rw 57 q2 ∷
   rw 56 q3 ∷
   rw 59 q4 ∷
   re 57 3 (CS03⁻ ∷ []) ∷
   rw 60 q4 ∷
   re 58 3 (CK30⁻ ∷ []) ∷
   rw 61 q4 ∷
   re 59 3 (CS03⁻ ∷ []) ∷
   rw 62 q4 ∷
   re 60 3 (CS03⁻ ∷ []) ∷
   rw 61 q3 ∷
   rw 64 q4 ∷
   re 62 3 (CS03 ∷ []) ∷
   rw 65 q4 ∷
   re 63 3 (CS03 ∷ []) ∷
   rw 66 q4 ∷
   re 64 3 (CK30 ∷ []) ∷
   rw 67 q4 ∷
   re 65 3 (CS03 ∷ []) ∷
   rw 68 q4 ∷
   re 66 3 (CK30 ∷ []) ∷
   rw 69 q4 ∷
   re 67 3 (CK30 ∷ []) ∷
   rw 70 q4 ∷
   re 68 3 (CX31 ∷ []) ∷
   rw⁻ 69 q5 ∷
   rw⁻ 70 q6 ∷
   rw⁻ 71 q5 ∷
   rw⁻ 72 q6 ∷
   rw⁻ 73 q7 ∷
   rw⁻ 74 q7 ∷
   rw⁻ 75 q7 ∷
   rw⁻ 76 q5 ∷
   rw⁻ 77 q6 ∷
   rw⁻ 78 q7 ∷
   rw⁻ 79 q7 ∷
   rw⁻ 80 q7 ∷
   rw⁻ 81 q7 ∷
   rw⁻ 82 q7 ∷
   rw⁻ 83 q7 ∷
   rw 86 q4 ∷
   re 84 3 (CX31 ∷ []) ∷
   rw⁻ 85 q7 ∷
   rw⁻ 86 q7 ∷
   rw⁻ 87 q5 ∷
   rw⁻ 88 q7 ∷
   rw⁻ 89 q5 ∷
   rw⁻ 90 q5 ∷
   rw 91 q1 ∷
   rw 96 q4 ∷
   rw 95 q8 ∷
   re 94 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 96 q1 ∷
   re 93 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 95 q1 ∷
   re 92 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 94 q1 ∷
   rw 91 q8 ∷
   rw 90 q5 ∷
   rw 89 q5 ∷
   rw 88 q7 ∷
   rw 87 q5 ∷
   rw 86 q7 ∷
   rw 85 q7 ∷
   re 84 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 86 q1 ∷
   rw 83 q7 ∷
   rw 82 q7 ∷
   rw 81 q7 ∷
   rw 80 q7 ∷
   rw 79 q7 ∷
   rw 78 q7 ∷
   rw 77 q6 ∷
   rw 76 q5 ∷
   rw 75 q7 ∷
   rw 74 q7 ∷
   rw 73 q7 ∷
   rw 72 q6 ∷
   rw 71 q5 ∷
   rw 70 q6 ∷
   rw 69 q5 ∷
   re 68 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 70 q1 ∷
   re 67 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 69 q1 ∷
   re 66 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 68 q1 ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 67 q1 ∷
   re 64 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 66 q1 ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 65 q1 ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 64 q1 ∷
   rw 63 q9 ∷
   rw 62 q3 ∷
   rw 65 q4 ∷
   re 63 3 (CS03⁻ ∷ []) ∷
   rw 66 q4 ∷
   re 64 3 (CS03⁻ ∷ []) ∷
   rw 67 q4 ∷
   re 65 3 (CS03⁻ ∷ []) ∷
   rw 66 q3 ∷
   rw 69 q4 ∷
   re 67 3 (CS03 ∷ []) ∷
   rw 70 q4 ∷
   re 68 3 (CS03 ∷ []) ∷
   rw 71 q4 ∷
   re 69 3 (CK30 ∷ []) ∷
   rw 72 q4 ∷
   re 70 3 (CS03 ∷ []) ∷
   rw 73 q4 ∷
   re 71 3 (CK30 ∷ []) ∷
   rw 74 q4 ∷
   re 72 3 (CK30 ∷ []) ∷
   rw 75 q4 ∷
   re 73 3 (CX31 ∷ []) ∷
   rw⁻ 74 q5 ∷
   rw⁻ 75 q6 ∷
   rw⁻ 76 q5 ∷
   rw⁻ 77 q6 ∷
   rw⁻ 78 q7 ∷
   rw⁻ 79 q7 ∷
   rw⁻ 80 q7 ∷
   rw⁻ 81 q5 ∷
   rw⁻ 82 q6 ∷
   rw⁻ 83 q7 ∷
   rw⁻ 84 q7 ∷
   rw⁻ 85 q7 ∷
   rw⁻ 86 q7 ∷
   rw⁻ 87 q7 ∷
   rw⁻ 88 q7 ∷
   rw 91 q4 ∷
   re 89 3 (CX31 ∷ []) ∷
   rw⁻ 90 q7 ∷
   rw⁻ 91 q7 ∷
   rw⁻ 92 q5 ∷
   rw⁻ 93 q7 ∷
   rw⁻ 94 q5 ∷
   rw⁻ 95 q5 ∷
   rw 96 q1 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = wE 581 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CKd30 X3]: 85 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CKd30-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CKd30-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (X3 ∷ CK30⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 32 q4 ∷
   rw 31 q8 ∷
   re 30 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   rw 29 q8 ∷
   rw 28 q5 ∷
   rw 27 q5 ∷
   rw 26 q7 ∷
   rw 25 q5 ∷
   rw 24 q7 ∷
   rw 23 q7 ∷
   re 22 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   rw 21 q7 ∷
   rw 20 q7 ∷
   rw 19 q7 ∷
   rw 18 q7 ∷
   rw 17 q7 ∷
   rw 16 q7 ∷
   rw 15 q6 ∷
   rw 14 q5 ∷
   rw 13 q7 ∷
   rw 12 q7 ∷
   rw 11 q7 ∷
   rw 10 q6 ∷
   rw 9 q5 ∷
   rw 8 q6 ∷
   rw 7 q5 ∷
   re 6 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 8 q1 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 7 q1 ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 6 q1 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q1 ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 4 q1 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q1 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q1 ∷
   rw 1 q10 ∷
   rw 0 q3 ∷
   rw 3 q4 ∷
   re 1 3 (CK30⁻ ∷ []) ∷
   rw 2 q3 ∷
   rw 5 q4 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 6 q4 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 7 q4 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 8 q4 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 9 q4 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 10 q4 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 11 q4 ∷
   re 9 3 (CX31 ∷ []) ∷
   rw⁻ 10 q5 ∷
   rw⁻ 11 q6 ∷
   rw⁻ 12 q5 ∷
   rw⁻ 13 q6 ∷
   rw⁻ 14 q7 ∷
   rw⁻ 15 q7 ∷
   rw⁻ 16 q7 ∷
   rw⁻ 17 q5 ∷
   rw⁻ 18 q6 ∷
   rw⁻ 19 q7 ∷
   rw⁻ 20 q7 ∷
   rw⁻ 21 q7 ∷
   rw⁻ 22 q7 ∷
   rw⁻ 23 q7 ∷
   rw⁻ 24 q7 ∷
   rw 27 q4 ∷
   re 25 3 (CX31 ∷ []) ∷
   rw⁻ 26 q7 ∷
   rw⁻ 27 q7 ∷
   rw⁻ 28 q5 ∷
   rw⁻ 29 q7 ∷
   rw⁻ 30 q5 ∷
   rw⁻ 31 q5 ∷
   rw 32 q1 ∷ []) Eq.refl

private
  q11 : Eqn
  q11 = eqn (CK10 ∷ X3 ∷ []) (X3 ∷ CK10 ∷ []) (low-comm (CK₁₀) ((X ↑)))
  q12 : Eqn
  q12 = eqn (CK10 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((S ↑ • CK₁₀)))
  q13 : Eqn
  q13 = eqn (CS01 ∷ X3 ∷ []) (X3 ∷ CS01 ∷ []) (low-comm (CS) ((X ↑)))
  q14 : Eqn
  q14 = eqn (CS01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CS01 ∷ []) (low-comm (CS) ((S ↑ • CK₁₀)))
  q15 : Eqn
  q15 = wE 547 W
  q16 : Eqn
  q16 = eqn (S1 ∷ X3 ∷ []) (X3 ∷ S1 ∷ []) (low-comm ((S ↑)) ((X ↑)))
  q17 : Eqn
  q17 = eqn (S1 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ S1 ∷ []) (low-comm ((S ↑)) ((S ↑ • CK₁₀)))
  q18 : Eqn
  q18 = wE 5 W
  q19 : Eqn
  q19 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q20 : Eqn
  q20 = eqn (Sw01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑ • CK₁₀)))
  q21 : Eqn
  q21 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q22 : Eqn
  q22 = wE 140 W
  q23 : Eqn
  q23 = wE 548 W
  q24 : Eqn
  q24 = wE 142 W
  q25 : Eqn
  q25 = wE 31 W
  q26 : Eqn
  q26 = wE 7 W
  q27 : Eqn
  q27 = wE 549 W
  q28 : Eqn
  q28 = wE 27 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CKd32 X3]: 179 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CKd32-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CKd32-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (X3 ∷ CK32⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 28 q11 ∷
   rw 29 q12 ∷
   rw 30 q11 ∷
   rw 27 q11 ∷
   rw 28 q12 ∷
   rw 29 q11 ∷
   rw 26 q13 ∷
   rw 27 q14 ∷
   rw 28 q13 ∷
   rw 25 q11 ∷
   rw 26 q12 ∷
   rw 27 q11 ∷
   rw 24 q13 ∷
   rw 25 q14 ∷
   rw 26 q13 ∷
   rw 23 q13 ∷
   rw 24 q14 ∷
   rw 25 q13 ∷
   rw 22 q15 ∷
   rw 21 q13 ∷
   rw 22 q14 ∷
   rw 23 q13 ∷
   rw 20 q13 ∷
   rw 21 q14 ∷
   rw 22 q13 ∷
   rw 19 q13 ∷
   rw 20 q14 ∷
   rw 21 q13 ∷
   rw 18 q13 ∷
   rw 19 q14 ∷
   rw 20 q13 ∷
   rw 17 q13 ∷
   rw 18 q14 ∷
   rw 19 q13 ∷
   rw 16 q13 ∷
   rw 17 q14 ∷
   rw 18 q13 ∷
   rw 15 q16 ∷
   rw 16 q17 ∷
   rw 17 q16 ∷
   rw 14 q11 ∷
   rw 15 q12 ∷
   rw 16 q11 ∷
   rw 13 q13 ∷
   rw 14 q14 ∷
   rw 15 q13 ∷
   rw 12 q13 ∷
   rw 13 q14 ∷
   rw 14 q13 ∷
   rw 11 q13 ∷
   rw 12 q14 ∷
   rw 13 q13 ∷
   rw 10 q16 ∷
   rw 11 q17 ∷
   rw 12 q16 ∷
   rw 9 q11 ∷
   rw 10 q12 ∷
   rw 11 q11 ∷
   rw 8 q16 ∷
   rw 9 q17 ∷
   rw 10 q16 ∷
   rw 7 q11 ∷
   rw 8 q12 ∷
   rw 9 q11 ∷
   rw 6 q15 ∷
   rw 9 q18 ∷
   rw⁻ 8 q19 ∷
   rw⁻ 7 q20 ∷
   rw⁻ 6 q19 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q21 ∷
   rw 6 q22 ∷
   rw⁻ 5 q21 ∷
   re 6 3 (CK31 ∷ []) ∷
   rw 6 q23 ∷
   rw 5 q19 ∷
   rw 6 q20 ∷
   rw 7 q19 ∷
   re 9 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 8 q21 ∷
   rw 9 q24 ∷
   rw 10 q21 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 9 q25 ∷
   rw 8 q18 ∷
   rw⁻ 7 q19 ∷
   rw⁻ 6 q20 ∷
   rw⁻ 5 q19 ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q21 ∷
   rw 5 q22 ∷
   rw⁻ 4 q21 ∷
   re 5 3 (CK31 ∷ []) ∷
   rw 5 q23 ∷
   rw 4 q19 ∷
   rw 5 q20 ∷
   rw 6 q19 ∷
   re 8 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 7 q21 ∷
   rw 8 q24 ∷
   rw 9 q21 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 8 q25 ∷
   rw 7 q18 ∷
   rw⁻ 6 q19 ∷
   rw⁻ 5 q20 ∷
   rw⁻ 4 q19 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q21 ∷
   rw 4 q26 ∷
   rw⁻ 3 q21 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 4 q27 ∷
   rw 3 q19 ∷
   rw 4 q20 ∷
   rw 5 q19 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q21 ∷
   rw 7 q28 ∷
   rw 8 q21 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q25 ∷
   rw 6 q18 ∷
   rw⁻ 5 q19 ∷
   rw⁻ 4 q20 ∷
   rw⁻ 3 q19 ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q21 ∷
   rw 3 q22 ∷
   rw⁻ 2 q21 ∷
   re 3 3 (CK31 ∷ []) ∷
   rw 3 q23 ∷
   rw 2 q19 ∷
   rw 3 q20 ∷
   rw 4 q19 ∷
   re 6 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 5 q21 ∷
   rw 6 q24 ∷
   rw 7 q21 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 6 q25 ∷
   rw 5 q18 ∷
   rw⁻ 4 q19 ∷
   rw⁻ 3 q20 ∷
   rw⁻ 2 q19 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q21 ∷
   rw 2 q26 ∷
   rw⁻ 1 q21 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 2 q27 ∷
   rw 1 q19 ∷
   rw 2 q20 ∷
   rw 3 q19 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q21 ∷
   rw 5 q28 ∷
   rw 6 q21 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q25 ∷
   rw 4 q18 ∷
   rw⁻ 3 q19 ∷
   rw⁻ 2 q20 ∷
   rw⁻ 1 q19 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q21 ∷
   rw 1 q26 ∷
   rw⁻ 0 q21 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q27 ∷
   rw 0 q19 ∷
   rw 1 q20 ∷
   rw 2 q19 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q21 ∷
   rw 4 q28 ∷
   rw 5 q21 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q25 ∷ []) Eq.refl
