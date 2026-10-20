{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D198 (W : Ws) where

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
  q1 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q2 : Eqn
  q2 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q3 : Eqn
  q3 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q4 : Eqn
  q4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q5 : Eqn
  q5 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q6 : Eqn
  q6 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q7 : Eqn
  q7 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q8 : Eqn
  q8 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (wn 733 W)
  q9 : Eqn
  q9 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q10 : Eqn
  q10 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (wn 735 W)

-- Bar(SSSKSS;3,1->0) passes white iX via V2 conjugates 2 part3: 200 steps
lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part3 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS31-⟶0⟩-passes-white-iX-via-V2-conjugates-2-part3 = derive (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ S2⁻ ∷ CK20⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ CS02⁻ ∷ X3 ∷ CX32 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ CS03⁻ ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (re 61 3 (CS03 ∷ []) ∷
   rw 62 q1 ∷
   rw 93 q2 ∷
   rw 92 q3 ∷
   re 91 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 93 q4 ∷
   re 90 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 92 q4 ∷
   re 89 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 91 q4 ∷
   re 88 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 90 q4 ∷
   rw 87 q3 ∷
   rw 86 q5 ∷
   rw 85 q5 ∷
   rw 84 q6 ∷
   rw 83 q5 ∷
   rw 82 q5 ∷
   rw 81 q5 ∷
   re 80 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 82 q4 ∷
   rw 79 q5 ∷
   rw 78 q5 ∷
   rw 77 q5 ∷
   rw 76 q5 ∷
   rw 75 q5 ∷
   rw 74 q5 ∷
   rw 73 q5 ∷
   rw 72 q5 ∷
   rw 71 q5 ∷
   rw 70 q7 ∷
   rw 69 q6 ∷
   rw 68 q5 ∷
   rw 67 q5 ∷
   rw 66 q5 ∷
   rw 65 q5 ∷
   rw 64 q5 ∷
   rw 63 q5 ∷
   re 62 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 64 q4 ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 63 q4 ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 62 q4 ∷
   re 59 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 61 q4 ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 60 q4 ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 59 q4 ∷
   re 56 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 58 q4 ∷
   rw 57 q8 ∷
   rw 56 q9 ∷
   rw 59 q2 ∷
   re 57 3 (CS03⁻ ∷ []) ∷
   rw 60 q2 ∷
   re 58 3 (CK30⁻ ∷ []) ∷
   rw 61 q2 ∷
   re 59 3 (CS03⁻ ∷ []) ∷
   rw 62 q2 ∷
   re 60 3 (CS03⁻ ∷ []) ∷
   rw 61 q9 ∷
   rw 64 q2 ∷
   re 62 3 (CS03 ∷ []) ∷
   rw 65 q2 ∷
   re 63 3 (CS03 ∷ []) ∷
   rw 66 q2 ∷
   re 64 3 (CS03 ∷ []) ∷
   rw 67 q2 ∷
   re 65 3 (CK30 ∷ []) ∷
   rw 68 q2 ∷
   re 66 3 (CS03 ∷ []) ∷
   rw 69 q2 ∷
   re 67 3 (CS03 ∷ []) ∷
   rw 70 q2 ∷
   re 68 3 (CX31 ∷ []) ∷
   rw⁻ 69 q5 ∷
   rw⁻ 70 q5 ∷
   rw⁻ 71 q5 ∷
   rw⁻ 72 q5 ∷
   rw⁻ 73 q5 ∷
   rw⁻ 74 q5 ∷
   rw⁻ 75 q6 ∷
   rw⁻ 76 q7 ∷
   rw⁻ 77 q5 ∷
   rw⁻ 78 q5 ∷
   rw⁻ 79 q5 ∷
   rw⁻ 80 q5 ∷
   rw⁻ 81 q5 ∷
   rw⁻ 82 q5 ∷
   rw⁻ 83 q5 ∷
   rw⁻ 84 q5 ∷
   rw⁻ 85 q5 ∷
   rw 88 q2 ∷
   re 86 3 (CX31 ∷ []) ∷
   rw⁻ 87 q5 ∷
   rw⁻ 88 q5 ∷
   rw⁻ 89 q5 ∷
   rw⁻ 90 q6 ∷
   rw⁻ 91 q5 ∷
   rw⁻ 92 q5 ∷
   rw 93 q4 ∷
   rw 98 q2 ∷
   rw 97 q3 ∷
   re 96 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 98 q4 ∷
   re 95 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 97 q4 ∷
   re 94 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 96 q4 ∷
   rw 93 q3 ∷
   rw 92 q5 ∷
   rw 91 q5 ∷
   rw 90 q6 ∷
   rw 89 q5 ∷
   rw 88 q5 ∷
   rw 87 q5 ∷
   re 86 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 88 q4 ∷
   rw 85 q5 ∷
   rw 84 q5 ∷
   rw 83 q5 ∷
   rw 82 q5 ∷
   rw 81 q5 ∷
   rw 80 q5 ∷
   rw 79 q5 ∷
   rw 78 q5 ∷
   rw 77 q5 ∷
   rw 76 q7 ∷
   rw 75 q6 ∷
   rw 74 q5 ∷
   rw 73 q5 ∷
   rw 72 q5 ∷
   rw 71 q5 ∷
   rw 70 q5 ∷
   rw 69 q5 ∷
   re 68 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 70 q4 ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 69 q4 ∷
   re 66 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 68 q4 ∷
   re 65 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 67 q4 ∷
   re 64 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 66 q4 ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 65 q4 ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 64 q4 ∷
   rw 63 q10 ∷
   rw 62 q9 ∷
   rw 65 q2 ∷
   re 63 3 (CS03⁻ ∷ []) ∷
   rw 66 q2 ∷
   re 64 3 (CS03⁻ ∷ []) ∷
   rw 67 q2 ∷
   re 65 3 (CS03⁻ ∷ []) ∷
   rw 66 q9 ∷
   rw 69 q2 ∷
   re 67 3 (CS03 ∷ []) ∷
   rw 70 q2 ∷
   re 68 3 (CS03 ∷ []) ∷
   rw 71 q2 ∷
   re 69 3 (CS03 ∷ []) ∷
   rw 72 q2 ∷
   re 70 3 (CK30 ∷ []) ∷
   rw 73 q2 ∷
   re 71 3 (CS03 ∷ []) ∷
   rw 74 q2 ∷
   re 72 3 (CS03 ∷ []) ∷
   rw 75 q2 ∷
   re 73 3 (CX31 ∷ []) ∷
   rw⁻ 74 q5 ∷
   rw⁻ 75 q5 ∷
   rw⁻ 76 q5 ∷
   rw⁻ 77 q5 ∷
   rw⁻ 78 q5 ∷
   rw⁻ 79 q5 ∷
   rw⁻ 80 q6 ∷
   rw⁻ 81 q7 ∷
   rw⁻ 82 q5 ∷
   rw⁻ 83 q5 ∷
   rw⁻ 84 q5 ∷
   rw⁻ 85 q5 ∷
   rw⁻ 86 q5 ∷
   rw⁻ 87 q5 ∷
   rw⁻ 88 q5 ∷
   rw⁻ 89 q5 ∷
   rw⁻ 90 q5 ∷
   rw 93 q2 ∷
   re 91 3 (CX31 ∷ []) ∷
   rw⁻ 92 q5 ∷
   rw⁻ 93 q5 ∷
   rw⁻ 94 q5 ∷
   rw⁻ 95 q6 ∷
   rw⁻ 96 q5 ∷
   rw⁻ 97 q5 ∷
   rw 98 q4 ∷ []) Eq.refl

private
  q11 : Eqn
  q11 = eqn (CS01 ∷ X3 ∷ []) (X3 ∷ CS01 ∷ []) (low-comm (CS) ((X ↑)))
  q12 : Eqn
  q12 = eqn (CS01 ∷ CK32 ∷ []) (CK32 ∷ CS01 ∷ []) (low-comm (CS) (CK₁₀))
  q13 : Eqn
  q13 = eqn (CK10 ∷ X3 ∷ []) (X3 ∷ CK10 ∷ []) (low-comm (CK₁₀) ((X ↑)))
  q14 : Eqn
  q14 = eqn (CK10 ∷ CK32 ∷ []) (CK32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CK₁₀))
  q15 : Eqn
  q15 = eqn (CX31 ∷ X3 ∷ CK32 ∷ X3 ∷ []) (X3 ∷ CK32 ∷ X3 ∷ CX31 ∷ []) (wn 528 W)
  q16 : Eqn
  q16 = eqn (S1 ∷ X3 ∷ []) (X3 ∷ S1 ∷ []) (low-comm ((S ↑)) ((X ↑)))
  q17 : Eqn
  q17 = eqn (S1 ∷ CK32 ∷ []) (CK32 ∷ S1 ∷ []) (low-comm ((S ↑)) (CK₁₀))
  q18 : Eqn
  q18 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q19 : Eqn
  q19 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q20 : Eqn
  q20 = eqn (Sw01 ∷ CK32 ∷ []) (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀))
  q21 : Eqn
  q21 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q22 : Eqn
  q22 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q23 : Eqn
  q23 = eqn (CS13 ∷ X3 ∷ CK32 ∷ X3 ∷ []) (X3 ∷ CK32 ∷ X3 ∷ CS13 ∷ []) (wn 530 W)
  q24 : Eqn
  q24 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q25 : Eqn
  q25 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q26 : Eqn
  q26 = eqn (CK31 ∷ X3 ∷ CK32 ∷ X3 ∷ []) (X3 ∷ CK32 ∷ X3 ∷ CK31 ∷ []) (wn 529 W)
  q27 : Eqn
  q27 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X3 CK32 X3]: 185 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK32-X3 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK32-X3 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CK32 ∷ X3 ∷ []) (X3 ∷ CK32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw 30 q11 ∷
   rw 31 q12 ∷
   rw 32 q11 ∷
   rw 29 q11 ∷
   rw 30 q12 ∷
   rw 31 q11 ∷
   rw 28 q13 ∷
   rw 29 q14 ∷
   rw 30 q13 ∷
   rw 27 q11 ∷
   rw 28 q12 ∷
   rw 29 q11 ∷
   rw 26 q11 ∷
   rw 27 q12 ∷
   rw 28 q11 ∷
   rw 25 q11 ∷
   rw 26 q12 ∷
   rw 27 q11 ∷
   rw 24 q15 ∷
   rw 23 q11 ∷
   rw 24 q12 ∷
   rw 25 q11 ∷
   rw 22 q11 ∷
   rw 23 q12 ∷
   rw 24 q11 ∷
   rw 21 q11 ∷
   rw 22 q12 ∷
   rw 23 q11 ∷
   rw 20 q11 ∷
   rw 21 q12 ∷
   rw 22 q11 ∷
   rw 19 q11 ∷
   rw 20 q12 ∷
   rw 21 q11 ∷
   rw 18 q11 ∷
   rw 19 q12 ∷
   rw 20 q11 ∷
   rw 17 q11 ∷
   rw 18 q12 ∷
   rw 19 q11 ∷
   rw 16 q11 ∷
   rw 17 q12 ∷
   rw 18 q11 ∷
   rw 15 q11 ∷
   rw 16 q12 ∷
   rw 17 q11 ∷
   rw 14 q16 ∷
   rw 15 q17 ∷
   rw 16 q16 ∷
   rw 13 q13 ∷
   rw 14 q14 ∷
   rw 15 q13 ∷
   rw 12 q11 ∷
   rw 13 q12 ∷
   rw 14 q11 ∷
   rw 11 q11 ∷
   rw 12 q12 ∷
   rw 13 q11 ∷
   rw 10 q11 ∷
   rw 11 q12 ∷
   rw 12 q11 ∷
   rw 9 q11 ∷
   rw 10 q12 ∷
   rw 11 q11 ∷
   rw 8 q11 ∷
   rw 9 q12 ∷
   rw 10 q11 ∷
   rw 7 q11 ∷
   rw 8 q12 ∷
   rw 9 q11 ∷
   rw 6 q15 ∷
   rw 9 q18 ∷
   rw⁻ 8 q19 ∷
   rw⁻ 7 q20 ∷
   rw⁻ 6 q19 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q21 ∷
   rw 6 q22 ∷
   rw⁻ 5 q21 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 6 q23 ∷
   rw 5 q19 ∷
   rw 6 q20 ∷
   rw 7 q19 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q21 ∷
   rw 9 q24 ∷
   rw 10 q21 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q1 ∷
   rw 8 q18 ∷
   rw⁻ 7 q19 ∷
   rw⁻ 6 q20 ∷
   rw⁻ 5 q19 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q21 ∷
   rw 5 q22 ∷
   rw⁻ 4 q21 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 5 q23 ∷
   rw 4 q19 ∷
   rw 5 q20 ∷
   rw 6 q19 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q21 ∷
   rw 8 q24 ∷
   rw 9 q21 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q1 ∷
   rw 7 q18 ∷
   rw⁻ 6 q19 ∷
   rw⁻ 5 q20 ∷
   rw⁻ 4 q19 ∷
   re 3 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q21 ∷
   rw 4 q25 ∷
   rw⁻ 3 q21 ∷
   re 4 3 (CK31 ∷ []) ∷
   rw 4 q26 ∷
   rw 3 q19 ∷
   rw 4 q20 ∷
   rw 5 q19 ∷
   re 7 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 6 q21 ∷
   rw 7 q27 ∷
   rw 8 q21 ∷
   re 6 3 (CK30 ∷ []) ∷
   rw 7 q1 ∷
   rw 6 q18 ∷
   rw⁻ 5 q19 ∷
   rw⁻ 4 q20 ∷
   rw⁻ 3 q19 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q21 ∷
   rw 3 q22 ∷
   rw⁻ 2 q21 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw 3 q23 ∷
   rw 2 q19 ∷
   rw 3 q20 ∷
   rw 4 q19 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q21 ∷
   rw 6 q24 ∷
   rw 7 q21 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q1 ∷
   rw 5 q18 ∷
   rw⁻ 4 q19 ∷
   rw⁻ 3 q20 ∷
   rw⁻ 2 q19 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q21 ∷
   rw 2 q22 ∷
   rw⁻ 1 q21 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 2 q23 ∷
   rw 1 q19 ∷
   rw 2 q20 ∷
   rw 3 q19 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q21 ∷
   rw 5 q24 ∷
   rw 6 q21 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q1 ∷
   rw 4 q18 ∷
   rw⁻ 3 q19 ∷
   rw⁻ 2 q20 ∷
   rw⁻ 1 q19 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q21 ∷
   rw 1 q22 ∷
   rw⁻ 0 q21 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q23 ∷
   rw 0 q19 ∷
   rw 1 q20 ∷
   rw 2 q19 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q21 ∷
   rw 4 q24 ∷
   rw 5 q21 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q1 ∷ []) Eq.refl
