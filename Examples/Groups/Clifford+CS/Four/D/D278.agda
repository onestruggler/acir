{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D278 (W : Ws) where

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
  q1 = wE 27 W
  q2 : Eqn
  q2 = wE 315 W
  q3 : Eqn
  q3 = wE 329 W
  q4 : Eqn
  q4 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q5 : Eqn
  q5 = wE 39 W
  q6 : Eqn
  q6 = wE 31 W
  q7 : Eqn
  q7 = wE 5 W
  q8 : Eqn
  q8 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q9 : Eqn
  q9 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q10 : Eqn
  q10 = wE 7 W
  q11 : Eqn
  q11 = wE 481 W
  q12 : Eqn
  q12 = wE 772 W
  q13 : Eqn
  q13 = wE 6 W
  q14 : Eqn
  q14 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q15 : Eqn
  q15 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q16 : Eqn
  q16 = eqn (Sw01 ∷ CK32 ∷ []) (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀))
  q17 : Eqn
  q17 = wE 863 W

-- Bar(['K', 'i', 'K', 'i', 'S', 'S', 'S', 'K', 'i', 'S', 'S', 'S', 'S', 'S', 'S'];3,0->2) passes white iX via V2 conjugates 1 part10: 214 steps
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part10 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw01 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ S1 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sw01 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part10 = derive (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw01 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ S1 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sw01 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ X3 ∷ CS12⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ S1⁻ ∷ CK12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ CS12⁻ ∷ X3 ∷ CX31 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CK32⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ CS23⁻ ∷ CS23⁻ ∷ X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ [])
  (rw 104 q1 ∷
   rw 105 q1 ∷
   rw 106 q1 ∷
   rw 107 q1 ∷
   rw 108 q1 ∷
   rw 109 q1 ∷
   rw 110 q2 ∷
   rw 111 q2 ∷
   rw 112 q2 ∷
   rw 113 q3 ∷
   rw 114 q2 ∷
   rw 115 q2 ∷
   rw 116 q2 ∷
   rw 117 q2 ∷
   rw 118 q3 ∷
   rw 119 q2 ∷
   re 121 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 120 q4 ∷
   rw 121 q5 ∷
   rw 122 q4 ∷
   re 120 3 (CX30 ∷ []) ∷
   rw 121 q3 ∷
   rw 122 q2 ∷
   rw 123 q3 ∷
   rw 124 q2 ∷
   rw 125 q1 ∷
   rw 126 q1 ∷
   rw 127 q1 ∷
   rw 128 q3 ∷
   rw 129 q2 ∷
   rw 130 q1 ∷
   rw 131 q1 ∷
   rw 132 q1 ∷
   rw 133 q1 ∷
   rw 134 q1 ∷
   rw 135 q1 ∷
   rw 136 q6 ∷
   rw 141 q7 ∷
   rw⁻ 140 q8 ∷
   rw⁻ 139 q9 ∷
   rw⁻ 138 q9 ∷
   rw⁻ 137 q9 ∷
   rw⁻ 136 q8 ∷
   rw 135 q10 ∷
   rw 134 q10 ∷
   rw 133 q10 ∷
   rw 132 q10 ∷
   rw 131 q10 ∷
   rw 130 q10 ∷
   rw 129 q11 ∷
   rw 128 q12 ∷
   rw 127 q10 ∷
   rw 126 q10 ∷
   rw 125 q10 ∷
   rw 124 q11 ∷
   rw 123 q12 ∷
   rw 122 q11 ∷
   rw 121 q12 ∷
   re 120 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 122 q4 ∷
   rw 121 q13 ∷
   rw⁻ 120 q4 ∷
   re 121 3 (CX31 ∷ []) ∷
   rw 119 q11 ∷
   rw 118 q12 ∷
   rw 117 q11 ∷
   rw 116 q11 ∷
   rw 115 q11 ∷
   rw 114 q11 ∷
   rw 113 q12 ∷
   rw 112 q11 ∷
   rw 111 q11 ∷
   rw 110 q11 ∷
   rw 109 q10 ∷
   rw 108 q10 ∷
   rw 107 q10 ∷
   rw 106 q10 ∷
   rw 105 q10 ∷
   rw 104 q10 ∷
   rw 103 q10 ∷
   rw 102 q10 ∷
   rw 101 q10 ∷
   rw 100 q11 ∷
   rw 99 q12 ∷
   rw 98 q11 ∷
   rw 97 q11 ∷
   rw 96 q11 ∷
   rw 95 q10 ∷
   rw 94 q10 ∷
   rw 93 q10 ∷
   rw 92 q10 ∷
   rw 91 q10 ∷
   rw 90 q10 ∷
   rw 89 q10 ∷
   rw 88 q10 ∷
   rw 87 q10 ∷
   rw 86 q10 ∷
   rw 85 q10 ∷
   rw 84 q10 ∷
   rw 83 q10 ∷
   rw 82 q10 ∷
   rw 81 q10 ∷
   rw 80 q10 ∷
   rw 79 q10 ∷
   rw 78 q10 ∷
   re 77 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 79 q4 ∷
   rw 78 q13 ∷
   rw⁻ 77 q4 ∷
   re 78 3 (CX31 ∷ []) ∷
   rw⁻ 76 q14 ∷
   rw⁻ 75 q14 ∷
   rw⁻ 74 q14 ∷
   rw⁻ 73 q14 ∷
   rw⁻ 72 q14 ∷
   rw⁻ 71 q14 ∷
   rw⁻ 70 q15 ∷
   rw⁻ 69 q16 ∷
   rw⁻ 68 q14 ∷
   rw⁻ 67 q14 ∷
   rw⁻ 66 q14 ∷
   rw⁻ 65 q15 ∷
   rw⁻ 64 q16 ∷
   rw⁻ 63 q15 ∷
   rw⁻ 62 q16 ∷
   rw 63 q17 ∷
   rw 62 q8 ∷
   rw 63 q9 ∷
   rw 64 q9 ∷
   rw 65 q9 ∷
   rw 66 q8 ∷
   rw 67 q16 ∷
   rw 68 q15 ∷
   rw 69 q16 ∷
   rw 70 q15 ∷
   rw 71 q14 ∷
   rw 72 q14 ∷
   rw 73 q14 ∷
   rw 74 q16 ∷
   rw 75 q15 ∷
   rw 76 q14 ∷
   rw 77 q14 ∷
   rw 78 q14 ∷
   rw 79 q14 ∷
   rw 80 q14 ∷
   rw 81 q14 ∷
   re 83 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 82 q4 ∷
   rw 83 q5 ∷
   rw 84 q4 ∷
   re 82 3 (CX30 ∷ []) ∷
   rw 83 q1 ∷
   rw 84 q1 ∷
   rw 85 q1 ∷
   rw 86 q1 ∷
   rw 87 q1 ∷
   rw 88 q1 ∷
   rw 89 q1 ∷
   rw 90 q1 ∷
   rw 91 q1 ∷
   rw 92 q1 ∷
   rw 93 q1 ∷
   rw 94 q1 ∷
   rw 95 q1 ∷
   rw 96 q1 ∷
   rw 97 q1 ∷
   rw 98 q1 ∷
   rw 99 q1 ∷
   rw 100 q1 ∷
   rw 101 q2 ∷
   rw 102 q2 ∷
   rw 103 q2 ∷
   rw 104 q3 ∷
   rw 105 q2 ∷
   rw 106 q1 ∷
   rw 107 q1 ∷
   rw 108 q1 ∷
   rw 109 q1 ∷
   rw 110 q1 ∷
   rw 111 q1 ∷
   rw 112 q1 ∷
   rw 113 q1 ∷
   rw 114 q1 ∷
   rw 115 q2 ∷
   rw 116 q2 ∷
   rw 117 q2 ∷
   rw 118 q3 ∷
   rw 119 q2 ∷
   rw 120 q2 ∷
   rw 121 q2 ∷
   rw 122 q2 ∷
   rw 123 q3 ∷
   rw 124 q2 ∷
   re 126 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 125 q4 ∷
   rw 126 q5 ∷
   rw 127 q4 ∷
   re 125 3 (CX30 ∷ []) ∷
   rw 126 q3 ∷
   rw 127 q2 ∷
   rw 128 q3 ∷
   rw 129 q2 ∷
   rw 130 q1 ∷
   rw 131 q1 ∷
   rw 132 q1 ∷
   rw 133 q3 ∷
   rw 134 q2 ∷
   rw 135 q1 ∷
   rw 136 q1 ∷
   rw 137 q1 ∷
   rw 138 q1 ∷
   rw 139 q1 ∷
   rw 140 q1 ∷
   rw 141 q6 ∷ []) Eq.refl
