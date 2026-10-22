{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD645 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D645 (W : Ws) (Sᴰ : SD645) where

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
  lem-HD-X-form : St 1390
  lem-HD-X-form = pickᴰ 0 Sᴰ
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30 : St 1589
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30 = pickᴰ 1 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK30-CS02-CS02-CS02-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S3-CK30 : St 1590
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK30-CS02-CS02-CS02-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S3-CK30 = pickᴰ 2 Sᴰ

private
  q1 : Eqn
  q1 = sE 1390 lem-HD-X-form
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = wE 464 W
  q5 : Eqn
  q5 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q6 : Eqn
  q6 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q7 : Eqn
  q7 = wE 1845 W
  q8 : Eqn
  q8 = wE 151 W
  q9 : Eqn
  q9 = sE 1590 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK30-CS02-CS02-CS02-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S3-CK30
  q10 : Eqn
  q10 = sE 1589 lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30
  q11 : Eqn
  q11 = sE 1390 lem-HD-X-form

-- X P3 -> P3 X: 215 steps
lem-X-P3--⟶-P3-X : ⟪ (Toff312 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ Toff312 ∷ []) ⟫ʷ
lem-X-P3--⟶-P3-X = derive (Toff312 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ Toff312 ∷ [])
  (rw 0 q1 ∷
   rw 171 q2 ∷
   re 170 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 172 q3 ∷
   re 169 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 171 q3 ∷
   re 168 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 170 q3 ∷
   re 167 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 169 q3 ∷
   re 166 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 168 q3 ∷
   re 165 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 167 q3 ∷
   re 164 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 166 q3 ∷
   re 163 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 165 q3 ∷
   re 162 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 164 q3 ∷
   re 161 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 163 q3 ∷
   re 160 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 162 q3 ∷
   re 159 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 161 q3 ∷
   re 158 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 160 q3 ∷
   rw 157 q4 ∷
   re 156 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 158 q3 ∷
   re 155 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 157 q3 ∷
   re 154 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 156 q3 ∷
   re 153 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 155 q3 ∷
   rw 152 q4 ∷
   re 151 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 153 q3 ∷
   rw 150 q4 ∷
   re 149 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 151 q3 ∷
   re 148 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 150 q3 ∷
   rw 147 q5 ∷
   rw 146 q5 ∷
   rw 145 q6 ∷
   rw 144 q5 ∷
   rw 143 q6 ∷
   rw 142 q6 ∷
   re 141 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 143 q3 ∷
   re 140 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 142 q3 ∷
   re 139 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 141 q3 ∷
   re 138 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 140 q3 ∷
   re 137 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 139 q3 ∷
   re 136 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 138 q3 ∷
   re 135 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 137 q3 ∷
   re 134 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 136 q3 ∷
   re 133 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 135 q3 ∷
   re 132 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 134 q3 ∷
   re 131 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 133 q3 ∷
   re 130 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 132 q3 ∷
   re 129 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 131 q3 ∷
   re 128 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 130 q3 ∷
   re 127 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 129 q3 ∷
   re 126 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 128 q3 ∷
   rw 125 q4 ∷
   re 124 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 126 q3 ∷
   re 123 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 125 q3 ∷
   re 122 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 124 q3 ∷
   re 121 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 123 q3 ∷
   re 120 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 122 q3 ∷
   re 119 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 121 q3 ∷
   re 118 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 120 q3 ∷
   re 117 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 119 q3 ∷
   rw 116 q6 ∷
   rw 115 q6 ∷
   rw 114 q5 ∷
   rw 113 q6 ∷
   rw 112 q6 ∷
   rw 111 q6 ∷
   rw 112 q7 ∷
   rw⁻ 111 q6 ∷
   rw⁻ 112 q6 ∷
   rw⁻ 113 q5 ∷
   rw⁻ 114 q6 ∷
   rw⁻ 115 q5 ∷
   rw⁻ 116 q5 ∷
   rw 119 q2 ∷
   re 117 3 (CX13 ∷ []) ∷
   rw 120 q2 ∷
   re 118 3 (CK30 ∷ []) ∷
   rw 119 q8 ∷
   rw 122 q2 ∷
   re 120 3 (CK30 ∷ []) ∷
   rw 121 q8 ∷
   rw 124 q2 ∷
   re 122 3 (CS03 ∷ []) ∷
   rw 125 q2 ∷
   re 123 3 (CS03 ∷ []) ∷
   rw 126 q2 ∷
   re 124 3 (CS03 ∷ []) ∷
   rw 127 q2 ∷
   re 125 3 (CK30 ∷ []) ∷
   rw 126 q8 ∷
   rw 129 q2 ∷
   re 127 3 (CS03 ∷ []) ∷
   rw 130 q2 ∷
   re 128 3 (CS03 ∷ []) ∷
   rw 131 q2 ∷
   re 129 3 (CS03 ∷ []) ∷
   rw 132 q2 ∷
   re 130 3 (CS03 ∷ []) ∷
   rw 133 q2 ∷
   re 131 3 (CS03 ∷ []) ∷
   rw 134 q2 ∷
   re 132 3 (CS03 ∷ []) ∷
   rw 135 q2 ∷
   re 133 3 (CX13 ∷ []) ∷
   rw 136 q2 ∷
   re 134 3 (CS03 ∷ []) ∷
   rw 137 q2 ∷
   re 135 3 (CS03 ∷ []) ∷
   rw 138 q2 ∷
   re 136 3 (CK30 ∷ []) ∷
   rw 139 q2 ∷
   re 137 3 (CS03 ∷ []) ∷
   rw 140 q2 ∷
   re 138 3 (CK30 ∷ []) ∷
   rw 141 q2 ∷
   re 139 3 (CK30 ∷ []) ∷
   rw⁻ 140 q6 ∷
   rw⁻ 141 q6 ∷
   rw⁻ 142 q6 ∷
   rw⁻ 143 q5 ∷
   rw⁻ 144 q6 ∷
   rw⁻ 145 q6 ∷
   rw 148 q2 ∷
   re 146 3 (CX13 ∷ []) ∷
   rw 149 q2 ∷
   re 147 3 (CS03 ∷ []) ∷
   rw 150 q2 ∷
   re 148 3 (CS03 ∷ []) ∷
   rw 151 q2 ∷
   re 149 3 (CS03 ∷ []) ∷
   rw 152 q2 ∷
   re 150 3 (CS03 ∷ []) ∷
   rw 153 q2 ∷
   re 151 3 (CS03 ∷ []) ∷
   rw 154 q2 ∷
   re 152 3 (CS03 ∷ []) ∷
   rw 155 q2 ∷
   re 153 3 (CK30 ∷ []) ∷
   rw 154 q8 ∷
   rw 157 q2 ∷
   re 155 3 (CS03 ∷ []) ∷
   rw 158 q2 ∷
   re 156 3 (CS03 ∷ []) ∷
   rw 159 q2 ∷
   re 157 3 (CS03 ∷ []) ∷
   rw 160 q2 ∷
   re 158 3 (CS03 ∷ []) ∷
   rw 161 q2 ∷
   re 159 3 (CS03 ∷ []) ∷
   rw 162 q2 ∷
   re 160 3 (CS03 ∷ []) ∷
   rw 163 q2 ∷
   re 161 3 (CS03 ∷ []) ∷
   rw 164 q2 ∷
   re 162 3 (CS03 ∷ []) ∷
   rw 165 q2 ∷
   re 163 3 (CS03 ∷ []) ∷
   rw 166 q2 ∷
   re 164 3 (CX13 ∷ []) ∷
   rw 167 q2 ∷
   re 165 3 (CS03 ∷ []) ∷
   rw 168 q2 ∷
   re 166 3 (CS03 ∷ []) ∷
   rw 169 q2 ∷
   re 167 3 (CS03 ∷ []) ∷
   rw 170 q2 ∷
   re 168 3 (CK30 ∷ []) ∷
   rw 171 q2 ∷
   re 169 3 (CS03 ∷ []) ∷
   rw 172 q2 ∷
   re 170 3 (CS03 ∷ []) ∷
   rw 171 q3 ∷
   rw⁻ 31 q9 ∷
   rw 0 q10 ∷
   rw⁻ 29 q11 ∷ []) Eq.refl
