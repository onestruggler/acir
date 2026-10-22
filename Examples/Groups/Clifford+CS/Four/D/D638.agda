{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD638 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D638 (W : Ws) (Sᴰ : SD638) where

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
  lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-III-units-1 : St 1536
  lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-III-units-1 = pickᴰ 0 Sᴰ
  lem-Bar⟨SSKSKK13-⟶0⟩-passes-factors-of-X0-X1-X2-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X0-X1-X2 : St 1537
  lem-Bar⟨SSKSKK13-⟶0⟩-passes-factors-of-X0-X1-X2-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X0-X1-X2 = pickᴰ 1 Sᴰ
  lem-Bar⟨SSKSKK13-⟶0⟩-passes-factors-of-X1-X2-X3-TOFF312-X1-X2-X3 : St 1538
  lem-Bar⟨SSKSKK13-⟶0⟩-passes-factors-of-X1-X2-X3-TOFF312-X1-X2-X3 = pickᴰ 2 Sᴰ
  lem-pass-X0-TOFF103-X0-vs-X3-TOFF123-X3 : St 1539
  lem-pass-X0-TOFF103-X0-vs-X3-TOFF123-X3 = pickᴰ 3 Sᴰ
  lem-pass-X0-X2-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X0-X2-vs-X1-TOFF312-X1 : St 1540
  lem-pass-X0-X2-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X0-X2-vs-X1-TOFF312-X1 = pickᴰ 4 Sᴰ
  lem-pass-X0-X3-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X0-X3-vs-X1-TOFF312-X1 : St 1541
  lem-pass-X0-X3-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X0-X3-vs-X1-TOFF312-X1 = pickᴰ 5 Sᴰ

private
  q1 : Eqn
  q1 = wE 1906 W
  q2 : Eqn
  q2 = sE 1536 lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-III-units-1
  q3 : Eqn
  q3 = wE 1907 W

-- pass [CK32 S3 CK32 S3 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CX30 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 S0 S0 S0 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 S0 S0 S0 CK02 S0 S0 S0 S0 CK02 S0 CX30 CK02 S0 CK02 S0 CS02 CS02 CS02 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02] [X3 TOFF123 X3]: 3 steps
lem-pass-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-vs-X3-TOFF123-X3 : ⟪ (CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff123 ∷ X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-vs-X3-TOFF123-X3 = derive (CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) (X3 ∷ Toff123 ∷ X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ [])
  (rw 74 q1 ∷
   rw 0 q2 ∷
   rw 0 q3 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = wE 1776 W
  q5 : Eqn
  q5 = wE 1 W
  q6 : Eqn
  q6 = wE 173 W
  q7 : Eqn
  q7 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q8 : Eqn
  q8 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q9 : Eqn
  q9 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q10 : Eqn
  q10 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q11 : Eqn
  q11 = wE 3 W
  q12 : Eqn
  q12 = wE 196 W
  q13 : Eqn
  q13 = wE 1924 W
  q14 : Eqn
  q14 = wE 175 W
  q15 : Eqn
  q15 = sE 1539 lem-pass-X0-TOFF103-X0-vs-X3-TOFF123-X3
  q16 : Eqn
  q16 = wE 1925 W
  q17 : Eqn
  q17 = wE 1779 W

-- pass [TOFF123] [X0 X3 TOFF103 X0 X3]: 133 steps
lem-pass-TOFF123-vs-X0-X3-TOFF103-X0-X3 : ⟪ (Toff123 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ Toff123 ∷ []) ⟫ʷ
lem-pass-TOFF123-vs-X0-X3-TOFF103-X0-X3 = derive (Toff123 ∷ X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff103 ∷ X0 ∷ X3 ∷ Toff123 ∷ [])
  (rw 0 q4 ∷
   rw 10 q5 ∷
   rw 9 q6 ∷
   rw 8 q7 ∷
   re 7 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 8 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 7 q8 ∷
   rw 10 q5 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 9 q9 ∷
   rw 12 q5 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q9 ∷
   rw 14 q5 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw⁻ 13 q8 ∷
   rw⁻ 14 q10 ∷
   rw 15 q11 ∷
   rw 14 q10 ∷
   rw 13 q8 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q11 ∷
   rw 11 q9 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q11 ∷
   rw 9 q9 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q11 ∷
   rw 7 q8 ∷
   rw 8 q12 ∷
   re 8 8 (Toff102 ∷ []) ∷
   rw 6 q6 ∷
   rw 5 q7 ∷
   rw 4 q6 ∷
   rw 5 q13 ∷
   rw⁻ 4 q7 ∷
   re 6 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 5 q8 ∷
   rw 8 q5 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q9 ∷
   rw 10 q5 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q9 ∷
   rw 12 q5 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 q8 ∷
   rw⁻ 12 q10 ∷
   rw 5 q5 ∷
   rw⁻ 6 q8 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q11 ∷
   rw⁻ 8 q9 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q11 ∷
   rw⁻ 10 q9 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q11 ∷
   rw⁻ 12 q8 ∷
   rw⁻ 13 q10 ∷
   rw 6 q12 ∷
   re 6 8 (Toff102 ∷ []) ∷
   re 5 3 (Toff103 ∷ []) ∷
   rw⁻ 6 q7 ∷
   rw 7 q14 ∷
   rw 8 q11 ∷
   rw⁻ 1 q15 ∷
   rw 4 q5 ∷
   rw 3 q7 ∷
   re 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 q8 ∷
   rw 5 q5 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q9 ∷
   rw 7 q5 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q9 ∷
   rw 9 q5 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q8 ∷
   rw⁻ 9 q10 ∷
   rw 10 q11 ∷
   rw 9 q10 ∷
   rw 8 q8 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q11 ∷
   rw 6 q9 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q11 ∷
   rw 4 q9 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q11 ∷
   rw 2 q8 ∷
   rw 3 q12 ∷
   re 3 8 (Toff102 ∷ []) ∷
   rw 1 q7 ∷
   rw 0 q6 ∷
   rw 1 q16 ∷
   rw⁻ 0 q7 ∷
   rw 1 q14 ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 q8 ∷
   rw 5 q5 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q9 ∷
   rw 7 q5 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q9 ∷
   rw 9 q5 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q8 ∷
   rw⁻ 9 q10 ∷
   rw 2 q5 ∷
   rw⁻ 3 q8 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q11 ∷
   rw⁻ 5 q9 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q11 ∷
   rw⁻ 7 q9 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q11 ∷
   rw⁻ 9 q8 ∷
   rw⁻ 10 q10 ∷
   rw 3 q12 ∷
   re 3 8 (Toff102 ∷ []) ∷
   re 2 3 (Toff103 ∷ []) ∷
   rw⁻ 3 q7 ∷
   rw 4 q14 ∷
   rw 5 q14 ∷
   rw 6 q11 ∷
   rw 5 q17 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = wE 1650 W
  q19 : Eqn
  q19 = sE 1537 lem-Bar⟨SSKSKK13-⟶0⟩-passes-factors-of-X0-X1-X2-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X0-X1-X2
  q20 : Eqn
  q20 = wE 1651 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [X0 X1 X2 CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20 X0 X1 X2]: 3 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X1-X2-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X0-X1-X2 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X1 ∷ X2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X1-X2-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X0-X1-X2 = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X1 ∷ X2 ∷ []) (X0 ∷ X1 ∷ X2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X1 ∷ X2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 29 q18 ∷
   rw 0 q19 ∷
   rw 0 q20 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = wE 1926 W
  q22 : Eqn
  q22 = sE 1538 lem-Bar⟨SSKSKK13-⟶0⟩-passes-factors-of-X1-X2-X3-TOFF312-X1-X2-X3
  q23 : Eqn
  q23 = wE 1927 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [X1 X2 X3 TOFF312 X1 X2 X3]: 3 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-X2-X3-TOFF312-X1-X2-X3 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X1 ∷ X2 ∷ X3 ∷ Toff312 ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ X3 ∷ Toff312 ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-X2-X3-TOFF312-X1-X2-X3 = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X1 ∷ X2 ∷ X3 ∷ Toff312 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ X3 ∷ Toff312 ∷ X1 ∷ X2 ∷ X3 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 29 q21 ∷
   rw 0 q22 ∷
   rw 0 q23 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = wE 1800 W
  q25 : Eqn
  q25 = wE 1928 W
  q26 : Eqn
  q26 = sE 1540 lem-pass-X0-X2-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X0-X2-vs-X1-TOFF312-X1
  q27 : Eqn
  q27 = wE 1929 W
  q28 : Eqn
  q28 = wE 1803 W

-- pass [TOFF312] [X0 X1 X2 CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20 X0 X1 X2]: 5 steps
lem-pass-TOFF312-vs-X0-X1-X2-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X0-X1-X2 : ⟪ (Toff312 ∷ X0 ∷ X1 ∷ X2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X1 ∷ X2 ∷ Toff312 ∷ []) ⟫ʷ
lem-pass-TOFF312-vs-X0-X1-X2-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X0-X1-X2 = derive (Toff312 ∷ X0 ∷ X1 ∷ X2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X1 ∷ X2 ∷ []) (X0 ∷ X1 ∷ X2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X1 ∷ X2 ∷ Toff312 ∷ [])
  (rw 0 q24 ∷
   rw 4 q25 ∷
   rw⁻ 1 q26 ∷
   rw 0 q27 ∷
   rw 35 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q30 : Eqn
  q30 = wE 464 W
  q31 : Eqn
  q31 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q32 : Eqn
  q32 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q33 : Eqn
  q33 = wE 1930 W
  q34 : Eqn
  q34 = wE 151 W
  q35 : Eqn
  q35 = sE 1541 lem-pass-X0-X3-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X0-X3-vs-X1-TOFF312-X1
  q36 : Eqn
  q36 = wE 1931 W

-- pass [TOFF312] [X0 X1 X3 CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03 X0 X1 X3]: 253 steps
lem-pass-TOFF312-vs-X0-X1-X3-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X0-X1-X3 : ⟪ (Toff312 ∷ X0 ∷ X1 ∷ X3 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X1 ∷ X3 ∷ Toff312 ∷ []) ⟫ʷ
lem-pass-TOFF312-vs-X0-X1-X3-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X0-X1-X3 = derive (Toff312 ∷ X0 ∷ X1 ∷ X3 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X1 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X3 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X1 ∷ X3 ∷ Toff312 ∷ [])
  (rw 0 q24 ∷
   rw 42 q5 ∷
   rw 41 q6 ∷
   rw 40 q29 ∷
   rw 39 q7 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q11 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q11 ∷
   re 36 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 38 q11 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q11 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q11 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q11 ∷
   re 32 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 34 q11 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q11 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q11 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q11 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q11 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q11 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q11 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q11 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q11 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q11 ∷
   rw 22 q30 ∷
   re 21 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 23 q11 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q11 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q11 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q11 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q11 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q11 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q11 ∷
   re 14 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 16 q11 ∷
   rw 13 q31 ∷
   rw 12 q31 ∷
   rw 11 q32 ∷
   rw 10 q31 ∷
   rw 9 q31 ∷
   rw 8 q31 ∷
   rw 7 q6 ∷
   rw 6 q29 ∷
   rw 5 q7 ∷
   rw 4 q29 ∷
   rw 5 q33 ∷
   rw⁻ 4 q7 ∷
   rw 5 q14 ∷
   rw⁻ 6 q31 ∷
   rw⁻ 7 q31 ∷
   rw⁻ 8 q31 ∷
   rw⁻ 9 q32 ∷
   rw⁻ 10 q31 ∷
   rw⁻ 11 q31 ∷
   rw 14 q5 ∷
   re 12 3 (CX13 ∷ []) ∷
   rw 15 q5 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 16 q5 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 17 q5 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 18 q5 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 19 q5 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 20 q5 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 21 q5 ∷
   re 19 3 (CK30 ∷ []) ∷
   rw 20 q34 ∷
   rw 23 q5 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 24 q5 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 25 q5 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 26 q5 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 27 q5 ∷
   re 25 3 (CS03 ∷ []) ∷
   rw 28 q5 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 29 q5 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 30 q5 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 31 q5 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 32 q5 ∷
   re 30 3 (CX13 ∷ []) ∷
   rw 33 q5 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 34 q5 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 35 q5 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 36 q5 ∷
   re 34 3 (CK30 ∷ []) ∷
   rw 37 q5 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 38 q5 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw⁻ 37 q7 ∷
   rw 38 q14 ∷
   rw⁻ 39 q29 ∷
   rw 40 q11 ∷
   rw⁻ 1 q35 ∷
   rw 36 q5 ∷
   rw 35 q6 ∷
   rw 34 q7 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q11 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q11 ∷
   re 31 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 33 q11 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q11 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q11 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q11 ∷
   re 27 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 29 q11 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q11 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q11 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q11 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q11 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q11 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q11 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q11 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q11 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q11 ∷
   rw 17 q30 ∷
   re 16 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 18 q11 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q11 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q11 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q11 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q11 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q11 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q11 ∷
   re 9 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 11 q11 ∷
   rw 8 q31 ∷
   rw 7 q31 ∷
   rw 6 q32 ∷
   rw 5 q31 ∷
   rw 4 q31 ∷
   rw 3 q31 ∷
   rw 2 q6 ∷
   rw 1 q7 ∷
   rw 0 q29 ∷
   rw 1 q36 ∷
   rw⁻ 0 q7 ∷
   rw⁻ 1 q29 ∷
   rw 2 q14 ∷
   rw⁻ 3 q31 ∷
   rw⁻ 4 q31 ∷
   rw⁻ 5 q31 ∷
   rw⁻ 6 q32 ∷
   rw⁻ 7 q31 ∷
   rw⁻ 8 q31 ∷
   rw 11 q5 ∷
   re 9 3 (CX13 ∷ []) ∷
   rw 12 q5 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 13 q5 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 14 q5 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 15 q5 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 16 q5 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 17 q5 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 18 q5 ∷
   re 16 3 (CK30 ∷ []) ∷
   rw 17 q34 ∷
   rw 20 q5 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 21 q5 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 22 q5 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 23 q5 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 24 q5 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 25 q5 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 26 q5 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 27 q5 ∷
   re 25 3 (CS03 ∷ []) ∷
   rw 28 q5 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 29 q5 ∷
   re 27 3 (CX13 ∷ []) ∷
   rw 30 q5 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 31 q5 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 32 q5 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 33 q5 ∷
   re 31 3 (CK30 ∷ []) ∷
   rw 34 q5 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 35 q5 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw⁻ 34 q7 ∷
   rw⁻ 35 q29 ∷
   rw 36 q14 ∷
   rw⁻ 37 q29 ∷
   rw 38 q11 ∷
   rw 37 q28 ∷ []) Eq.refl
