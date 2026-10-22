{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD594 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D594 (W : Ws) (Sᴰ : SD594) where

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
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'01-⟶3⟩-passes-II/IV-units-2-1 : St 1082
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'01-⟶3⟩-passes-II/IV-units-2-1 = pickᴰ 0 Sᴰ
  lem-Bar⟨SSKSKK02-⟶3⟩-passes-groups-of-WBar⟨SSKSKK~01-⟶3⟩ : St 1083
  lem-Bar⟨SSKSKK02-⟶3⟩-passes-groups-of-WBar⟨SSKSKK~01-⟶3⟩ = pickᴰ 1 Sᴰ
  lem-Bar⟨SSKSKK03-⟶2⟩-passes-II/IV-units-3-1 : St 1084
  lem-Bar⟨SSKSKK03-⟶2⟩-passes-II/IV-units-3-1 = pickᴰ 2 Sᴰ
  lem-Bar⟨SSSKSS03-⟶2⟩-passes-II/IV-units-3-1 : St 1085
  lem-Bar⟨SSSKSS03-⟶2⟩-passes-II/IV-units-3-1 = pickᴰ 3 Sᴰ

private
  q1 : Eqn
  q1 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q2 : Eqn
  q2 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q3 : Eqn
  q3 = eqn (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) (wn 335 W)
  q4 : Eqn
  q4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q5 : Eqn
  q5 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q6 : Eqn
  q6 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q7 : Eqn
  q7 = eqn (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ []) (wn 1294 W)
  q8 : Eqn
  q8 = eqn (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (wn 368 W)
  q9 : Eqn
  q9 = eqn (X0 ∷ Toff201 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CZ12 ∷ CS02 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ []) (wn 1723 W)
  q10 : Eqn
  q10 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q11 : Eqn
  q11 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q12 : Eqn
  q12 = eqn (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X0 ∷ CK03 ∷ X0 ∷ CZ13 ∷ CS03 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CZ13 ∷ CS03 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ []) (lem-Bar⟨SSKSKK03-⟶2⟩-passes-II/IV-units-3-1)
  q13 : Eqn
  q13 = eqn (X0 ∷ CK02 ∷ X0 ∷ CZ12 ∷ CS02 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ []) (X0 ∷ Toff201 ∷ X0 ∷ []) (wn 1724 W)
  q14 : Eqn
  q14 = eqn (Sw23 ∷ K3 ∷ []) (K2 ∷ Sw23 ∷ []) (wn 336 W)

-- pass [CS02 CS02 CK02 CS02 CK02 CK02 CX03 CK32 S3 CK32 S3 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CK32 CS23 CK32 CK32] [X0 TOFF301 X0]: 101 steps
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-TOFF301-X0 : ⟪ (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X0 ∷ Toff301 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff301 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-TOFF301-X0 = derive (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X0 ∷ Toff301 ∷ X0 ∷ []) (X0 ∷ Toff301 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ [])
  (rw 32 q1 ∷
   rw 31 q2 ∷
   re 30 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 31 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 30 q3 ∷
   rw 33 q1 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw⁻ 32 q4 ∷
   rw 35 q1 ∷
   re 33 3 (CS13⁻ ∷ []) ∷
   rw⁻ 34 q4 ∷
   rw 37 q1 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 36 q3 ∷
   rw⁻ 37 q5 ∷
   rw 38 q6 ∷
   rw 37 q5 ∷
   rw 36 q7 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q6 ∷
   rw 34 q4 ∷
   re 33 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 35 q6 ∷
   rw 32 q4 ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q6 ∷
   rw 30 q7 ∷
   rw 31 q8 ∷
   re 31 8 (Toff201 ∷ []) ∷
   rw 29 q2 ∷
   rw 30 q9 ∷
   rw⁻ 29 q2 ∷
   rw 32 q1 ∷
   re 30 3 (CK03 ∷ []) ∷
   rw⁻ 31 q2 ∷
   rw 34 q1 ∷
   re 32 3 (CZ13 ∷ []) ∷
   rw 35 q1 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw⁻ 34 q10 ∷
   rw 37 q1 ∷
   re 35 3 (CX31 ∷ []) ∷
   rw⁻ 36 q11 ∷
   rw 39 q1 ∷
   re 37 3 (CX31 ∷ []) ∷
   rw⁻ 38 q2 ∷
   rw 41 q1 ∷
   re 39 3 (CK03⁻ ∷ []) ∷
   rw⁻ 40 q2 ∷
   rw 41 q6 ∷
   rw 0 q12 ∷
   rw 12 q1 ∷
   rw 11 q2 ∷
   re 10 1 (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   rw 9 q2 ∷
   re 8 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw 7 q11 ∷
   re 6 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q10 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   re 3 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 2 q2 ∷
   re 1 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q2 ∷
   rw 1 q13 ∷
   rw⁻ 0 q2 ∷
   re 2 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 1 q1 ∷
   rw 2 q14 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 8 q14 ∷
   rw⁻ 9 q5 ∷
   rw 2 q8 ∷
   re 2 8 (Toff201 ∷ []) ∷
   re 1 3 (Toff301 ∷ []) ∷
   rw⁻ 2 q2 ∷
   rw 3 q6 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ CK03 ∷ X0 ∷ CZ13 ∷ CS03 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CZ13 ∷ CS03 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ X0 ∷ CK03⁻ ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (lem-Bar⟨SSSKSS03-⟶2⟩-passes-II/IV-units-3-1)

-- pass [CS02 CS02 CS02 CK02 CS02 CS02 CX03 CS23 CS23 CS23 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CS23 CK32 CS23 CS23] [X0 TOFF301 X0]: 101 steps
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-TOFF301-X0 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ Toff301 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff301 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-TOFF301-X0 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ X0 ∷ Toff301 ∷ X0 ∷ []) (X0 ∷ Toff301 ∷ X0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ [])
  (rw 34 q1 ∷
   rw 33 q2 ∷
   re 32 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 33 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 32 q3 ∷
   rw 35 q1 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw⁻ 34 q4 ∷
   rw 37 q1 ∷
   re 35 3 (CS13⁻ ∷ []) ∷
   rw⁻ 36 q4 ∷
   rw 39 q1 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 38 q3 ∷
   rw⁻ 39 q5 ∷
   rw 40 q6 ∷
   rw 39 q5 ∷
   rw 38 q7 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q6 ∷
   rw 36 q4 ∷
   re 35 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 37 q6 ∷
   rw 34 q4 ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q6 ∷
   rw 32 q7 ∷
   rw 33 q8 ∷
   re 33 8 (Toff201 ∷ []) ∷
   rw 31 q2 ∷
   rw 32 q9 ∷
   rw⁻ 31 q2 ∷
   rw 34 q1 ∷
   re 32 3 (CK03 ∷ []) ∷
   rw⁻ 33 q2 ∷
   rw 36 q1 ∷
   re 34 3 (CZ13 ∷ []) ∷
   rw 37 q1 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw⁻ 36 q10 ∷
   rw 39 q1 ∷
   re 37 3 (CX31 ∷ []) ∷
   rw⁻ 38 q11 ∷
   rw 41 q1 ∷
   re 39 3 (CX31 ∷ []) ∷
   rw⁻ 40 q2 ∷
   rw 43 q1 ∷
   re 41 3 (CK03⁻ ∷ []) ∷
   rw⁻ 42 q2 ∷
   rw 43 q6 ∷
   rw 0 q15 ∷
   rw 12 q1 ∷
   rw 11 q2 ∷
   re 10 1 (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   rw 9 q2 ∷
   re 8 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw 7 q11 ∷
   re 6 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q10 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   re 3 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 2 q2 ∷
   re 1 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q2 ∷
   rw 1 q13 ∷
   rw⁻ 0 q2 ∷
   re 2 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 1 q1 ∷
   rw 2 q14 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 8 q14 ∷
   rw⁻ 9 q5 ∷
   rw 2 q8 ∷
   re 2 8 (Toff201 ∷ []) ∷
   re 1 3 (Toff301 ∷ []) ∷
   rw⁻ 2 q2 ∷
   rw 3 q6 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q17 : Eqn
  q17 = eqn (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ []) (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ CX01 ∷ X0 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (wn 1431 W)
  q18 : Eqn
  q18 = eqn (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) (lem-Bar⟨SSKSKK02-⟶3⟩-passes-groups-of-WBar⟨SSKSKK~01-⟶3⟩)
  q19 : Eqn
  q19 = eqn (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ X0 ∷ CX01 ∷ X0 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX01 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX01 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X0 ∷ []) (wn 1432 W)

-- pass [CS03 CS03 CK03 CS03 CK03 CK03 CX02 CK23 S2 CK23 S2 CS23 CS23 CS23 CK23 S2 CS23 CS23 CS23 CS23 CS23 CS23 CX02 CS23 CS23 CK23 CS23 CK23 CK23] [X0 CS03 CS03 CK03 CS03 CK03 CK03 CX01 CK13 S1 CK13 S1 CS13 CS13 CS13 CK13 S1 CS13 CS13 CS13 CS13 CS13 CS13 CX01 CS13 CS13 CK13 CS13 CK13 CK13 X0]: 235 steps
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-X0-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-X0 : ⟪ (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-X0-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-X0 = derive (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ [])
  (rw 60 q1 ∷
   rw 59 q2 ∷
   re 58 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 60 q6 ∷
   re 57 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 59 q6 ∷
   re 56 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 58 q6 ∷
   re 55 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 57 q6 ∷
   re 54 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 56 q6 ∷
   re 53 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 55 q6 ∷
   rw 52 q4 ∷
   re 51 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 53 q6 ∷
   re 50 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 52 q6 ∷
   re 49 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 51 q6 ∷
   re 48 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 50 q6 ∷
   re 47 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 49 q6 ∷
   re 46 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 48 q6 ∷
   rw 45 q16 ∷
   re 44 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 46 q6 ∷
   re 43 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 45 q6 ∷
   re 42 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 44 q6 ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q6 ∷
   rw 40 q16 ∷
   re 39 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 41 q6 ∷
   rw 38 q16 ∷
   re 37 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 39 q6 ∷
   rw 36 q4 ∷
   re 35 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 37 q6 ∷
   re 34 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 36 q6 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q6 ∷
   re 32 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 34 q6 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q6 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q6 ∷
   rw 29 q2 ∷
   rw 30 q17 ∷
   rw⁻ 29 q2 ∷
   rw 32 q1 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 33 q1 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 34 q1 ∷
   re 32 3 (CK03 ∷ []) ∷
   rw 35 q1 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 36 q1 ∷
   re 34 3 (CK03 ∷ []) ∷
   rw 37 q1 ∷
   re 35 3 (CK03 ∷ []) ∷
   rw⁻ 36 q2 ∷
   rw⁻ 37 q2 ∷
   rw⁻ 38 q4 ∷
   rw⁻ 39 q2 ∷
   rw 42 q1 ∷
   re 40 3 (CK13 ∷ []) ∷
   rw⁻ 41 q16 ∷
   rw 44 q1 ∷
   re 42 3 (CK13 ∷ []) ∷
   rw⁻ 43 q16 ∷
   rw 46 q1 ∷
   re 44 3 (CS13 ∷ []) ∷
   rw 47 q1 ∷
   re 45 3 (CS13 ∷ []) ∷
   rw 48 q1 ∷
   re 46 3 (CS13 ∷ []) ∷
   rw 49 q1 ∷
   re 47 3 (CK13 ∷ []) ∷
   rw⁻ 48 q16 ∷
   rw 51 q1 ∷
   re 49 3 (CS13 ∷ []) ∷
   rw 52 q1 ∷
   re 50 3 (CS13 ∷ []) ∷
   rw 53 q1 ∷
   re 51 3 (CS13 ∷ []) ∷
   rw 54 q1 ∷
   re 52 3 (CS13 ∷ []) ∷
   rw 55 q1 ∷
   re 53 3 (CS13 ∷ []) ∷
   rw 56 q1 ∷
   re 54 3 (CS13 ∷ []) ∷
   rw⁻ 55 q2 ∷
   rw⁻ 56 q4 ∷
   rw⁻ 57 q2 ∷
   rw 60 q1 ∷
   re 58 3 (CS13 ∷ []) ∷
   rw 61 q1 ∷
   re 59 3 (CS13 ∷ []) ∷
   rw 62 q1 ∷
   re 60 3 (CK13 ∷ []) ∷
   rw 63 q1 ∷
   re 61 3 (CS13 ∷ []) ∷
   rw 64 q1 ∷
   re 62 3 (CK13 ∷ []) ∷
   rw 65 q1 ∷
   re 63 3 (CK13 ∷ []) ∷
   rw 64 q6 ∷
   rw 0 q18 ∷
   rw 35 q1 ∷
   re 34 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 36 q6 ∷
   re 33 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 35 q6 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q6 ∷
   re 31 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 33 q6 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q6 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q6 ∷
   rw 28 q2 ∷
   rw 27 q4 ∷
   rw 26 q2 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q6 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q6 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q6 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q6 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q6 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q6 ∷
   rw 19 q16 ∷
   re 18 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 20 q6 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q6 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q6 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q6 ∷
   rw 14 q16 ∷
   re 13 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 15 q6 ∷
   rw 12 q16 ∷
   re 11 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 13 q6 ∷
   rw 10 q2 ∷
   rw 9 q4 ∷
   rw 8 q2 ∷
   rw 7 q2 ∷
   re 6 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   re 5 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   re 3 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q2 ∷
   rw 1 q19 ∷
   rw⁻ 0 q2 ∷
   rw 3 q1 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 4 q1 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 5 q1 ∷
   re 3 3 (CK03 ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CK03 ∷ []) ∷
   rw 8 q1 ∷
   re 6 3 (CK03 ∷ []) ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (CK13 ∷ []) ∷
   rw⁻ 9 q16 ∷
   rw 12 q1 ∷
   re 10 3 (CK13 ∷ []) ∷
   rw⁻ 11 q16 ∷
   rw 14 q1 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 15 q1 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 16 q1 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 17 q1 ∷
   re 15 3 (CK13 ∷ []) ∷
   rw⁻ 16 q16 ∷
   rw 19 q1 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw 20 q1 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 21 q1 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 22 q1 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 23 q1 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 24 q1 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw⁻ 23 q4 ∷
   rw 26 q1 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 27 q1 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 28 q1 ∷
   re 26 3 (CK13 ∷ []) ∷
   rw 29 q1 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 30 q1 ∷
   re 28 3 (CK13 ∷ []) ∷
   rw 31 q1 ∷
   re 29 3 (CK13 ∷ []) ∷
   rw⁻ 30 q2 ∷
   rw 31 q6 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = eqn (X0 ∷ Toff201 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CZ12 ∷ CS01 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ []) (wn 1721 W)
  q21 : Eqn
  q21 = eqn (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ X0 ∷ CK02 ∷ X0 ∷ CZ12 ∷ CS01 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CZ12 ∷ CS01 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'01-⟶3⟩-passes-II/IV-units-2-1)
  q22 : Eqn
  q22 = eqn (X0 ∷ CK02 ∷ X0 ∷ CZ12 ∷ CS01 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ []) (X0 ∷ Toff201 ∷ X0 ∷ []) (wn 1722 W)

-- pass [CS03 CS03 CK03 CS03 CK03 CK03 CX01 CK13 S1 CK13 S1 CS13 CS13 CS13 CK13 S1 CS13 CS13 CS13 CS13 CS13 CS13 CX01 CS13 CS13 CK13 CS13 CK13 CK13] [X0 TOFF201 X0]: 3 steps
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-X0-TOFF201-X0 : ⟪ (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ X0 ∷ Toff201 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff201 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-X0-TOFF201-X0 = derive (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ X0 ∷ Toff201 ∷ X0 ∷ []) (X0 ∷ Toff201 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  (rw 29 q20 ∷
   rw 0 q21 ∷
   rw 0 q22 ∷ []) Eq.refl
