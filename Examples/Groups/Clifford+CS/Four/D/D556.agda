{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD556 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D556 (W : Ws) (Sᴰ : SD556) where

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
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X2-X3-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-X2-X3 : St 949
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X2-X3-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-X2-X3 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q4 : Eqn
  q4 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q5 : Eqn
  q5 = wE 140 W
  q6 : Eqn
  q6 = wE 7 W
  q7 : Eqn
  q7 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q8 : Eqn
  q8 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q9 : Eqn
  q9 = wE 1587 W
  q10 : Eqn
  q10 = wE 29 W
  q11 : Eqn
  q11 = wE 139 W
  q12 : Eqn
  q12 = wE 27 W
  q13 : Eqn
  q13 = wE 142 W
  q14 : Eqn
  q14 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q15 : Eqn
  q15 = wE 31 W
  q16 : Eqn
  q16 = sE 949 lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X2-X3-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-X2-X3
  q17 : Eqn
  q17 = wE 137 W
  q18 : Eqn
  q18 = wE 76 W
  q19 : Eqn
  q19 = wE 1588 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 X3 CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30 X2 X3]: 717 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-X2-X3 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-X2-X3 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 62 q1 ∷
   rw⁻ 61 q2 ∷
   rw⁻ 60 q3 ∷
   re 59 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 61 q4 ∷
   rw 60 q5 ∷
   rw⁻ 59 q4 ∷
   re 60 3 (CK31 ∷ []) ∷
   re 58 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 60 q4 ∷
   rw 59 q5 ∷
   rw⁻ 58 q4 ∷
   re 59 3 (CK31 ∷ []) ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 59 q4 ∷
   rw 58 q6 ∷
   rw⁻ 57 q4 ∷
   re 58 3 (CS13 ∷ []) ∷
   re 56 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 58 q4 ∷
   rw 57 q5 ∷
   rw⁻ 56 q4 ∷
   re 57 3 (CK31 ∷ []) ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 57 q4 ∷
   rw 56 q6 ∷
   rw⁻ 55 q4 ∷
   re 56 3 (CS13 ∷ []) ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 56 q4 ∷
   rw 55 q6 ∷
   rw⁻ 54 q4 ∷
   re 55 3 (CS13 ∷ []) ∷
   rw⁻ 53 q7 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 54 q4 ∷
   rw 53 q6 ∷
   rw⁻ 52 q4 ∷
   re 53 3 (CS13 ∷ []) ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 53 q4 ∷
   rw 52 q6 ∷
   rw⁻ 51 q4 ∷
   re 52 3 (CS13 ∷ []) ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 52 q4 ∷
   rw 51 q6 ∷
   rw⁻ 50 q4 ∷
   re 51 3 (CS13 ∷ []) ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 51 q4 ∷
   rw 50 q6 ∷
   rw⁻ 49 q4 ∷
   re 50 3 (CS13 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 50 q4 ∷
   rw 49 q6 ∷
   rw⁻ 48 q4 ∷
   re 49 3 (CS13 ∷ []) ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q4 ∷
   rw 48 q6 ∷
   rw⁻ 47 q4 ∷
   re 48 3 (CS13 ∷ []) ∷
   rw⁻ 46 q8 ∷
   re 45 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 47 q4 ∷
   rw 46 q5 ∷
   rw⁻ 45 q4 ∷
   re 46 3 (CK31 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q4 ∷
   rw 45 q6 ∷
   rw⁻ 44 q4 ∷
   re 45 3 (CS13 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q4 ∷
   rw 44 q6 ∷
   rw⁻ 43 q4 ∷
   re 44 3 (CS13 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q4 ∷
   rw 43 q6 ∷
   rw⁻ 42 q4 ∷
   re 43 3 (CS13 ∷ []) ∷
   rw⁻ 41 q8 ∷
   re 40 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q4 ∷
   rw 41 q5 ∷
   rw⁻ 40 q4 ∷
   re 41 3 (CK31 ∷ []) ∷
   rw⁻ 39 q8 ∷
   re 38 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q4 ∷
   rw 39 q5 ∷
   rw⁻ 38 q4 ∷
   re 39 3 (CK31 ∷ []) ∷
   rw⁻ 37 q7 ∷
   rw 36 q5 ∷
   rw 35 q5 ∷
   rw 34 q6 ∷
   rw 33 q5 ∷
   rw 32 q6 ∷
   rw 31 q6 ∷
   rw⁻ 30 q2 ∷
   rw⁻ 29 q3 ∷
   rw 30 q9 ∷
   rw 29 q3 ∷
   rw 30 q10 ∷
   rw 31 q11 ∷
   rw 32 q12 ∷
   rw 33 q12 ∷
   rw 34 q3 ∷
   rw 35 q3 ∷
   rw 36 q13 ∷
   rw 37 q14 ∷
   rw 38 q13 ∷
   rw 39 q14 ∷
   rw 40 q12 ∷
   rw 41 q12 ∷
   rw 42 q12 ∷
   rw 43 q13 ∷
   rw 44 q14 ∷
   rw 45 q12 ∷
   rw 46 q12 ∷
   rw 47 q12 ∷
   rw 48 q12 ∷
   rw 49 q12 ∷
   rw 50 q12 ∷
   rw 51 q7 ∷
   re 53 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 52 q4 ∷
   rw 53 q12 ∷
   rw 54 q4 ∷
   re 52 3 (CS03 ∷ []) ∷
   re 54 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 53 q4 ∷
   rw 54 q12 ∷
   rw 55 q4 ∷
   re 53 3 (CS03 ∷ []) ∷
   re 55 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 54 q4 ∷
   rw 55 q12 ∷
   rw 56 q4 ∷
   re 54 3 (CS03 ∷ []) ∷
   re 56 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 55 q4 ∷
   rw 56 q12 ∷
   rw 57 q4 ∷
   re 55 3 (CS03 ∷ []) ∷
   re 57 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 56 q4 ∷
   rw 57 q12 ∷
   rw 58 q4 ∷
   re 56 3 (CS03 ∷ []) ∷
   re 58 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 57 q4 ∷
   rw 58 q12 ∷
   rw 59 q4 ∷
   re 57 3 (CS03 ∷ []) ∷
   re 59 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 58 q4 ∷
   rw 59 q12 ∷
   rw 60 q4 ∷
   re 58 3 (CS03 ∷ []) ∷
   re 60 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 59 q4 ∷
   rw 60 q12 ∷
   rw 61 q4 ∷
   re 59 3 (CS03 ∷ []) ∷
   re 61 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 60 q4 ∷
   rw 61 q12 ∷
   rw 62 q4 ∷
   re 60 3 (CS03 ∷ []) ∷
   re 62 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 61 q4 ∷
   rw 62 q12 ∷
   rw 63 q4 ∷
   re 61 3 (CS03 ∷ []) ∷
   re 63 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 62 q4 ∷
   rw 63 q12 ∷
   rw 64 q4 ∷
   re 62 3 (CS03 ∷ []) ∷
   re 64 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 63 q4 ∷
   rw 64 q12 ∷
   rw 65 q4 ∷
   re 63 3 (CS03 ∷ []) ∷
   re 65 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 64 q4 ∷
   rw 65 q12 ∷
   rw 66 q4 ∷
   re 64 3 (CS03 ∷ []) ∷
   re 66 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 65 q4 ∷
   rw 66 q12 ∷
   rw 67 q4 ∷
   re 65 3 (CS03 ∷ []) ∷
   re 67 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 66 q4 ∷
   rw 67 q12 ∷
   rw 68 q4 ∷
   re 66 3 (CS03 ∷ []) ∷
   re 68 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 67 q4 ∷
   rw 68 q12 ∷
   rw 69 q4 ∷
   re 67 3 (CS03 ∷ []) ∷
   re 69 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 68 q4 ∷
   rw 69 q12 ∷
   rw 70 q4 ∷
   re 68 3 (CS03 ∷ []) ∷
   re 70 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 69 q4 ∷
   rw 70 q12 ∷
   rw 71 q4 ∷
   re 69 3 (CS03 ∷ []) ∷
   rw 70 q8 ∷
   rw 71 q8 ∷
   rw 72 q8 ∷
   re 74 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 73 q4 ∷
   rw 74 q13 ∷
   rw 75 q4 ∷
   re 73 3 (CK30 ∷ []) ∷
   rw 74 q8 ∷
   re 76 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 75 q4 ∷
   rw 76 q12 ∷
   rw 77 q4 ∷
   re 75 3 (CS03 ∷ []) ∷
   re 77 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 76 q4 ∷
   rw 77 q12 ∷
   rw 78 q4 ∷
   re 76 3 (CS03 ∷ []) ∷
   re 78 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 77 q4 ∷
   rw 78 q12 ∷
   rw 79 q4 ∷
   re 77 3 (CS03 ∷ []) ∷
   re 79 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 78 q4 ∷
   rw 79 q12 ∷
   rw 80 q4 ∷
   re 78 3 (CS03 ∷ []) ∷
   re 80 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 79 q4 ∷
   rw 80 q12 ∷
   rw 81 q4 ∷
   re 79 3 (CS03 ∷ []) ∷
   re 81 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 80 q4 ∷
   rw 81 q12 ∷
   rw 82 q4 ∷
   re 80 3 (CS03 ∷ []) ∷
   re 82 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 81 q4 ∷
   rw 82 q12 ∷
   rw 83 q4 ∷
   re 81 3 (CS03 ∷ []) ∷
   re 83 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 82 q4 ∷
   rw 83 q12 ∷
   rw 84 q4 ∷
   re 82 3 (CS03 ∷ []) ∷
   re 84 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 83 q4 ∷
   rw 84 q12 ∷
   rw 85 q4 ∷
   re 83 3 (CS03 ∷ []) ∷
   rw 84 q8 ∷
   rw 85 q8 ∷
   rw 86 q8 ∷
   re 88 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 87 q4 ∷
   rw 88 q13 ∷
   rw 89 q4 ∷
   re 87 3 (CK30 ∷ []) ∷
   rw 88 q8 ∷
   rw 89 q8 ∷
   rw 90 q8 ∷
   rw 91 q8 ∷
   re 93 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 92 q4 ∷
   rw 93 q13 ∷
   rw 94 q4 ∷
   re 92 3 (CK30 ∷ []) ∷
   rw 93 q8 ∷
   rw 94 q7 ∷
   re 96 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 95 q4 ∷
   rw 96 q13 ∷
   rw 97 q4 ∷
   re 95 3 (CK30 ∷ []) ∷
   rw 96 q8 ∷
   re 98 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 97 q4 ∷
   rw 98 q13 ∷
   rw 99 q4 ∷
   re 97 3 (CK30 ∷ []) ∷
   rw 98 q8 ∷
   re 100 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 99 q4 ∷
   rw 100 q12 ∷
   rw 101 q4 ∷
   re 99 3 (CS03 ∷ []) ∷
   re 101 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 100 q4 ∷
   rw 101 q12 ∷
   rw 102 q4 ∷
   re 100 3 (CS03 ∷ []) ∷
   re 102 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 101 q4 ∷
   rw 102 q12 ∷
   rw 103 q4 ∷
   re 101 3 (CS03 ∷ []) ∷
   re 103 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 102 q4 ∷
   rw 103 q13 ∷
   rw 104 q4 ∷
   re 102 3 (CK30 ∷ []) ∷
   rw 103 q8 ∷
   re 105 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 104 q4 ∷
   rw 105 q12 ∷
   rw 106 q4 ∷
   re 104 3 (CS03 ∷ []) ∷
   re 106 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 105 q4 ∷
   rw 106 q12 ∷
   rw 107 q4 ∷
   re 105 3 (CS03 ∷ []) ∷
   re 107 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 106 q4 ∷
   rw 107 q12 ∷
   rw 108 q4 ∷
   re 106 3 (CS03 ∷ []) ∷
   re 108 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 107 q4 ∷
   rw 108 q12 ∷
   rw 109 q4 ∷
   re 107 3 (CS03 ∷ []) ∷
   re 109 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 108 q4 ∷
   rw 109 q12 ∷
   rw 110 q4 ∷
   re 108 3 (CS03 ∷ []) ∷
   re 110 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 109 q4 ∷
   rw 110 q12 ∷
   rw 111 q4 ∷
   re 109 3 (CS03 ∷ []) ∷
   rw 110 q3 ∷
   rw 111 q15 ∷
   rw 0 q16 ∷
   rw 82 q1 ∷
   rw⁻ 81 q3 ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 82 q4 ∷
   rw 81 q6 ∷
   rw⁻ 80 q4 ∷
   re 81 3 (CS13 ∷ []) ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 81 q4 ∷
   rw 80 q6 ∷
   rw⁻ 79 q4 ∷
   re 80 3 (CS13 ∷ []) ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 80 q4 ∷
   rw 79 q6 ∷
   rw⁻ 78 q4 ∷
   re 79 3 (CS13 ∷ []) ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 79 q4 ∷
   rw 78 q6 ∷
   rw⁻ 77 q4 ∷
   re 78 3 (CS13 ∷ []) ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 78 q4 ∷
   rw 77 q6 ∷
   rw⁻ 76 q4 ∷
   re 77 3 (CS13 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 77 q4 ∷
   rw 76 q6 ∷
   rw⁻ 75 q4 ∷
   re 76 3 (CS13 ∷ []) ∷
   rw⁻ 74 q8 ∷
   re 73 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 75 q4 ∷
   rw 74 q5 ∷
   rw⁻ 73 q4 ∷
   re 74 3 (CK31 ∷ []) ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 74 q4 ∷
   rw 73 q6 ∷
   rw⁻ 72 q4 ∷
   re 73 3 (CS13 ∷ []) ∷
   re 71 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 73 q4 ∷
   rw 72 q6 ∷
   rw⁻ 71 q4 ∷
   re 72 3 (CS13 ∷ []) ∷
   re 70 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 72 q4 ∷
   rw 71 q6 ∷
   rw⁻ 70 q4 ∷
   re 71 3 (CS13 ∷ []) ∷
   rw⁻ 69 q8 ∷
   re 68 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 70 q4 ∷
   rw 69 q5 ∷
   rw⁻ 68 q4 ∷
   re 69 3 (CK31 ∷ []) ∷
   rw⁻ 67 q8 ∷
   re 66 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 68 q4 ∷
   rw 67 q5 ∷
   rw⁻ 66 q4 ∷
   re 67 3 (CK31 ∷ []) ∷
   rw⁻ 65 q7 ∷
   rw⁻ 64 q8 ∷
   re 63 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 65 q4 ∷
   rw 64 q5 ∷
   rw⁻ 63 q4 ∷
   re 64 3 (CK31 ∷ []) ∷
   rw⁻ 62 q8 ∷
   rw⁻ 61 q8 ∷
   rw⁻ 60 q8 ∷
   rw⁻ 59 q8 ∷
   re 58 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 60 q4 ∷
   rw 59 q5 ∷
   rw⁻ 58 q4 ∷
   re 59 3 (CK31 ∷ []) ∷
   rw⁻ 57 q8 ∷
   rw⁻ 56 q8 ∷
   rw⁻ 55 q8 ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 56 q4 ∷
   rw 55 q6 ∷
   rw⁻ 54 q4 ∷
   re 55 3 (CS13 ∷ []) ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 55 q4 ∷
   rw 54 q6 ∷
   rw⁻ 53 q4 ∷
   re 54 3 (CS13 ∷ []) ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 54 q4 ∷
   rw 53 q6 ∷
   rw⁻ 52 q4 ∷
   re 53 3 (CS13 ∷ []) ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 53 q4 ∷
   rw 52 q6 ∷
   rw⁻ 51 q4 ∷
   re 52 3 (CS13 ∷ []) ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 52 q4 ∷
   rw 51 q6 ∷
   rw⁻ 50 q4 ∷
   re 51 3 (CS13 ∷ []) ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 51 q4 ∷
   rw 50 q6 ∷
   rw⁻ 49 q4 ∷
   re 50 3 (CS13 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 50 q4 ∷
   rw 49 q6 ∷
   rw⁻ 48 q4 ∷
   re 49 3 (CS13 ∷ []) ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q4 ∷
   rw 48 q6 ∷
   rw⁻ 47 q4 ∷
   re 48 3 (CS13 ∷ []) ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q4 ∷
   rw 47 q6 ∷
   rw⁻ 46 q4 ∷
   re 47 3 (CS13 ∷ []) ∷
   rw⁻ 45 q8 ∷
   re 44 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q4 ∷
   rw 45 q5 ∷
   rw⁻ 44 q4 ∷
   re 45 3 (CK31 ∷ []) ∷
   rw⁻ 43 q8 ∷
   rw⁻ 42 q8 ∷
   rw⁻ 41 q8 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q4 ∷
   rw 41 q6 ∷
   rw⁻ 40 q4 ∷
   re 41 3 (CS13 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q4 ∷
   rw 40 q6 ∷
   rw⁻ 39 q4 ∷
   re 40 3 (CS13 ∷ []) ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q4 ∷
   rw 39 q6 ∷
   rw⁻ 38 q4 ∷
   re 39 3 (CS13 ∷ []) ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q4 ∷
   rw 38 q6 ∷
   rw⁻ 37 q4 ∷
   re 38 3 (CS13 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q4 ∷
   rw 37 q6 ∷
   rw⁻ 36 q4 ∷
   re 37 3 (CS13 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q4 ∷
   rw 36 q6 ∷
   rw⁻ 35 q4 ∷
   re 36 3 (CS13 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q4 ∷
   rw 35 q6 ∷
   rw⁻ 34 q4 ∷
   re 35 3 (CS13 ∷ []) ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q4 ∷
   rw 34 q6 ∷
   rw⁻ 33 q4 ∷
   re 34 3 (CS13 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q4 ∷
   rw 33 q6 ∷
   rw⁻ 32 q4 ∷
   re 33 3 (CS13 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q4 ∷
   rw 32 q6 ∷
   rw⁻ 31 q4 ∷
   re 32 3 (CS13 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q4 ∷
   rw 31 q6 ∷
   rw⁻ 30 q4 ∷
   re 31 3 (CS13 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q4 ∷
   rw 30 q6 ∷
   rw⁻ 29 q4 ∷
   re 30 3 (CS13 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q4 ∷
   rw 29 q6 ∷
   rw⁻ 28 q4 ∷
   re 29 3 (CS13 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q4 ∷
   rw 28 q6 ∷
   rw⁻ 27 q4 ∷
   re 28 3 (CS13 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q4 ∷
   rw 27 q6 ∷
   rw⁻ 26 q4 ∷
   re 27 3 (CS13 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q4 ∷
   rw 26 q6 ∷
   rw⁻ 25 q4 ∷
   re 26 3 (CS13 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q4 ∷
   rw 25 q6 ∷
   rw⁻ 24 q4 ∷
   re 25 3 (CS13 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q4 ∷
   rw 24 q6 ∷
   rw⁻ 23 q4 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw⁻ 22 q7 ∷
   rw 21 q6 ∷
   rw 20 q6 ∷
   rw 19 q6 ∷
   rw 18 q6 ∷
   rw 17 q6 ∷
   rw 16 q6 ∷
   rw⁻ 15 q14 ∷
   rw 14 q5 ∷
   rw 13 q6 ∷
   rw 12 q6 ∷
   rw 11 q6 ∷
   rw⁻ 10 q14 ∷
   rw 9 q5 ∷
   rw⁻ 8 q14 ∷
   rw 7 q5 ∷
   rw⁻ 6 q3 ∷
   rw⁻ 5 q3 ∷
   rw 4 q6 ∷
   rw 3 q6 ∷
   rw 2 q17 ∷
   rw 1 q18 ∷
   rw⁻ 0 q3 ∷
   rw 1 q19 ∷
   rw 0 q3 ∷
   rw 1 q2 ∷
   rw 2 q12 ∷
   rw 3 q12 ∷
   rw 4 q13 ∷
   rw 5 q12 ∷
   rw 6 q13 ∷
   rw 7 q13 ∷
   rw 8 q7 ∷
   re 10 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 9 q4 ∷
   rw 10 q13 ∷
   rw 11 q4 ∷
   re 9 3 (CK30 ∷ []) ∷
   rw 10 q8 ∷
   re 12 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 11 q4 ∷
   rw 12 q13 ∷
   rw 13 q4 ∷
   re 11 3 (CK30 ∷ []) ∷
   rw 12 q8 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q4 ∷
   rw 14 q12 ∷
   rw 15 q4 ∷
   re 13 3 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q4 ∷
   rw 15 q12 ∷
   rw 16 q4 ∷
   re 14 3 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q4 ∷
   rw 16 q12 ∷
   rw 17 q4 ∷
   re 15 3 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 16 q4 ∷
   rw 17 q13 ∷
   rw 18 q4 ∷
   re 16 3 (CK30 ∷ []) ∷
   rw 17 q8 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q4 ∷
   rw 19 q12 ∷
   rw 20 q4 ∷
   re 18 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q4 ∷
   rw 20 q12 ∷
   rw 21 q4 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q4 ∷
   rw 21 q12 ∷
   rw 22 q4 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q4 ∷
   rw 22 q12 ∷
   rw 23 q4 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q4 ∷
   rw 23 q12 ∷
   rw 24 q4 ∷
   re 22 3 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q4 ∷
   rw 24 q12 ∷
   rw 25 q4 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 24 q7 ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q4 ∷
   rw 26 q12 ∷
   rw 27 q4 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q4 ∷
   rw 27 q12 ∷
   rw 28 q4 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 27 q4 ∷
   rw 28 q13 ∷
   rw 29 q4 ∷
   re 27 3 (CK30 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q4 ∷
   rw 29 q12 ∷
   rw 30 q4 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 29 q4 ∷
   rw 30 q13 ∷
   rw 31 q4 ∷
   re 29 3 (CK30 ∷ []) ∷
   re 31 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 30 q4 ∷
   rw 31 q13 ∷
   rw 32 q4 ∷
   re 30 3 (CK30 ∷ []) ∷
   rw 31 q3 ∷
   rw 32 q2 ∷
   rw 33 q15 ∷ []) Eq.refl
