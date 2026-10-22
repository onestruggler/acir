{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D458 (W : Ws) where

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
  q1 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q2 : Eqn
  q2 = wE 140 W
  q3 : Eqn
  q3 = wE 7 W
  q4 : Eqn
  q4 = wE 766 W
  q5 : Eqn
  q5 = wE 27 W
  q6 : Eqn
  q6 = wE 142 W
  q7 : Eqn
  q7 = wE 31 W
  q8 : Eqn
  q8 = wE 36 W
  q9 : Eqn
  q9 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q10 : Eqn
  q10 = wE 37 W
  q11 : Eqn
  q11 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q12 : Eqn
  q12 = wE 5 W
  q13 : Eqn
  q13 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q14 : Eqn
  q14 = wE 1144 W
  q15 : Eqn
  q15 = wE 764 W

-- Bar(SSKSKK;1,3->0) passes groups of WBar(SSKSKK;~1,2->0) part3: 269 steps
lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩-part3 : ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X1 ∷ CX12 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩-part3 = derive (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X1 ∷ CX12 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ Sw01 ∷ []) (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw⁻ 59 q1 ∷
   rw 58 q2 ∷
   rw⁻ 57 q1 ∷
   re 58 3 (CK31 ∷ []) ∷
   re 56 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 58 q1 ∷
   rw 57 q2 ∷
   rw⁻ 56 q1 ∷
   re 57 3 (CK31 ∷ []) ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 57 q1 ∷
   rw 56 q3 ∷
   rw⁻ 55 q1 ∷
   re 56 3 (CS13 ∷ []) ∷
   re 54 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 56 q1 ∷
   rw 55 q2 ∷
   rw⁻ 54 q1 ∷
   re 55 3 (CK31 ∷ []) ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 55 q1 ∷
   rw 54 q3 ∷
   rw⁻ 53 q1 ∷
   re 54 3 (CS13 ∷ []) ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 54 q1 ∷
   rw 53 q3 ∷
   rw⁻ 52 q1 ∷
   re 53 3 (CS13 ∷ []) ∷
   rw 53 q4 ∷
   rw 52 q5 ∷
   rw 53 q5 ∷
   rw 54 q6 ∷
   rw 55 q5 ∷
   rw 56 q6 ∷
   rw 57 q6 ∷
   re 59 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 58 q1 ∷
   rw 59 q5 ∷
   rw 60 q1 ∷
   re 58 3 (CS03 ∷ []) ∷
   re 60 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 59 q1 ∷
   rw 60 q5 ∷
   rw 61 q1 ∷
   re 59 3 (CS03 ∷ []) ∷
   re 61 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 60 q1 ∷
   rw 61 q6 ∷
   rw 62 q1 ∷
   re 60 3 (CK30 ∷ []) ∷
   re 62 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 61 q1 ∷
   rw 62 q5 ∷
   rw 63 q1 ∷
   re 61 3 (CS03 ∷ []) ∷
   re 63 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 62 q1 ∷
   rw 63 q6 ∷
   rw 64 q1 ∷
   re 62 3 (CK30 ∷ []) ∷
   re 64 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 63 q1 ∷
   rw 64 q6 ∷
   rw 65 q1 ∷
   re 63 3 (CK30 ∷ []) ∷
   rw 64 q7 ∷
   re 52 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 51 q8 ∷
   rw⁻ 52 q9 ∷
   rw 53 q10 ∷
   re 51 3 (CS02 ∷ []) ∷
   re 53 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 52 q8 ∷
   rw⁻ 53 q9 ∷
   rw 54 q10 ∷
   re 52 3 (CS02 ∷ []) ∷
   re 54 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 53 q8 ∷
   rw⁻ 54 q11 ∷
   rw 55 q10 ∷
   re 53 3 (CK20 ∷ []) ∷
   re 55 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 54 q8 ∷
   rw⁻ 55 q9 ∷
   rw 56 q10 ∷
   re 54 3 (CS02 ∷ []) ∷
   re 56 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 55 q8 ∷
   rw⁻ 56 q11 ∷
   rw 57 q10 ∷
   re 55 3 (CK20 ∷ []) ∷
   re 57 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 56 q8 ∷
   rw⁻ 57 q11 ∷
   rw 58 q10 ∷
   re 56 3 (CK20 ∷ []) ∷
   rw 57 q12 ∷
   rw 56 q2 ∷
   rw 55 q2 ∷
   rw 54 q3 ∷
   rw 53 q2 ∷
   rw 52 q3 ∷
   rw 51 q3 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 52 q1 ∷
   rw 51 q3 ∷
   rw⁻ 50 q1 ∷
   re 51 3 (CS13 ∷ []) ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 51 q1 ∷
   rw 50 q3 ∷
   rw⁻ 49 q1 ∷
   re 50 3 (CS13 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 50 q1 ∷
   rw 49 q3 ∷
   rw⁻ 48 q1 ∷
   re 49 3 (CS13 ∷ []) ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q1 ∷
   rw 48 q3 ∷
   rw⁻ 47 q1 ∷
   re 48 3 (CS13 ∷ []) ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q1 ∷
   rw 47 q3 ∷
   rw⁻ 46 q1 ∷
   re 47 3 (CS13 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 47 q1 ∷
   rw 46 q3 ∷
   rw⁻ 45 q1 ∷
   re 46 3 (CS13 ∷ []) ∷
   rw⁻ 44 q13 ∷
   re 43 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q1 ∷
   rw 44 q2 ∷
   rw⁻ 43 q1 ∷
   re 44 3 (CK31 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q1 ∷
   rw 43 q3 ∷
   rw⁻ 42 q1 ∷
   re 43 3 (CS13 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q1 ∷
   rw 42 q3 ∷
   rw⁻ 41 q1 ∷
   re 42 3 (CS13 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q1 ∷
   rw 41 q3 ∷
   rw⁻ 40 q1 ∷
   re 41 3 (CS13 ∷ []) ∷
   rw⁻ 39 q13 ∷
   re 38 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q1 ∷
   rw 39 q2 ∷
   rw⁻ 38 q1 ∷
   re 39 3 (CK31 ∷ []) ∷
   rw⁻ 37 q13 ∷
   re 36 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q1 ∷
   rw 37 q2 ∷
   rw⁻ 36 q1 ∷
   re 37 3 (CK31 ∷ []) ∷
   rw 37 q14 ∷
   rw 36 q5 ∷
   rw 37 q5 ∷
   rw 38 q6 ∷
   rw 39 q5 ∷
   rw 40 q6 ∷
   rw 41 q6 ∷
   re 43 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 42 q1 ∷
   rw 43 q6 ∷
   rw 44 q1 ∷
   re 42 3 (CK30 ∷ []) ∷
   rw 43 q13 ∷
   re 45 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 44 q1 ∷
   rw 45 q6 ∷
   rw 46 q1 ∷
   re 44 3 (CK30 ∷ []) ∷
   rw 45 q13 ∷
   re 47 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 46 q1 ∷
   rw 47 q5 ∷
   rw 48 q1 ∷
   re 46 3 (CS03 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 47 q1 ∷
   rw 48 q5 ∷
   rw 49 q1 ∷
   re 47 3 (CS03 ∷ []) ∷
   re 49 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 48 q1 ∷
   rw 49 q5 ∷
   rw 50 q1 ∷
   re 48 3 (CS03 ∷ []) ∷
   re 50 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 49 q1 ∷
   rw 50 q6 ∷
   rw 51 q1 ∷
   re 49 3 (CK30 ∷ []) ∷
   rw 50 q13 ∷
   re 52 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 51 q1 ∷
   rw 52 q5 ∷
   rw 53 q1 ∷
   re 51 3 (CS03 ∷ []) ∷
   re 53 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 52 q1 ∷
   rw 53 q5 ∷
   rw 54 q1 ∷
   re 52 3 (CS03 ∷ []) ∷
   re 54 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 53 q1 ∷
   rw 54 q5 ∷
   rw 55 q1 ∷
   re 53 3 (CS03 ∷ []) ∷
   re 55 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 54 q1 ∷
   rw 55 q5 ∷
   rw 56 q1 ∷
   re 54 3 (CS03 ∷ []) ∷
   re 56 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 55 q1 ∷
   rw 56 q5 ∷
   rw 57 q1 ∷
   re 55 3 (CS03 ∷ []) ∷
   re 57 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 56 q1 ∷
   rw 57 q5 ∷
   rw 58 q1 ∷
   re 56 3 (CS03 ∷ []) ∷
   rw 57 q7 ∷
   re 36 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 35 q8 ∷
   rw⁻ 36 q9 ∷
   rw 37 q10 ∷
   re 35 3 (CS02 ∷ []) ∷
   re 37 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 36 q8 ∷
   rw⁻ 37 q9 ∷
   rw 38 q10 ∷
   re 36 3 (CS02 ∷ []) ∷
   re 38 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 37 q8 ∷
   rw⁻ 38 q11 ∷
   rw 39 q10 ∷
   re 37 3 (CK20 ∷ []) ∷
   re 39 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 38 q8 ∷
   rw⁻ 39 q9 ∷
   rw 40 q10 ∷
   re 38 3 (CS02 ∷ []) ∷
   re 40 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 39 q8 ∷
   rw⁻ 40 q11 ∷
   rw 41 q10 ∷
   re 39 3 (CK20 ∷ []) ∷
   re 41 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 40 q8 ∷
   rw⁻ 41 q11 ∷
   rw 42 q10 ∷
   re 40 3 (CK20 ∷ []) ∷
   rw 29 q15 ∷ []) Eq.refl
