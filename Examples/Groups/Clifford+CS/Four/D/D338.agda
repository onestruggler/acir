{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D338 (W : Ws) where

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
  q1 = wE 959 W
  q2 : Eqn
  q2 = wE 879 W
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = wE 157 W
  q5 : Eqn
  q5 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q6 : Eqn
  q6 = wE 158 W
  q7 : Eqn
  q7 = wE 3 W
  q8 : Eqn
  q8 = wE 880 W
  q9 : Eqn
  q9 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q10 : Eqn
  q10 = wE 956 W
  q11 : Eqn
  q11 = eqn (X1 ∷ S2 ∷ []) (S2 ∷ X1 ∷ []) (low-comm ((X ↑)) (S))
  q12 : Eqn
  q12 = wE 625 W
  q13 : Eqn
  q13 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q14 : Eqn
  q14 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q15 : Eqn
  q15 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q16 : Eqn
  q16 = wE 882 W
  q17 : Eqn
  q17 = wE 5 W
  q18 : Eqn
  q18 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q19 : Eqn
  q19 = wE 7 W
  q20 : Eqn
  q20 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q21 : Eqn
  q21 = wE 140 W

-- Bar(SSKSKK;1,2->0) passes groups of WBar(SSSSSSKiSSSSSSSSS;~1,3->0) part0: 500 steps
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part0 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw01 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK12-⟶0⟩-passes-groups-of-WBar⟨SSSSSSKiSSSSSSSSS~13-⟶0⟩-part0 = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) (X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X1 ∷ X1 ∷ CX13 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw01 ∷ X1 ∷ CX13 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ [])
  (rw 0 q1 ∷
   rw 47 q2 ∷
   re 49 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 48 q3 ∷
   re 49 3 (CK30 ∷ []) ∷
   re 49 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 55 q3 ∷
   re 53 3 (CX13 ∷ []) ∷
   rw 52 q4 ∷
   rw 51 q5 ∷
   rw 50 q6 ∷
   re 50 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 49 q7 ∷
   re 50 5 (CK30 ∷ []) ∷
   re 50 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 52 q7 ∷
   re 48 3 (CX13 ∷ []) ∷
   rw 49 q2 ∷
   rw 46 q2 ∷
   re 48 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 47 q3 ∷
   re 48 3 (CK30 ∷ []) ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q3 ∷
   re 52 3 (CX13 ∷ []) ∷
   rw 51 q4 ∷
   rw 50 q5 ∷
   rw 49 q6 ∷
   re 49 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 48 q7 ∷
   re 49 5 (CK30 ∷ []) ∷
   re 49 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 51 q7 ∷
   re 47 3 (CX13 ∷ []) ∷
   rw 48 q2 ∷
   rw 45 q8 ∷
   re 47 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 46 q3 ∷
   re 47 3 (CS03 ∷ []) ∷
   re 47 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q3 ∷
   re 51 3 (CX13 ∷ []) ∷
   rw 50 q4 ∷
   rw 49 q9 ∷
   rw 48 q6 ∷
   re 48 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 47 q7 ∷
   re 48 5 (CS03 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q7 ∷
   re 46 3 (CX13 ∷ []) ∷
   rw 47 q8 ∷
   rw 44 q2 ∷
   re 46 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 45 q3 ∷
   re 46 3 (CK30 ∷ []) ∷
   re 46 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q3 ∷
   re 50 3 (CX13 ∷ []) ∷
   rw 49 q4 ∷
   rw 48 q5 ∷
   rw 47 q6 ∷
   re 47 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 46 q7 ∷
   re 47 5 (CK30 ∷ []) ∷
   re 47 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 49 q7 ∷
   re 45 3 (CX13 ∷ []) ∷
   rw 46 q2 ∷
   rw 43 q8 ∷
   re 45 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 44 q3 ∷
   re 45 3 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q3 ∷
   re 49 3 (CX13 ∷ []) ∷
   rw 48 q4 ∷
   rw 47 q9 ∷
   rw 46 q6 ∷
   re 46 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 45 q7 ∷
   re 46 5 (CS03 ∷ []) ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q7 ∷
   re 44 3 (CX13 ∷ []) ∷
   rw 45 q8 ∷
   rw 42 q8 ∷
   re 44 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 43 q3 ∷
   re 44 3 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q3 ∷
   re 48 3 (CX13 ∷ []) ∷
   rw 47 q4 ∷
   rw 46 q9 ∷
   rw 45 q6 ∷
   re 45 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 44 q7 ∷
   re 45 5 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q7 ∷
   re 43 3 (CX13 ∷ []) ∷
   rw 44 q8 ∷
   rw 41 q10 ∷
   rw 40 q8 ∷
   re 42 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 41 q3 ∷
   re 42 3 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q3 ∷
   re 46 3 (CX13 ∷ []) ∷
   rw 45 q4 ∷
   rw 44 q9 ∷
   rw 43 q6 ∷
   re 43 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 42 q7 ∷
   re 43 5 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q7 ∷
   re 41 3 (CX13 ∷ []) ∷
   rw 42 q8 ∷
   rw 39 q8 ∷
   re 41 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 40 q3 ∷
   re 41 3 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q3 ∷
   re 45 3 (CX13 ∷ []) ∷
   rw 44 q4 ∷
   rw 43 q9 ∷
   rw 42 q6 ∷
   re 42 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 41 q7 ∷
   re 42 5 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q7 ∷
   re 40 3 (CX13 ∷ []) ∷
   rw 41 q8 ∷
   rw 38 q8 ∷
   re 40 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 39 q3 ∷
   re 40 3 (CS03 ∷ []) ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q3 ∷
   re 44 3 (CX13 ∷ []) ∷
   rw 43 q4 ∷
   rw 42 q9 ∷
   rw 41 q6 ∷
   re 41 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 40 q7 ∷
   re 41 5 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 43 q7 ∷
   re 39 3 (CX13 ∷ []) ∷
   rw 40 q8 ∷
   rw 37 q8 ∷
   re 39 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 38 q3 ∷
   re 39 3 (CS03 ∷ []) ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q3 ∷
   re 43 3 (CX13 ∷ []) ∷
   rw 42 q4 ∷
   rw 41 q9 ∷
   rw 40 q6 ∷
   re 40 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 39 q7 ∷
   re 40 5 (CS03 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q7 ∷
   re 38 3 (CX13 ∷ []) ∷
   rw 39 q8 ∷
   rw 36 q8 ∷
   re 38 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 37 q3 ∷
   re 38 3 (CS03 ∷ []) ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q3 ∷
   re 42 3 (CX13 ∷ []) ∷
   rw 41 q4 ∷
   rw 40 q9 ∷
   rw 39 q6 ∷
   re 39 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 38 q7 ∷
   re 39 5 (CS03 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q7 ∷
   re 37 3 (CX13 ∷ []) ∷
   rw 38 q8 ∷
   rw 35 q8 ∷
   re 37 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 36 q3 ∷
   re 37 3 (CS03 ∷ []) ∷
   re 37 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q3 ∷
   re 41 3 (CX13 ∷ []) ∷
   rw 40 q4 ∷
   rw 39 q9 ∷
   rw 38 q6 ∷
   re 38 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 37 q7 ∷
   re 38 5 (CS03 ∷ []) ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q7 ∷
   re 36 3 (CX13 ∷ []) ∷
   rw 37 q8 ∷
   rw⁻ 34 q11 ∷
   rw 35 q12 ∷
   rw⁻ 36 q11 ∷
   rw 33 q2 ∷
   re 35 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 34 q3 ∷
   re 35 3 (CK30 ∷ []) ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q3 ∷
   re 39 3 (CX13 ∷ []) ∷
   rw 38 q4 ∷
   rw 37 q5 ∷
   rw 36 q6 ∷
   re 36 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 35 q7 ∷
   re 36 5 (CK30 ∷ []) ∷
   re 36 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 38 q7 ∷
   re 34 3 (CX13 ∷ []) ∷
   rw 35 q2 ∷
   rw 32 q8 ∷
   re 34 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 33 q3 ∷
   re 34 3 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q3 ∷
   re 38 3 (CX13 ∷ []) ∷
   rw 37 q4 ∷
   rw 36 q9 ∷
   rw 35 q6 ∷
   re 35 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 34 q7 ∷
   re 35 5 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q7 ∷
   re 33 3 (CX13 ∷ []) ∷
   rw 34 q8 ∷
   rw 31 q8 ∷
   re 33 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 32 q3 ∷
   re 33 3 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q3 ∷
   re 37 3 (CX13 ∷ []) ∷
   rw 36 q4 ∷
   rw 35 q9 ∷
   rw 34 q6 ∷
   re 34 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 33 q7 ∷
   re 34 5 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q7 ∷
   re 32 3 (CX13 ∷ []) ∷
   rw 33 q8 ∷
   rw 30 q8 ∷
   re 32 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 31 q3 ∷
   re 32 3 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q3 ∷
   re 36 3 (CX13 ∷ []) ∷
   rw 35 q4 ∷
   rw 34 q9 ∷
   rw 33 q6 ∷
   re 33 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 32 q7 ∷
   re 33 5 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q7 ∷
   re 31 3 (CX13 ∷ []) ∷
   rw 32 q8 ∷
   rw⁻ 29 q11 ∷
   rw 30 q12 ∷
   rw⁻ 31 q11 ∷
   rw 28 q2 ∷
   re 30 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 29 q3 ∷
   re 30 3 (CK30 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q3 ∷
   re 34 3 (CX13 ∷ []) ∷
   rw 33 q4 ∷
   rw 32 q5 ∷
   rw 31 q6 ∷
   re 31 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 30 q7 ∷
   re 31 5 (CK30 ∷ []) ∷
   re 31 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 33 q7 ∷
   re 29 3 (CX13 ∷ []) ∷
   rw 30 q2 ∷
   rw⁻ 27 q11 ∷
   rw 28 q12 ∷
   rw⁻ 29 q11 ∷
   rw 26 q2 ∷
   re 28 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 27 q3 ∷
   re 28 3 (CK30 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q3 ∷
   re 32 3 (CX13 ∷ []) ∷
   rw 31 q4 ∷
   rw 30 q5 ∷
   rw 29 q6 ∷
   re 29 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 28 q7 ∷
   re 29 5 (CK30 ∷ []) ∷
   re 29 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 31 q7 ∷
   re 27 3 (CX13 ∷ []) ∷
   rw 28 q2 ∷
   rw 25 q10 ∷
   rw 28 q3 ∷
   rw 27 q13 ∷
   re 26 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 28 q7 ∷
   rw 25 q13 ∷
   rw 24 q14 ∷
   rw 23 q14 ∷
   rw 22 q15 ∷
   rw 21 q14 ∷
   rw 20 q15 ∷
   rw 19 q15 ∷
   rw 20 q16 ∷
   rw⁻ 19 q13 ∷
   rw 22 q3 ∷
   re 20 3 (CX13 ∷ []) ∷
   rw⁻ 21 q13 ∷
   rw⁻ 22 q15 ∷
   rw⁻ 23 q15 ∷
   rw⁻ 24 q14 ∷
   rw⁻ 25 q15 ∷
   rw⁻ 26 q14 ∷
   rw⁻ 27 q14 ∷
   rw 28 q7 ∷
   rw 101 q17 ∷
   re 100 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 102 q18 ∷
   rw 101 q19 ∷
   rw⁻ 100 q18 ∷
   re 101 3 (CS13 ∷ []) ∷
   re 99 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 101 q18 ∷
   rw 100 q19 ∷
   rw⁻ 99 q18 ∷
   re 100 3 (CS13 ∷ []) ∷
   re 98 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 100 q18 ∷
   rw 99 q19 ∷
   rw⁻ 98 q18 ∷
   re 99 3 (CS13 ∷ []) ∷
   re 97 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 99 q18 ∷
   rw 98 q19 ∷
   rw⁻ 97 q18 ∷
   re 98 3 (CS13 ∷ []) ∷
   re 96 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 98 q18 ∷
   rw 97 q19 ∷
   rw⁻ 96 q18 ∷
   re 97 3 (CS13 ∷ []) ∷
   re 95 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 97 q18 ∷
   rw 96 q19 ∷
   rw⁻ 95 q18 ∷
   re 96 3 (CS13 ∷ []) ∷
   re 94 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 96 q18 ∷
   rw 95 q19 ∷
   rw⁻ 94 q18 ∷
   re 95 3 (CS13 ∷ []) ∷
   re 93 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 95 q18 ∷
   rw 94 q19 ∷
   rw⁻ 93 q18 ∷
   re 94 3 (CS13 ∷ []) ∷
   re 92 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 94 q18 ∷
   rw 93 q19 ∷
   rw⁻ 92 q18 ∷
   re 93 3 (CS13 ∷ []) ∷
   re 91 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 93 q18 ∷
   rw 92 q19 ∷
   rw⁻ 91 q18 ∷
   re 92 3 (CS13 ∷ []) ∷
   re 90 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 92 q18 ∷
   rw 91 q19 ∷
   rw⁻ 90 q18 ∷
   re 91 3 (CS13 ∷ []) ∷
   re 89 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 91 q18 ∷
   rw 90 q19 ∷
   rw⁻ 89 q18 ∷
   re 90 3 (CS13 ∷ []) ∷
   re 88 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 90 q18 ∷
   rw 89 q19 ∷
   rw⁻ 88 q18 ∷
   re 89 3 (CS13 ∷ []) ∷
   re 87 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 89 q18 ∷
   rw 88 q19 ∷
   rw⁻ 87 q18 ∷
   re 88 3 (CS13 ∷ []) ∷
   re 86 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 88 q18 ∷
   rw 87 q19 ∷
   rw⁻ 86 q18 ∷
   re 87 3 (CS13 ∷ []) ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 87 q18 ∷
   rw 86 q19 ∷
   rw⁻ 85 q18 ∷
   re 86 3 (CS13 ∷ []) ∷
   re 84 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 86 q18 ∷
   rw 85 q19 ∷
   rw⁻ 84 q18 ∷
   re 85 3 (CS13 ∷ []) ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 85 q18 ∷
   rw 84 q19 ∷
   rw⁻ 83 q18 ∷
   re 84 3 (CS13 ∷ []) ∷
   rw⁻ 82 q20 ∷
   re 81 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 83 q18 ∷
   rw 82 q21 ∷
   rw⁻ 81 q18 ∷
   re 82 3 (CK31 ∷ []) ∷
   rw⁻ 80 q20 ∷
   rw⁻ 79 q20 ∷
   rw⁻ 78 q20 ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 79 q18 ∷
   rw 78 q19 ∷
   rw⁻ 77 q18 ∷
   re 78 3 (CS13 ∷ []) ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 78 q18 ∷
   rw 77 q19 ∷
   rw⁻ 76 q18 ∷
   re 77 3 (CS13 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 77 q18 ∷
   rw 76 q19 ∷
   rw⁻ 75 q18 ∷
   re 76 3 (CS13 ∷ []) ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 76 q18 ∷
   rw 75 q19 ∷
   rw⁻ 74 q18 ∷
   re 75 3 (CS13 ∷ []) ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 75 q18 ∷
   rw 74 q19 ∷
   rw⁻ 73 q18 ∷
   re 74 3 (CS13 ∷ []) ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 74 q18 ∷
   rw 73 q19 ∷
   rw⁻ 72 q18 ∷
   re 73 3 (CS13 ∷ []) ∷
   re 71 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 73 q18 ∷
   rw 72 q19 ∷
   rw⁻ 71 q18 ∷
   re 72 3 (CS13 ∷ []) ∷
   re 70 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 72 q18 ∷
   rw 71 q19 ∷
   rw⁻ 70 q18 ∷
   re 71 3 (CS13 ∷ []) ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 71 q18 ∷
   rw 70 q19 ∷
   rw⁻ 69 q18 ∷
   re 70 3 (CS13 ∷ []) ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 70 q18 ∷
   rw 69 q19 ∷
   rw⁻ 68 q18 ∷
   re 69 3 (CS13 ∷ []) ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 69 q18 ∷
   rw 68 q19 ∷
   rw⁻ 67 q18 ∷
   re 68 3 (CS13 ∷ []) ∷
   re 66 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 68 q18 ∷
   rw 67 q19 ∷
   rw⁻ 66 q18 ∷ []) Eq.refl
