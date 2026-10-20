{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D283 (W : Ws) where

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
  q1 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q2 : Eqn
  q2 = eqn (CX32 ∷ Sw12 ∷ []) (Sw12 ∷ CX31 ∷ []) (wn 78 W)
  q3 : Eqn
  q3 = eqn (CX31 ∷ Sw12 ∷ []) (Sw12 ∷ CX32 ∷ []) (wn 13 W)
  q4 : Eqn
  q4 = eqn (CX31 ∷ S2 ∷ []) (S2 ∷ CX31 ∷ []) (wn 762 W)
  q5 : Eqn
  q5 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q6 : Eqn
  q6 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q7 : Eqn
  q7 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q8 : Eqn
  q8 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q9 : Eqn
  q9 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q11 : Eqn
  q11 = eqn (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ []) (CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ S2 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (wn 868 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q13 : Eqn
  q13 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q15 : Eqn
  q15 = eqn (CS01 ∷ X3 ∷ []) (X3 ∷ CS01 ∷ []) (low-comm (CS) ((X ↑)))
  q16 : Eqn
  q16 = eqn (CK10 ∷ X3 ∷ []) (X3 ∷ CK10 ∷ []) (low-comm (CK₁₀) ((X ↑)))
  q17 : Eqn
  q17 = eqn (CX31 ∷ X3 ∷ CX32 ∷ X3 ∷ []) (X3 ∷ CX32 ∷ X3 ∷ CX31 ∷ []) (wn 537 W)
  q18 : Eqn
  q18 = eqn (S1 ∷ X3 ∷ []) (X3 ∷ S1 ∷ []) (low-comm ((S ↑)) ((X ↑)))
  q19 : Eqn
  q19 = eqn (S1 ∷ CX32 ∷ []) (CX32 ∷ S1 ∷ []) (low-comm ((S ↑)) (CX₁₀))
  q20 : Eqn
  q20 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q21 : Eqn
  q21 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q22 : Eqn
  q22 = eqn (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ X3 ∷ CX32 ∷ X3 ∷ []) (X3 ∷ CX32 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (wn 796 W)
  q23 : Eqn
  q23 = eqn (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (wn 665 W)
  q24 : Eqn
  q24 = eqn (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (wn 666 W)

-- Bar(SSSKSS;3,1->0) passes groups of WBar(KiKiSSSKiSSSSSS;~3,2->0) part1: 500 steps
lem-Bar⟨SSSKSS31-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~32-⟶0⟩-part1 : ⟪ (X3 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw12 ∷ CX32 ∷ CS01 ∷ Sw12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CX32 ∷ X3 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ X3 ∷ CX32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CX31 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS31-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~32-⟶0⟩-part1 = derive (X3 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw12 ∷ CX32 ∷ CS01 ∷ Sw12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CX32 ∷ X3 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (X3 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X3 ∷ X3 ∷ CX32 ∷ X3 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ X3 ∷ CX32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CX31 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw⁻ 38 q1 ∷
   rw 39 q2 ∷
   re 37 3 (CS02 ∷ []) ∷
   re 39 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 38 q3 ∷
   rw⁻ 39 q1 ∷
   rw 40 q2 ∷
   re 38 3 (CS02 ∷ []) ∷
   re 40 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 39 q3 ∷
   rw⁻ 40 q1 ∷
   rw 41 q2 ∷
   re 39 3 (CS02 ∷ []) ∷
   re 41 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 40 q3 ∷
   rw⁻ 41 q1 ∷
   rw 42 q2 ∷
   re 40 3 (CS02 ∷ []) ∷
   re 42 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 41 q3 ∷
   rw⁻ 42 q1 ∷
   rw 43 q2 ∷
   re 41 3 (CS02 ∷ []) ∷
   re 43 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 42 q3 ∷
   rw⁻ 43 q1 ∷
   rw 44 q2 ∷
   re 42 3 (CS02 ∷ []) ∷
   re 44 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 43 q3 ∷
   rw⁻ 44 q1 ∷
   rw 45 q2 ∷
   re 43 3 (CS02 ∷ []) ∷
   rw 44 q4 ∷
   rw 45 q4 ∷
   rw 46 q4 ∷
   re 48 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 47 q3 ∷
   rw⁻ 48 q5 ∷
   rw 49 q2 ∷
   re 47 3 (CK20 ∷ []) ∷
   rw 48 q4 ∷
   re 50 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 49 q3 ∷
   rw⁻ 50 q1 ∷
   rw 51 q2 ∷
   re 49 3 (CS02 ∷ []) ∷
   re 51 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 50 q3 ∷
   rw⁻ 51 q1 ∷
   rw 52 q2 ∷
   re 50 3 (CS02 ∷ []) ∷
   re 52 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 51 q3 ∷
   rw⁻ 52 q1 ∷
   rw 53 q2 ∷
   re 51 3 (CS02 ∷ []) ∷
   re 53 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 52 q3 ∷
   rw⁻ 53 q1 ∷
   rw 54 q2 ∷
   re 52 3 (CS02 ∷ []) ∷
   re 54 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 53 q3 ∷
   rw⁻ 54 q1 ∷
   rw 55 q2 ∷
   re 53 3 (CS02 ∷ []) ∷
   re 55 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 54 q3 ∷
   rw⁻ 55 q1 ∷
   rw 56 q2 ∷
   re 54 3 (CS02 ∷ []) ∷
   re 56 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 55 q3 ∷
   rw⁻ 56 q1 ∷
   rw 57 q2 ∷
   re 55 3 (CS02 ∷ []) ∷
   re 57 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 56 q3 ∷
   rw⁻ 57 q1 ∷
   rw 58 q2 ∷
   re 56 3 (CS02 ∷ []) ∷
   re 58 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 57 q3 ∷
   rw⁻ 58 q1 ∷
   rw 59 q2 ∷
   re 57 3 (CS02 ∷ []) ∷
   rw 58 q4 ∷
   rw 59 q4 ∷
   rw 60 q4 ∷
   re 62 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 61 q3 ∷
   rw⁻ 62 q5 ∷
   rw 63 q2 ∷
   re 61 3 (CK20 ∷ []) ∷
   rw 62 q4 ∷
   rw 63 q4 ∷
   rw 64 q4 ∷
   rw 65 q4 ∷
   re 67 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 66 q3 ∷
   rw⁻ 67 q5 ∷
   rw 68 q2 ∷
   re 66 3 (CK20 ∷ []) ∷
   rw 67 q4 ∷
   rw 68 q6 ∷
   rw⁻ 67 q7 ∷
   rw 66 q8 ∷
   rw⁻ 65 q7 ∷
   rw⁻ 64 q7 ∷
   rw⁻ 63 q7 ∷
   rw⁻ 62 q7 ∷
   rw 61 q8 ∷
   rw⁻ 60 q7 ∷
   rw⁻ 59 q7 ∷
   rw⁻ 58 q7 ∷
   rw 57 q9 ∷
   rw 56 q9 ∷
   rw 55 q9 ∷
   rw 54 q9 ∷
   rw 53 q9 ∷
   rw 52 q9 ∷
   rw 51 q9 ∷
   rw 50 q9 ∷
   rw 49 q9 ∷
   rw⁻ 48 q7 ∷
   rw 47 q8 ∷
   rw⁻ 46 q7 ∷
   rw⁻ 45 q7 ∷
   rw⁻ 44 q7 ∷
   rw 43 q9 ∷
   rw 42 q9 ∷
   rw 41 q9 ∷
   rw 40 q9 ∷
   rw 39 q9 ∷
   rw 38 q9 ∷
   rw 37 q9 ∷
   rw 36 q9 ∷
   rw 35 q9 ∷
   rw 34 q9 ∷
   rw 33 q9 ∷
   rw 32 q9 ∷
   rw 31 q9 ∷
   rw 30 q9 ∷
   rw 29 q9 ∷
   rw 28 q9 ∷
   rw 27 q9 ∷
   rw 26 q9 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q10 ∷
   rw 26 q9 ∷
   rw⁻ 25 q10 ∷
   re 26 3 (CS13 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q10 ∷
   rw 25 q9 ∷
   rw⁻ 24 q10 ∷
   re 25 3 (CS13 ∷ []) ∷
   re 23 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q10 ∷
   rw 24 q8 ∷
   rw⁻ 23 q10 ∷
   re 24 3 (CK31 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q10 ∷
   rw 23 q9 ∷
   rw⁻ 22 q10 ∷
   re 23 3 (CS13 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q10 ∷
   rw 22 q9 ∷
   rw⁻ 21 q10 ∷
   re 22 3 (CS13 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q10 ∷
   rw 21 q9 ∷
   rw⁻ 20 q10 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 21 q11 ∷
   rw 20 q12 ∷
   rw 21 q12 ∷
   rw 22 q12 ∷
   rw 23 q12 ∷
   rw 24 q12 ∷
   rw 25 q12 ∷
   rw 26 q12 ∷
   rw 27 q12 ∷
   rw 28 q12 ∷
   rw 29 q12 ∷
   rw 30 q12 ∷
   rw 31 q12 ∷
   rw 32 q12 ∷
   rw 33 q12 ∷
   rw 34 q12 ∷
   rw 35 q12 ∷
   rw 36 q12 ∷
   rw 37 q12 ∷
   rw 38 q7 ∷
   rw 39 q7 ∷
   rw 40 q7 ∷
   rw 41 q13 ∷
   rw 42 q7 ∷
   rw 43 q12 ∷
   rw 44 q12 ∷
   rw 45 q12 ∷
   rw 46 q12 ∷
   rw 47 q12 ∷
   rw 48 q12 ∷
   rw 49 q12 ∷
   rw 50 q12 ∷
   rw 51 q12 ∷
   rw 52 q7 ∷
   rw 53 q7 ∷
   rw 54 q7 ∷
   rw 55 q13 ∷
   rw 56 q7 ∷
   rw 57 q7 ∷
   rw 58 q7 ∷
   rw 59 q7 ∷
   rw 60 q13 ∷
   rw 61 q7 ∷
   re 63 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 62 q10 ∷
   rw 63 q12 ∷
   rw 64 q10 ∷
   re 62 3 (CS03 ∷ []) ∷
   re 64 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 63 q10 ∷
   rw 64 q12 ∷
   rw 65 q10 ∷
   re 63 3 (CS03 ∷ []) ∷
   re 65 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 64 q10 ∷
   rw 65 q12 ∷
   rw 66 q10 ∷
   re 64 3 (CS03 ∷ []) ∷
   re 66 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 65 q10 ∷
   rw 66 q13 ∷
   rw 67 q10 ∷
   re 65 3 (CK30 ∷ []) ∷
   re 67 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 66 q10 ∷
   rw 67 q12 ∷
   rw 68 q10 ∷
   re 66 3 (CS03 ∷ []) ∷
   re 68 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 67 q10 ∷
   rw 68 q12 ∷
   rw 69 q10 ∷
   re 67 3 (CS03 ∷ []) ∷
   rw 68 q14 ∷
   rw 92 q15 ∷
   rw 93 q1 ∷
   rw 94 q15 ∷
   rw 91 q15 ∷
   rw 92 q1 ∷
   rw 93 q15 ∷
   rw 90 q16 ∷
   rw 91 q5 ∷
   rw 92 q16 ∷
   rw 89 q15 ∷
   rw 90 q1 ∷
   rw 91 q15 ∷
   rw 88 q15 ∷
   rw 89 q1 ∷
   rw 90 q15 ∷
   rw 87 q15 ∷
   rw 88 q1 ∷
   rw 89 q15 ∷
   rw 86 q17 ∷
   rw 85 q15 ∷
   rw 86 q1 ∷
   rw 87 q15 ∷
   rw 84 q15 ∷
   rw 85 q1 ∷
   rw 86 q15 ∷
   rw 83 q15 ∷
   rw 84 q1 ∷
   rw 85 q15 ∷
   rw 82 q15 ∷
   rw 83 q1 ∷
   rw 84 q15 ∷
   rw 81 q15 ∷
   rw 82 q1 ∷
   rw 83 q15 ∷
   rw 80 q15 ∷
   rw 81 q1 ∷
   rw 82 q15 ∷
   rw 79 q15 ∷
   rw 80 q1 ∷
   rw 81 q15 ∷
   rw 78 q15 ∷
   rw 79 q1 ∷
   rw 80 q15 ∷
   rw 77 q15 ∷
   rw 78 q1 ∷
   rw 79 q15 ∷
   rw 76 q18 ∷
   rw 77 q19 ∷
   rw 78 q18 ∷
   rw 75 q16 ∷
   rw 76 q5 ∷
   rw 77 q16 ∷
   rw 74 q15 ∷
   rw 75 q1 ∷
   rw 76 q15 ∷
   rw 73 q15 ∷
   rw 74 q1 ∷
   rw 75 q15 ∷
   rw 72 q15 ∷
   rw 73 q1 ∷
   rw 74 q15 ∷
   rw 71 q15 ∷
   rw 72 q1 ∷
   rw 73 q15 ∷
   rw 70 q15 ∷
   rw 71 q1 ∷
   rw 72 q15 ∷
   rw 69 q15 ∷
   rw 70 q1 ∷
   rw 71 q15 ∷
   rw 68 q17 ∷
   rw 71 q6 ∷
   rw⁻ 70 q20 ∷
   rw⁻ 69 q21 ∷
   rw⁻ 68 q20 ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 69 q10 ∷
   rw 68 q9 ∷
   rw⁻ 67 q10 ∷
   re 68 3 (CS13 ∷ []) ∷
   re 66 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 68 q10 ∷
   rw 67 q9 ∷
   rw⁻ 66 q10 ∷
   re 67 3 (CS13 ∷ []) ∷
   re 65 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 67 q10 ∷
   rw 66 q8 ∷
   rw⁻ 65 q10 ∷
   re 66 3 (CK31 ∷ []) ∷
   re 64 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 66 q10 ∷
   rw 65 q9 ∷
   rw⁻ 64 q10 ∷
   re 65 3 (CS13 ∷ []) ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 65 q10 ∷
   rw 64 q9 ∷
   rw⁻ 63 q10 ∷
   re 64 3 (CS13 ∷ []) ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 64 q10 ∷
   rw 63 q9 ∷
   rw⁻ 62 q10 ∷
   re 63 3 (CS13 ∷ []) ∷
   rw 63 q22 ∷
   rw 62 q20 ∷
   rw 63 q21 ∷
   rw 64 q20 ∷
   re 66 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 65 q10 ∷
   rw 66 q12 ∷
   rw 67 q10 ∷
   re 65 3 (CS03 ∷ []) ∷
   re 67 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 66 q10 ∷
   rw 67 q12 ∷
   rw 68 q10 ∷
   re 66 3 (CS03 ∷ []) ∷
   re 68 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 67 q10 ∷
   rw 68 q12 ∷
   rw 69 q10 ∷
   re 67 3 (CS03 ∷ []) ∷
   re 69 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 68 q10 ∷
   rw 69 q13 ∷
   rw 70 q10 ∷
   re 68 3 (CK30 ∷ []) ∷
   re 70 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 69 q10 ∷
   rw 70 q12 ∷
   rw 71 q10 ∷
   re 69 3 (CS03 ∷ []) ∷
   re 71 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 70 q10 ∷
   rw 71 q12 ∷
   rw 72 q10 ∷
   re 70 3 (CS03 ∷ []) ∷
   rw 71 q14 ∷
   rw 90 q23 ∷
   re 90 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 89 q3 ∷
   rw⁻ 90 q5 ∷
   rw 91 q2 ∷
   re 89 3 (CK20 ∷ []) ∷
   rw 90 q4 ∷
   re 92 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 91 q3 ∷
   rw⁻ 92 q5 ∷
   rw 93 q2 ∷
   re 91 3 (CK20 ∷ []) ∷
   rw 92 q4 ∷
   re 94 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 93 q3 ∷
   rw⁻ 94 q1 ∷
   rw 95 q2 ∷
   re 93 3 (CS02 ∷ []) ∷
   re 95 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 94 q3 ∷
   rw⁻ 95 q1 ∷
   rw 96 q2 ∷
   re 94 3 (CS02 ∷ []) ∷
   re 96 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 95 q3 ∷
   rw⁻ 96 q1 ∷
   rw 97 q2 ∷
   re 95 3 (CS02 ∷ []) ∷
   re 97 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 96 q3 ∷
   rw⁻ 97 q5 ∷
   rw 98 q2 ∷
   re 96 3 (CK20 ∷ []) ∷
   rw 97 q4 ∷
   re 99 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 98 q3 ∷
   rw⁻ 99 q1 ∷
   rw 100 q2 ∷
   re 98 3 (CS02 ∷ []) ∷
   re 100 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 99 q3 ∷
   rw⁻ 100 q1 ∷
   rw 101 q2 ∷
   re 99 3 (CS02 ∷ []) ∷
   re 101 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 100 q3 ∷
   rw⁻ 101 q1 ∷
   rw 102 q2 ∷
   re 100 3 (CS02 ∷ []) ∷
   re 102 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 101 q3 ∷
   rw⁻ 102 q1 ∷
   rw 103 q2 ∷
   re 101 3 (CS02 ∷ []) ∷
   re 103 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 102 q3 ∷
   rw⁻ 103 q1 ∷
   rw 104 q2 ∷
   re 102 3 (CS02 ∷ []) ∷
   re 104 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 103 q3 ∷
   rw⁻ 104 q1 ∷
   rw 105 q2 ∷
   re 103 3 (CS02 ∷ []) ∷
   rw 72 q24 ∷
   re 72 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 71 q3 ∷
   rw⁻ 72 q5 ∷
   rw 73 q2 ∷
   re 71 3 (CK20 ∷ []) ∷
   rw 72 q4 ∷
   re 74 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 73 q3 ∷
   rw⁻ 74 q5 ∷
   rw 75 q2 ∷
   re 73 3 (CK20 ∷ []) ∷
   rw 74 q4 ∷
   re 76 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 75 q3 ∷
   rw⁻ 76 q1 ∷
   rw 77 q2 ∷
   re 75 3 (CS02 ∷ []) ∷
   re 77 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 76 q3 ∷
   rw⁻ 77 q1 ∷
   rw 78 q2 ∷
   re 76 3 (CS02 ∷ []) ∷
   re 78 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 77 q3 ∷
   rw⁻ 78 q1 ∷
   rw 79 q2 ∷
   re 77 3 (CS02 ∷ []) ∷
   re 79 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 78 q3 ∷
   rw⁻ 79 q5 ∷
   rw 80 q2 ∷
   re 78 3 (CK20 ∷ []) ∷
   rw 79 q4 ∷
   re 81 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 80 q3 ∷
   rw⁻ 81 q1 ∷
   rw 82 q2 ∷
   re 80 3 (CS02 ∷ []) ∷
   re 82 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 81 q3 ∷
   rw⁻ 82 q1 ∷
   rw 83 q2 ∷
   re 81 3 (CS02 ∷ []) ∷ []) Eq.refl
