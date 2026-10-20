{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D112 (W : Ws) where

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
  q2 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q3 : Eqn
  q3 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q4 : Eqn
  q4 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q5 : Eqn
  q5 = eqn (CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ []) (CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ S3 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) (wn 664 W)
  q6 : Eqn
  q6 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q7 : Eqn
  q7 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q8 : Eqn
  q8 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q9 : Eqn
  q9 = eqn (CS01 ∷ X2 ∷ []) (X2 ∷ CS01 ∷ []) (low-comm (CS) (X))
  q10 : Eqn
  q10 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q11 : Eqn
  q11 = eqn (CK10 ∷ X2 ∷ []) (X2 ∷ CK10 ∷ []) (low-comm (CK₁₀) (X))
  q12 : Eqn
  q12 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q13 : Eqn
  q13 = eqn (CX21 ∷ X2 ∷ CX23 ∷ X2 ∷ []) (X2 ∷ CX23 ∷ X2 ∷ CX21 ∷ []) (wn 612 W)
  q14 : Eqn
  q14 = eqn (S1 ∷ X2 ∷ []) (X2 ∷ S1 ∷ []) (low-comm ((S ↑)) (X))
  q15 : Eqn
  q15 = eqn (S1 ∷ CX23 ∷ []) (CX23 ∷ S1 ∷ []) (low-comm ((S ↑)) (CX₀₁))
  q16 : Eqn
  q16 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q18 : Eqn
  q18 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q19 : Eqn
  q19 = eqn (CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X2 ∷ CX23 ∷ X2 ∷ []) (X2 ∷ CX23 ∷ X2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) (wn 661 W)
  q20 : Eqn
  q20 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q21 : Eqn
  q21 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q22 : Eqn
  q22 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q23 : Eqn
  q23 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q24 : Eqn
  q24 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q25 : Eqn
  q25 = eqn (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (wn 665 W)
  q26 : Eqn
  q26 = eqn (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) (wn 151 W)

-- Bar(SSSKSS;2,1->0) passes groups of WBar(KiKiSSSKiSSSSSS;~2,3->0) part2: 500 steps
lem-Bar⟨SSSKSS21-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~23-⟶0⟩-part2 : ⟪ (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ S3 ∷ Sw01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX23 ∷ X2 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX23 ∷ X2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sw23 ∷ CX31 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS21-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~23-⟶0⟩-part2 = derive (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ Sw23 ∷ CK20 ∷ Sw23 ∷ Sw01 ∷ S3 ∷ Sw01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX23 ∷ X2 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) (X2 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX23 ∷ X2 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ X2 ∷ CX23 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sw23 ∷ CX31 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw⁻ 68 q1 ∷
   rw 67 q2 ∷
   rw⁻ 66 q1 ∷
   re 67 3 (CK31 ∷ []) ∷
   rw⁻ 65 q3 ∷
   rw⁻ 64 q3 ∷
   rw⁻ 63 q3 ∷
   rw⁻ 62 q3 ∷
   re 61 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 63 q1 ∷
   rw 62 q2 ∷
   rw⁻ 61 q1 ∷
   re 62 3 (CK31 ∷ []) ∷
   rw⁻ 60 q3 ∷
   rw⁻ 59 q3 ∷
   rw⁻ 58 q3 ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 59 q1 ∷
   rw 58 q4 ∷
   rw⁻ 57 q1 ∷
   re 58 3 (CS13 ∷ []) ∷
   re 56 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 58 q1 ∷
   rw 57 q4 ∷
   rw⁻ 56 q1 ∷
   re 57 3 (CS13 ∷ []) ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 57 q1 ∷
   rw 56 q4 ∷
   rw⁻ 55 q1 ∷
   re 56 3 (CS13 ∷ []) ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 56 q1 ∷
   rw 55 q4 ∷
   rw⁻ 54 q1 ∷
   re 55 3 (CS13 ∷ []) ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 55 q1 ∷
   rw 54 q4 ∷
   rw⁻ 53 q1 ∷
   re 54 3 (CS13 ∷ []) ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 54 q1 ∷
   rw 53 q4 ∷
   rw⁻ 52 q1 ∷
   re 53 3 (CS13 ∷ []) ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 53 q1 ∷
   rw 52 q4 ∷
   rw⁻ 51 q1 ∷
   re 52 3 (CS13 ∷ []) ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 52 q1 ∷
   rw 51 q4 ∷
   rw⁻ 50 q1 ∷
   re 51 3 (CS13 ∷ []) ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 51 q1 ∷
   rw 50 q4 ∷
   rw⁻ 49 q1 ∷
   re 50 3 (CS13 ∷ []) ∷
   rw⁻ 48 q3 ∷
   re 47 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q1 ∷
   rw 48 q2 ∷
   rw⁻ 47 q1 ∷
   re 48 3 (CK31 ∷ []) ∷
   rw⁻ 46 q3 ∷
   rw⁻ 45 q3 ∷
   rw⁻ 44 q3 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q1 ∷
   rw 44 q4 ∷
   rw⁻ 43 q1 ∷
   re 44 3 (CS13 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q1 ∷
   rw 43 q4 ∷
   rw⁻ 42 q1 ∷
   re 43 3 (CS13 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q1 ∷
   rw 42 q4 ∷
   rw⁻ 41 q1 ∷
   re 42 3 (CS13 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q1 ∷
   rw 41 q4 ∷
   rw⁻ 40 q1 ∷
   re 41 3 (CS13 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q1 ∷
   rw 40 q4 ∷
   rw⁻ 39 q1 ∷
   re 40 3 (CS13 ∷ []) ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q1 ∷
   rw 39 q4 ∷
   rw⁻ 38 q1 ∷
   re 39 3 (CS13 ∷ []) ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q1 ∷
   rw 38 q4 ∷
   rw⁻ 37 q1 ∷
   re 38 3 (CS13 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q1 ∷
   rw 37 q4 ∷
   rw⁻ 36 q1 ∷
   re 37 3 (CS13 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q1 ∷
   rw 36 q4 ∷
   rw⁻ 35 q1 ∷
   re 36 3 (CS13 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q1 ∷
   rw 35 q4 ∷
   rw⁻ 34 q1 ∷
   re 35 3 (CS13 ∷ []) ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q1 ∷
   rw 34 q4 ∷
   rw⁻ 33 q1 ∷
   re 34 3 (CS13 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q1 ∷
   rw 33 q4 ∷
   rw⁻ 32 q1 ∷
   re 33 3 (CS13 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q1 ∷
   rw 32 q4 ∷
   rw⁻ 31 q1 ∷
   re 32 3 (CS13 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q1 ∷
   rw 31 q4 ∷
   rw⁻ 30 q1 ∷
   re 31 3 (CS13 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q1 ∷
   rw 30 q4 ∷
   rw⁻ 29 q1 ∷
   re 30 3 (CS13 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q1 ∷
   rw 29 q4 ∷
   rw⁻ 28 q1 ∷
   re 29 3 (CS13 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q1 ∷
   rw 28 q4 ∷
   rw⁻ 27 q1 ∷
   re 28 3 (CS13 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q1 ∷
   rw 27 q4 ∷
   rw⁻ 26 q1 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 25 q4 ∷
   rw 24 q4 ∷
   rw 23 q2 ∷
   rw 22 q4 ∷
   rw 21 q4 ∷
   rw 20 q4 ∷
   rw 21 q5 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q1 ∷
   rw 21 q6 ∷
   rw 22 q1 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q1 ∷
   rw 22 q6 ∷
   rw 23 q1 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q1 ∷
   rw 23 q6 ∷
   rw 24 q1 ∷
   re 22 3 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q1 ∷
   rw 24 q6 ∷
   rw 25 q1 ∷
   re 23 3 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   rw 25 q6 ∷
   rw 26 q1 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   rw 26 q6 ∷
   rw 27 q1 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   rw 27 q6 ∷
   rw 28 q1 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   rw 28 q6 ∷
   rw 29 q1 ∷
   re 27 3 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   rw 29 q6 ∷
   rw 30 q1 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   rw 30 q6 ∷
   rw 31 q1 ∷
   re 29 3 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q1 ∷
   rw 31 q6 ∷
   rw 32 q1 ∷
   re 30 3 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   rw 32 q6 ∷
   rw 33 q1 ∷
   re 31 3 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   rw 33 q6 ∷
   rw 34 q1 ∷
   re 32 3 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   rw 34 q6 ∷
   rw 35 q1 ∷
   re 33 3 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   rw 35 q6 ∷
   rw 36 q1 ∷
   re 34 3 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q1 ∷
   rw 36 q6 ∷
   rw 37 q1 ∷
   re 35 3 (CS03 ∷ []) ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q1 ∷
   rw 37 q6 ∷
   rw 38 q1 ∷
   re 36 3 (CS03 ∷ []) ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q1 ∷
   rw 38 q6 ∷
   rw 39 q1 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 38 q3 ∷
   rw 39 q3 ∷
   rw 40 q3 ∷
   re 42 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 41 q1 ∷
   rw 42 q7 ∷
   rw 43 q1 ∷
   re 41 3 (CK30 ∷ []) ∷
   rw 42 q3 ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q1 ∷
   rw 44 q6 ∷
   rw 45 q1 ∷
   re 43 3 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 44 q1 ∷
   rw 45 q6 ∷
   rw 46 q1 ∷
   re 44 3 (CS03 ∷ []) ∷
   re 46 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 45 q1 ∷
   rw 46 q6 ∷
   rw 47 q1 ∷
   re 45 3 (CS03 ∷ []) ∷
   re 47 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 46 q1 ∷
   rw 47 q6 ∷
   rw 48 q1 ∷
   re 46 3 (CS03 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 47 q1 ∷
   rw 48 q6 ∷
   rw 49 q1 ∷
   re 47 3 (CS03 ∷ []) ∷
   re 49 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 48 q1 ∷
   rw 49 q6 ∷
   rw 50 q1 ∷
   re 48 3 (CS03 ∷ []) ∷
   re 50 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 49 q1 ∷
   rw 50 q6 ∷
   rw 51 q1 ∷
   re 49 3 (CS03 ∷ []) ∷
   re 51 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 50 q1 ∷
   rw 51 q6 ∷
   rw 52 q1 ∷
   re 50 3 (CS03 ∷ []) ∷
   re 52 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 51 q1 ∷
   rw 52 q6 ∷
   rw 53 q1 ∷
   re 51 3 (CS03 ∷ []) ∷
   rw 52 q3 ∷
   rw 53 q3 ∷
   rw 54 q3 ∷
   re 56 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 55 q1 ∷
   rw 56 q7 ∷
   rw 57 q1 ∷
   re 55 3 (CK30 ∷ []) ∷
   rw 56 q3 ∷
   rw 57 q3 ∷
   rw 58 q3 ∷
   rw 59 q3 ∷
   re 61 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 60 q1 ∷
   rw 61 q7 ∷
   rw 62 q1 ∷
   re 60 3 (CK30 ∷ []) ∷
   rw 61 q3 ∷
   rw 62 q6 ∷
   rw 63 q6 ∷
   rw 64 q6 ∷
   rw 65 q7 ∷
   rw 66 q6 ∷
   rw 67 q6 ∷
   rw 68 q8 ∷
   rw 92 q9 ∷
   rw 93 q10 ∷
   rw 94 q9 ∷
   rw 91 q9 ∷
   rw 92 q10 ∷
   rw 93 q9 ∷
   rw 90 q11 ∷
   rw 91 q12 ∷
   rw 92 q11 ∷
   rw 89 q9 ∷
   rw 90 q10 ∷
   rw 91 q9 ∷
   rw 88 q9 ∷
   rw 89 q10 ∷
   rw 90 q9 ∷
   rw 87 q9 ∷
   rw 88 q10 ∷
   rw 89 q9 ∷
   rw 86 q13 ∷
   rw 85 q9 ∷
   rw 86 q10 ∷
   rw 87 q9 ∷
   rw 84 q9 ∷
   rw 85 q10 ∷
   rw 86 q9 ∷
   rw 83 q9 ∷
   rw 84 q10 ∷
   rw 85 q9 ∷
   rw 82 q9 ∷
   rw 83 q10 ∷
   rw 84 q9 ∷
   rw 81 q9 ∷
   rw 82 q10 ∷
   rw 83 q9 ∷
   rw 80 q9 ∷
   rw 81 q10 ∷
   rw 82 q9 ∷
   rw 79 q9 ∷
   rw 80 q10 ∷
   rw 81 q9 ∷
   rw 78 q9 ∷
   rw 79 q10 ∷
   rw 80 q9 ∷
   rw 77 q9 ∷
   rw 78 q10 ∷
   rw 79 q9 ∷
   rw 76 q14 ∷
   rw 77 q15 ∷
   rw 78 q14 ∷
   rw 75 q11 ∷
   rw 76 q12 ∷
   rw 77 q11 ∷
   rw 74 q9 ∷
   rw 75 q10 ∷
   rw 76 q9 ∷
   rw 73 q9 ∷
   rw 74 q10 ∷
   rw 75 q9 ∷
   rw 72 q9 ∷
   rw 73 q10 ∷
   rw 74 q9 ∷
   rw 71 q9 ∷
   rw 72 q10 ∷
   rw 73 q9 ∷
   rw 70 q9 ∷
   rw 71 q10 ∷
   rw 72 q9 ∷
   rw 69 q9 ∷
   rw 70 q10 ∷
   rw 71 q9 ∷
   rw 68 q13 ∷
   rw 71 q16 ∷
   rw⁻ 70 q17 ∷
   rw⁻ 69 q18 ∷
   rw⁻ 68 q17 ∷
   rw 67 q4 ∷
   rw 66 q4 ∷
   rw 65 q2 ∷
   rw 64 q4 ∷
   rw 63 q4 ∷
   rw 62 q4 ∷
   rw 63 q19 ∷
   rw 62 q17 ∷
   rw 63 q18 ∷
   rw 64 q17 ∷
   rw 65 q6 ∷
   rw 66 q6 ∷
   rw 67 q6 ∷
   rw 68 q7 ∷
   rw 69 q6 ∷
   rw 70 q6 ∷
   rw 71 q8 ∷
   rw 111 q20 ∷
   re 110 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 112 q21 ∷
   re 109 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 111 q21 ∷
   re 108 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 110 q21 ∷
   re 107 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 109 q21 ∷
   re 106 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 108 q21 ∷
   re 105 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 107 q21 ∷
   rw 104 q22 ∷
   re 103 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 105 q21 ∷
   re 102 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 104 q21 ∷
   re 101 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 103 q21 ∷
   re 100 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 102 q21 ∷
   rw 99 q22 ∷
   re 98 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 100 q21 ∷
   rw 97 q22 ∷
   re 96 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 98 q21 ∷
   rw 95 q23 ∷
   rw 94 q23 ∷
   rw 93 q24 ∷
   rw 92 q23 ∷
   rw 91 q23 ∷
   rw 90 q23 ∷
   rw 91 q25 ∷
   rw 92 q20 ∷
   re 90 3 (CK30 ∷ []) ∷
   rw 91 q26 ∷
   rw 94 q20 ∷
   re 92 3 (CK30 ∷ []) ∷
   rw 93 q26 ∷
   rw 96 q20 ∷
   re 94 3 (CS03 ∷ []) ∷
   rw 97 q20 ∷
   re 95 3 (CS03 ∷ []) ∷
   rw 98 q20 ∷
   re 96 3 (CS03 ∷ []) ∷
   rw 99 q20 ∷
   re 97 3 (CK30 ∷ []) ∷
   rw 98 q26 ∷
   rw 101 q20 ∷
   re 99 3 (CS03 ∷ []) ∷
   rw 102 q20 ∷
   re 100 3 (CS03 ∷ []) ∷
   rw 103 q20 ∷
   re 101 3 (CS03 ∷ []) ∷
   rw 104 q20 ∷
   re 102 3 (CS03 ∷ []) ∷
   rw 105 q20 ∷
   re 103 3 (CS03 ∷ []) ∷
   rw 106 q20 ∷
   re 104 3 (CS03 ∷ []) ∷
   rw⁻ 105 q23 ∷
   rw⁻ 106 q23 ∷
   rw⁻ 107 q23 ∷
   rw⁻ 108 q24 ∷
   rw⁻ 109 q23 ∷
   rw⁻ 110 q23 ∷
   rw 111 q21 ∷
   re 90 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 89 q20 ∷
   re 90 3 (CX31 ∷ []) ∷ []) Eq.refl
