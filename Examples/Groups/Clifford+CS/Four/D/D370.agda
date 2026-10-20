{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D370 (W : Ws) where

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
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q4 : Eqn
  q4 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q5 : Eqn
  q5 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q6 : Eqn
  q6 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q8 : Eqn
  q8 = eqn (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) (wn 1006 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X3 CS03 X3]: 127 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS03-X3 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS03-X3 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ [])
  (rw 34 q1 ∷
   rw⁻ 33 q2 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q3 ∷
   rw 33 q4 ∷
   rw⁻ 32 q3 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw⁻ 31 q2 ∷
   rw 30 q4 ∷
   rw 29 q4 ∷
   rw 28 q5 ∷
   rw 27 q4 ∷
   rw 26 q4 ∷
   rw 25 q4 ∷
   rw⁻ 24 q6 ∷
   rw 23 q4 ∷
   rw 22 q4 ∷
   rw 21 q4 ∷
   rw 20 q4 ∷
   rw 19 q4 ∷
   rw 18 q4 ∷
   rw 17 q4 ∷
   rw 16 q4 ∷
   rw 15 q4 ∷
   rw⁻ 14 q7 ∷
   rw 13 q5 ∷
   rw 12 q4 ∷
   rw 11 q4 ∷
   rw 10 q4 ∷
   rw 9 q4 ∷
   rw 8 q4 ∷
   rw 7 q4 ∷
   rw⁻ 6 q6 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw 6 q4 ∷
   rw⁻ 5 q3 ∷
   re 6 3 (CS13 ∷ []) ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q3 ∷
   rw 5 q4 ∷
   rw⁻ 4 q3 ∷
   re 5 3 (CS13 ∷ []) ∷
   re 3 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 4 q5 ∷
   rw⁻ 3 q3 ∷
   re 4 3 (CK31 ∷ []) ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q3 ∷
   rw 3 q4 ∷
   rw⁻ 2 q3 ∷
   re 3 3 (CS13 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 2 q4 ∷
   rw⁻ 1 q3 ∷
   re 2 3 (CS13 ∷ []) ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 1 q4 ∷
   rw⁻ 0 q3 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q8 ∷
   rw 0 q2 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q3 ∷
   rw 2 q9 ∷
   rw 3 q3 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q2 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q3 ∷
   rw 4 q9 ∷
   rw 5 q3 ∷
   re 3 3 (CS03 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q3 ∷
   rw 5 q9 ∷
   rw 6 q3 ∷
   re 4 3 (CS03 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q3 ∷
   rw 6 q9 ∷
   rw 7 q3 ∷
   re 5 3 (CS03 ∷ []) ∷
   re 7 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   rw 7 q10 ∷
   rw 8 q3 ∷
   re 6 3 (CK30 ∷ []) ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   rw 8 q9 ∷
   rw 9 q3 ∷
   re 7 3 (CS03 ∷ []) ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   rw 9 q9 ∷
   rw 10 q3 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q6 ∷
   rw 10 q9 ∷
   rw 11 q9 ∷
   rw 12 q9 ∷
   rw 13 q9 ∷
   rw 14 q9 ∷
   rw 15 q9 ∷
   rw 16 q10 ∷
   rw 17 q7 ∷
   rw 18 q9 ∷
   rw 19 q9 ∷
   rw 20 q9 ∷
   rw 21 q9 ∷
   rw 22 q9 ∷
   rw 23 q9 ∷
   rw 24 q9 ∷
   rw 25 q9 ∷
   rw 26 q9 ∷
   rw 27 q6 ∷
   rw 28 q9 ∷
   rw 29 q9 ∷
   rw 30 q9 ∷
   rw 31 q10 ∷
   rw 32 q9 ∷
   rw 33 q9 ∷
   rw 34 q11 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q13 : Eqn
  q13 = eqn (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) (wn 1007 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X3 CSd03 X3]: 127 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CSd03-X3 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CSd03-X3 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ [])
  (rw 34 q1 ∷
   rw⁻ 33 q2 ∷
   re 32 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q3 ∷
   rw 33 q12 ∷
   rw⁻ 32 q3 ∷
   re 33 3 (CS13⁻ ∷ []) ∷
   rw⁻ 31 q2 ∷
   rw 30 q4 ∷
   rw 29 q4 ∷
   rw 28 q5 ∷
   rw 27 q4 ∷
   rw 26 q4 ∷
   rw 25 q4 ∷
   rw⁻ 24 q6 ∷
   rw 23 q4 ∷
   rw 22 q4 ∷
   rw 21 q4 ∷
   rw 20 q4 ∷
   rw 19 q4 ∷
   rw 18 q4 ∷
   rw 17 q4 ∷
   rw 16 q4 ∷
   rw 15 q4 ∷
   rw⁻ 14 q7 ∷
   rw 13 q5 ∷
   rw 12 q4 ∷
   rw 11 q4 ∷
   rw 10 q4 ∷
   rw 9 q4 ∷
   rw 8 q4 ∷
   rw 7 q4 ∷
   rw⁻ 6 q6 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw 6 q4 ∷
   rw⁻ 5 q3 ∷
   re 6 3 (CS13 ∷ []) ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q3 ∷
   rw 5 q4 ∷
   rw⁻ 4 q3 ∷
   re 5 3 (CS13 ∷ []) ∷
   re 3 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 4 q5 ∷
   rw⁻ 3 q3 ∷
   re 4 3 (CK31 ∷ []) ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q3 ∷
   rw 3 q4 ∷
   rw⁻ 2 q3 ∷
   re 3 3 (CS13 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 2 q4 ∷
   rw⁻ 1 q3 ∷
   re 2 3 (CS13 ∷ []) ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 1 q4 ∷
   rw⁻ 0 q3 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q13 ∷
   rw 0 q2 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 1 q3 ∷
   rw 2 q14 ∷
   rw 3 q3 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q2 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q3 ∷
   rw 4 q9 ∷
   rw 5 q3 ∷
   re 3 3 (CS03 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q3 ∷
   rw 5 q9 ∷
   rw 6 q3 ∷
   re 4 3 (CS03 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q3 ∷
   rw 6 q9 ∷
   rw 7 q3 ∷
   re 5 3 (CS03 ∷ []) ∷
   re 7 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   rw 7 q10 ∷
   rw 8 q3 ∷
   re 6 3 (CK30 ∷ []) ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   rw 8 q9 ∷
   rw 9 q3 ∷
   re 7 3 (CS03 ∷ []) ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   rw 9 q9 ∷
   rw 10 q3 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q6 ∷
   rw 10 q9 ∷
   rw 11 q9 ∷
   rw 12 q9 ∷
   rw 13 q9 ∷
   rw 14 q9 ∷
   rw 15 q9 ∷
   rw 16 q10 ∷
   rw 17 q7 ∷
   rw 18 q9 ∷
   rw 19 q9 ∷
   rw 20 q9 ∷
   rw 21 q9 ∷
   rw 22 q9 ∷
   rw 23 q9 ∷
   rw 24 q9 ∷
   rw 25 q9 ∷
   rw 26 q9 ∷
   rw 27 q6 ∷
   rw 28 q9 ∷
   rw 29 q9 ∷
   rw 30 q9 ∷
   rw 31 q10 ∷
   rw 32 q9 ∷
   rw 33 q9 ∷
   rw 34 q11 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q16 : Eqn
  q16 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q17 : Eqn
  q17 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q18 : Eqn
  q18 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q19 : Eqn
  q19 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q20 : Eqn
  q20 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q21 : Eqn
  q21 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (X2 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (wn 1008 W)
  q22 : Eqn
  q22 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CS03 X3]: 85 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS03-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS03-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 32 q15 ∷
   rw 31 q16 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q17 ∷
   rw 29 q16 ∷
   rw 28 q18 ∷
   rw 27 q18 ∷
   rw 26 q19 ∷
   rw 25 q18 ∷
   rw 24 q19 ∷
   rw 23 q19 ∷
   re 22 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 24 q17 ∷
   rw 21 q19 ∷
   rw 20 q19 ∷
   rw 19 q19 ∷
   rw 18 q19 ∷
   rw 17 q19 ∷
   rw 16 q19 ∷
   rw 15 q20 ∷
   rw 14 q18 ∷
   rw 13 q19 ∷
   rw 12 q19 ∷
   rw 11 q19 ∷
   rw 10 q20 ∷
   rw 9 q18 ∷
   rw 8 q20 ∷
   rw 7 q18 ∷
   re 6 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 8 q17 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 7 q17 ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 6 q17 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q17 ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 4 q17 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q17 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q17 ∷
   rw 1 q21 ∷
   rw 0 q22 ∷
   rw 3 q15 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q22 ∷
   rw 5 q15 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 6 q15 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 7 q15 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 8 q15 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 9 q15 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 10 q15 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 11 q15 ∷
   re 9 3 (CX31 ∷ []) ∷
   rw⁻ 10 q18 ∷
   rw⁻ 11 q20 ∷
   rw⁻ 12 q18 ∷
   rw⁻ 13 q20 ∷
   rw⁻ 14 q19 ∷
   rw⁻ 15 q19 ∷
   rw⁻ 16 q19 ∷
   rw⁻ 17 q18 ∷
   rw⁻ 18 q20 ∷
   rw⁻ 19 q19 ∷
   rw⁻ 20 q19 ∷
   rw⁻ 21 q19 ∷
   rw⁻ 22 q19 ∷
   rw⁻ 23 q19 ∷
   rw⁻ 24 q19 ∷
   rw 27 q15 ∷
   re 25 3 (CX31 ∷ []) ∷
   rw⁻ 26 q19 ∷
   rw⁻ 27 q19 ∷
   rw⁻ 28 q18 ∷
   rw⁻ 29 q19 ∷
   rw⁻ 30 q18 ∷
   rw⁻ 31 q18 ∷
   rw 32 q17 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (X2 ∷ CS02⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (wn 1009 W)

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CSd03 X3]: 85 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd03-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd03-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (X3 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 32 q15 ∷
   rw 31 q16 ∷
   re 30 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 32 q17 ∷
   rw 29 q16 ∷
   rw 28 q18 ∷
   rw 27 q18 ∷
   rw 26 q19 ∷
   rw 25 q18 ∷
   rw 24 q19 ∷
   rw 23 q19 ∷
   re 22 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 24 q17 ∷
   rw 21 q19 ∷
   rw 20 q19 ∷
   rw 19 q19 ∷
   rw 18 q19 ∷
   rw 17 q19 ∷
   rw 16 q19 ∷
   rw 15 q20 ∷
   rw 14 q18 ∷
   rw 13 q19 ∷
   rw 12 q19 ∷
   rw 11 q19 ∷
   rw 10 q20 ∷
   rw 9 q18 ∷
   rw 8 q20 ∷
   rw 7 q18 ∷
   re 6 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 8 q17 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 7 q17 ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 6 q17 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q17 ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 4 q17 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q17 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q17 ∷
   rw 1 q23 ∷
   rw 0 q22 ∷
   rw 3 q15 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q22 ∷
   rw 5 q15 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 6 q15 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 7 q15 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 8 q15 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 9 q15 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 10 q15 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 11 q15 ∷
   re 9 3 (CX31 ∷ []) ∷
   rw⁻ 10 q18 ∷
   rw⁻ 11 q20 ∷
   rw⁻ 12 q18 ∷
   rw⁻ 13 q20 ∷
   rw⁻ 14 q19 ∷
   rw⁻ 15 q19 ∷
   rw⁻ 16 q19 ∷
   rw⁻ 17 q18 ∷
   rw⁻ 18 q20 ∷
   rw⁻ 19 q19 ∷
   rw⁻ 20 q19 ∷
   rw⁻ 21 q19 ∷
   rw⁻ 22 q19 ∷
   rw⁻ 23 q19 ∷
   rw⁻ 24 q19 ∷
   rw 27 q15 ∷
   re 25 3 (CX31 ∷ []) ∷
   rw⁻ 26 q19 ∷
   rw⁻ 27 q19 ∷
   rw⁻ 28 q18 ∷
   rw⁻ 29 q19 ∷
   rw⁻ 30 q18 ∷
   rw⁻ 31 q18 ∷
   rw 32 q17 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = eqn (X3 ∷ CK32⁻ ∷ X3 ∷ Toff123 ∷ []) (Toff123 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (wn 404 W)

-- pass [X3 CKd32 X3] [TOFF123]: 1 steps
lem-pass-X3-CKd32-X3-vs-TOFF123 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd32-X3-vs-TOFF123 = derive (X3 ∷ CK32⁻ ∷ X3 ∷ Toff123 ∷ []) (Toff123 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ [])
  (rw 0 q24 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = eqn (CCZ123 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ CCZ123 ∷ []) (wn 1010 W)

-- pass [CCZ123] [X3 CS13 X3]: 1 steps
lem-pass-CCZ123-vs-X3-CS13-X3 : ⟪ (CCZ123 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X3-CS13-X3 = derive (CCZ123 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ CCZ123 ∷ [])
  (rw 0 q25 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = eqn (CCZ123 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (X3 ∷ CK31 ∷ X3 ∷ CCZ123 ∷ []) (wn 1011 W)

-- pass [CCZ123] [X3 CK31 X3]: 1 steps
lem-pass-CCZ123-vs-X3-CK31-X3 : ⟪ (CCZ123 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X3-CK31-X3 = derive (CCZ123 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (X3 ∷ CK31 ∷ X3 ∷ CCZ123 ∷ [])
  (rw 0 q26 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = eqn (CZ12 ∷ CS13 ∷ []) (CS13 ∷ CZ12 ∷ []) (wn 1012 W)

-- pass [CZ12] [CS13]: 1 steps
lem-pass-CZ12-vs-CS13 : ⟪ (CZ12 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CZ12 ∷ []) ⟫ʷ
lem-pass-CZ12-vs-CS13 = derive (CZ12 ∷ CS13 ∷ []) (CS13 ∷ CZ12 ∷ [])
  (rw 0 q27 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = eqn (CZ12 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CZ12 ∷ []) (wn 1013 W)

-- pass [CZ12] [CSd13]: 1 steps
lem-pass-CZ12-vs-CSd13 : ⟪ (CZ12 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CZ12 ∷ []) ⟫ʷ
lem-pass-CZ12-vs-CSd13 = derive (CZ12 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CZ12 ∷ [])
  (rw 0 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = eqn (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) (wn 21 W)
  q30 : Eqn
  q30 = eqn (CZ01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CZ01 ∷ []) (low-comm (CZ) ((CS • CS • CS)))
  q31 : Eqn
  q31 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)

-- pass [CZ02] [CSd13]: 15 steps
lem-pass-CZ02-vs-CSd13 : ⟪ (CZ02 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CZ02 ∷ []) ⟫ʷ
lem-pass-CZ02-vs-CSd13 = derive (CZ02 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CZ02 ∷ [])
  (re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 0 q15 ∷
   re 1 3 (CZ03 ∷ []) ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q15 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw 4 q29 ∷
   rw 3 q30 ∷
   rw 2 q31 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 1 q17 ∷
   re 2 5 (CZ03 ∷ []) ∷
   re 2 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ∷
   rw 4 q17 ∷
   re 0 3 (CS13⁻ ∷ []) ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = eqn (CCZ123 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (X3 ∷ CK31⁻ ∷ X3 ∷ CCZ123 ∷ []) (wn 1014 W)

-- pass [CCZ123] [X3 CKd31 X3]: 1 steps
lem-pass-CCZ123-vs-X3-CKd31-X3 : ⟪ (CCZ123 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X3-CKd31-X3 = derive (CCZ123 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (X3 ∷ CK31⁻ ∷ X3 ∷ CCZ123 ∷ [])
  (rw 0 q32 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = eqn (CCZ123 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CCZ123 ∷ []) (wn 1015 W)

-- pass [CCZ123] [X3 CSd13 X3]: 1 steps
lem-pass-CCZ123-vs-X3-CSd13-X3 : ⟪ (CCZ123 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X3-CSd13-X3 = derive (CCZ123 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ CS13⁻ ∷ X3 ∷ CCZ123 ∷ [])
  (rw 0 q33 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = eqn (X3 ∷ CK32 ∷ X3 ∷ Toff123 ∷ []) (Toff123 ∷ X3 ∷ CK32 ∷ X3 ∷ []) (wn 419 W)

-- pass [X3 CK32 X3] [TOFF123]: 1 steps
lem-pass-X3-CK32-X3-vs-TOFF123 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ Toff123 ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK32-X3-vs-TOFF123 = derive (X3 ∷ CK32 ∷ X3 ∷ Toff123 ∷ []) (Toff123 ∷ X3 ∷ CK32 ∷ X3 ∷ [])
  (rw 0 q34 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (wn 1016 W)

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CS13 X3]: 85 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 32 q15 ∷
   rw 31 q16 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q17 ∷
   rw 29 q16 ∷
   rw 28 q18 ∷
   rw 27 q18 ∷
   rw 26 q19 ∷
   rw 25 q18 ∷
   rw 24 q19 ∷
   rw 23 q19 ∷
   re 22 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 24 q17 ∷
   rw 21 q19 ∷
   rw 20 q19 ∷
   rw 19 q19 ∷
   rw 18 q19 ∷
   rw 17 q19 ∷
   rw 16 q19 ∷
   rw 15 q20 ∷
   rw 14 q18 ∷
   rw 13 q19 ∷
   rw 12 q19 ∷
   rw 11 q19 ∷
   rw 10 q20 ∷
   rw 9 q18 ∷
   rw 8 q20 ∷
   rw 7 q18 ∷
   re 6 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 8 q17 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 7 q17 ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 6 q17 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q17 ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 4 q17 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q17 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q17 ∷
   rw 1 q35 ∷
   rw 0 q22 ∷
   rw 3 q15 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 2 q22 ∷
   rw 5 q15 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 6 q15 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 7 q15 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 8 q15 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 9 q15 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 10 q15 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 11 q15 ∷
   re 9 3 (CX31 ∷ []) ∷
   rw⁻ 10 q18 ∷
   rw⁻ 11 q20 ∷
   rw⁻ 12 q18 ∷
   rw⁻ 13 q20 ∷
   rw⁻ 14 q19 ∷
   rw⁻ 15 q19 ∷
   rw⁻ 16 q19 ∷
   rw⁻ 17 q18 ∷
   rw⁻ 18 q20 ∷
   rw⁻ 19 q19 ∷
   rw⁻ 20 q19 ∷
   rw⁻ 21 q19 ∷
   rw⁻ 22 q19 ∷
   rw⁻ 23 q19 ∷
   rw⁻ 24 q19 ∷
   rw 27 q15 ∷
   re 25 3 (CX31 ∷ []) ∷
   rw⁻ 26 q19 ∷
   rw⁻ 27 q19 ∷
   rw⁻ 28 q18 ∷
   rw⁻ 29 q19 ∷
   rw⁻ 30 q18 ∷
   rw⁻ 31 q18 ∷
   rw 32 q17 ∷ []) Eq.refl
