{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD637 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D637 (W : Ws) (Sᴰ : SD637) where

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
  lem-Bar⟨SSSKSS32-⟶0⟩-passes-factors-of-X0-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X0-X3 : St 1534
  lem-Bar⟨SSSKSS32-⟶0⟩-passes-factors-of-X0-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X0-X3 = pickᴰ 0 Sᴰ
  lem-pass-X0-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-X0-vs-X3-TOFF213-X3 : St 1535
  lem-pass-X0-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-X0-vs-X3-TOFF213-X3 = pickᴰ 1 Sᴰ

private
  q1 : Eqn
  q1 = eqn (Toff213 ∷ []) (X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ []) (wn 1389 W)
  q2 : Eqn
  q2 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q3 : Eqn
  q3 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q4 : Eqn
  q4 = eqn (X0 ∷ Sw01 ∷ []) (Sw01 ∷ X1 ∷ []) (wn 1106 W)
  q5 : Eqn
  q5 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q6 : Eqn
  q6 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q7 : Eqn
  q7 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q8 : Eqn
  q8 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q9 : Eqn
  q9 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q10 : Eqn
  q10 = eqn (X3 ∷ X1 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X1 ∷ X3 ∷ []) (X1 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X1 ∷ X3 ∷ []) (wn 1922 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ []) (wn 317 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q13 : Eqn
  q13 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q15 : Eqn
  q15 = eqn (X0 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X3 ∷ Toff213 ∷ X3 ∷ []) (X3 ∷ Toff213 ∷ X3 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ []) lem-pass-X0-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-X0-vs-X3-TOFF213-X3
  q16 : Eqn
  q16 = eqn (X3 ∷ X1 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X1 ∷ []) (X1 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X1 ∷ X3 ∷ X3 ∷ []) (wn 1923 W)
  q17 : Eqn
  q17 = eqn (X3 ∷ X3 ∷ Toff213 ∷ X3 ∷ X3 ∷ []) (Toff213 ∷ []) (wn 1392 W)

-- pass [TOFF213] [X0 X3 CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20 X0 X3]: 237 steps
lem-pass-TOFF213-vs-X0-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-X0-X3 : ⟪ (Toff213 ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X3 ∷ Toff213 ∷ []) ⟫ʷ
lem-pass-TOFF213-vs-X0-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-X0-X3 = derive (Toff213 ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X3 ∷ Toff213 ∷ [])
  (rw 0 q1 ∷
   rw 38 q2 ∷
   rw⁻ 37 q3 ∷
   rw 36 q4 ∷
   rw 35 q5 ∷
   rw 34 q5 ∷
   rw 33 q6 ∷
   rw 32 q5 ∷
   rw 31 q6 ∷
   rw 30 q6 ∷
   rw⁻ 29 q7 ∷
   rw 28 q6 ∷
   rw 27 q6 ∷
   rw 26 q6 ∷
   rw 25 q6 ∷
   rw 24 q6 ∷
   rw 23 q6 ∷
   rw⁻ 22 q8 ∷
   rw 21 q5 ∷
   rw 20 q6 ∷
   rw 19 q6 ∷
   rw 18 q6 ∷
   rw⁻ 17 q8 ∷
   rw 16 q5 ∷
   rw⁻ 15 q8 ∷
   rw 14 q5 ∷
   rw⁻ 13 q7 ∷
   re 12 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q9 ∷
   rw 13 q5 ∷
   rw⁻ 12 q9 ∷
   re 13 3 (CK31 ∷ []) ∷
   re 11 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q9 ∷
   rw 12 q5 ∷
   rw⁻ 11 q9 ∷
   re 12 3 (CK31 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q9 ∷
   rw 11 q6 ∷
   rw⁻ 10 q9 ∷
   re 11 3 (CS13 ∷ []) ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q9 ∷
   rw 10 q5 ∷
   rw⁻ 9 q9 ∷
   re 10 3 (CK31 ∷ []) ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q9 ∷
   rw 9 q6 ∷
   rw⁻ 8 q9 ∷
   re 9 3 (CS13 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q9 ∷
   rw 8 q6 ∷
   rw⁻ 7 q9 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 6 q3 ∷
   rw 5 q4 ∷
   rw⁻ 4 q3 ∷
   rw 5 q10 ∷
   rw 4 q11 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q9 ∷
   rw 6 q12 ∷
   rw 7 q9 ∷
   re 5 3 (CS03 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q9 ∷
   rw 7 q12 ∷
   rw 8 q9 ∷
   re 6 3 (CS03 ∷ []) ∷
   re 8 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 7 q9 ∷
   rw 8 q13 ∷
   rw 9 q9 ∷
   re 7 3 (CK30 ∷ []) ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q9 ∷
   rw 9 q12 ∷
   rw 10 q9 ∷
   re 8 3 (CS03 ∷ []) ∷
   re 10 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 9 q9 ∷
   rw 10 q13 ∷
   rw 11 q9 ∷
   re 9 3 (CK30 ∷ []) ∷
   re 11 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 10 q9 ∷
   rw 11 q13 ∷
   rw 12 q9 ∷
   re 10 3 (CK30 ∷ []) ∷
   rw 11 q7 ∷
   rw 12 q13 ∷
   rw 13 q8 ∷
   rw 14 q13 ∷
   rw 15 q8 ∷
   rw 16 q12 ∷
   rw 17 q12 ∷
   rw 18 q12 ∷
   rw 19 q13 ∷
   rw 20 q8 ∷
   rw 21 q12 ∷
   rw 22 q12 ∷
   rw 23 q12 ∷
   rw 24 q12 ∷
   rw 25 q12 ∷
   rw 26 q12 ∷
   rw 27 q7 ∷
   rw 28 q12 ∷
   rw 29 q12 ∷
   rw 30 q13 ∷
   rw 31 q12 ∷
   rw 32 q13 ∷
   rw 33 q13 ∷
   rw 34 q11 ∷
   rw 35 q3 ∷
   rw 36 q14 ∷
   rw⁻ 1 q15 ∷
   rw 32 q2 ∷
   rw 31 q4 ∷
   rw 30 q5 ∷
   rw 29 q5 ∷
   rw 28 q6 ∷
   rw 27 q5 ∷
   rw 26 q6 ∷
   rw 25 q6 ∷
   rw⁻ 24 q7 ∷
   rw 23 q6 ∷
   rw 22 q6 ∷
   rw 21 q6 ∷
   rw 20 q6 ∷
   rw 19 q6 ∷
   rw 18 q6 ∷
   rw⁻ 17 q8 ∷
   rw 16 q5 ∷
   rw 15 q6 ∷
   rw 14 q6 ∷
   rw 13 q6 ∷
   rw⁻ 12 q8 ∷
   rw 11 q5 ∷
   rw⁻ 10 q8 ∷
   rw 9 q5 ∷
   rw⁻ 8 q7 ∷
   re 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q9 ∷
   rw 8 q5 ∷
   rw⁻ 7 q9 ∷
   re 8 3 (CK31 ∷ []) ∷
   re 6 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q9 ∷
   rw 7 q5 ∷
   rw⁻ 6 q9 ∷
   re 7 3 (CK31 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q9 ∷
   rw 6 q6 ∷
   rw⁻ 5 q9 ∷
   re 6 3 (CS13 ∷ []) ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q9 ∷
   rw 5 q5 ∷
   rw⁻ 4 q9 ∷
   re 5 3 (CK31 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q9 ∷
   rw 4 q6 ∷
   rw⁻ 3 q9 ∷
   re 4 3 (CS13 ∷ []) ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q9 ∷
   rw 3 q6 ∷
   rw⁻ 2 q9 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw 1 q4 ∷
   rw⁻ 0 q3 ∷
   rw 1 q16 ∷
   rw 0 q11 ∷
   rw 1 q3 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q9 ∷
   rw 3 q12 ∷
   rw 4 q9 ∷
   re 2 3 (CS03 ∷ []) ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q9 ∷
   rw 4 q12 ∷
   rw 5 q9 ∷
   re 3 3 (CS03 ∷ []) ∷
   re 5 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 4 q9 ∷
   rw 5 q13 ∷
   rw 6 q9 ∷
   re 4 3 (CK30 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q9 ∷
   rw 6 q12 ∷
   rw 7 q9 ∷
   re 5 3 (CS03 ∷ []) ∷
   re 7 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 6 q9 ∷
   rw 7 q13 ∷
   rw 8 q9 ∷
   re 6 3 (CK30 ∷ []) ∷
   re 8 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 7 q9 ∷
   rw 8 q13 ∷
   rw 9 q9 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 8 q7 ∷
   rw 9 q13 ∷
   rw 10 q8 ∷
   rw 11 q13 ∷
   rw 12 q8 ∷
   rw 13 q12 ∷
   rw 14 q12 ∷
   rw 15 q12 ∷
   rw 16 q13 ∷
   rw 17 q8 ∷
   rw 18 q12 ∷
   rw 19 q12 ∷
   rw 20 q12 ∷
   rw 21 q12 ∷
   rw 22 q12 ∷
   rw 23 q12 ∷
   rw 24 q7 ∷
   rw 25 q12 ∷
   rw 26 q12 ∷
   rw 27 q13 ∷
   rw 28 q12 ∷
   rw 29 q13 ∷
   rw 30 q13 ∷
   rw 31 q11 ∷
   rw 32 q3 ∷
   rw 33 q3 ∷
   rw 34 q14 ∷
   rw 33 q17 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q19 : Eqn
  q19 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q20 : Eqn
  q20 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q21 : Eqn
  q21 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q22 : Eqn
  q22 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q23 : Eqn
  q23 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q24 : Eqn
  q24 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q25 : Eqn
  q25 = eqn (X0 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X0 ∷ X2 ∷ []) (X2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ X2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1634 W)
  q26 : Eqn
  q26 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q27 : Eqn
  q27 = eqn (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ X3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CK30⁻ ∷ X3 ∷ []) (X3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ X3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CK30⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) (lem-Bar⟨SSSKSS32-⟶0⟩-passes-factors-of-X0-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X0-X3)
  q28 : Eqn
  q28 = eqn (X2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X2 ∷ X2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CK20⁻ ∷ X2 ∷ []) (X0 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X0 ∷ X2 ∷ []) (wn 1635 W)

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X0 X3 CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10 X0 X3]: 207 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X0-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X0-X3 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X0-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X0-X3 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ [])
  (rw 64 q18 ∷
   rw 63 q19 ∷
   rw 62 q20 ∷
   rw 61 q21 ∷
   rw 60 q21 ∷
   rw 59 q22 ∷
   rw 58 q21 ∷
   rw 57 q22 ∷
   rw 56 q22 ∷
   re 55 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 57 q23 ∷
   rw 54 q22 ∷
   rw 53 q22 ∷
   rw 52 q22 ∷
   rw 51 q22 ∷
   rw 50 q22 ∷
   rw 49 q22 ∷
   rw 48 q24 ∷
   rw 47 q21 ∷
   rw 46 q22 ∷
   rw 45 q22 ∷
   rw 44 q22 ∷
   rw 43 q24 ∷
   rw 42 q21 ∷
   rw 41 q24 ∷
   rw 40 q21 ∷
   re 39 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 41 q23 ∷
   re 38 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 40 q23 ∷
   re 37 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 39 q23 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q23 ∷
   re 35 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 37 q23 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q23 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q23 ∷
   rw 32 q19 ∷
   rw 31 q20 ∷
   rw 32 q25 ∷
   rw 31 q26 ∷
   rw 34 q18 ∷
   re 32 3 (CK30 ∷ []) ∷
   rw 35 q18 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 36 q18 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 37 q18 ∷
   re 35 3 (CK30⁻ ∷ []) ∷
   rw 36 q26 ∷
   rw 37 q26 ∷
   rw 40 q18 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 41 q18 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 42 q18 ∷
   re 40 3 (CK30 ∷ []) ∷
   rw 43 q18 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 44 q18 ∷
   re 42 3 (CK30 ∷ []) ∷
   rw 45 q18 ∷
   re 43 3 (CK30 ∷ []) ∷
   rw 46 q18 ∷
   re 44 3 (CX31 ∷ []) ∷
   rw⁻ 45 q21 ∷
   rw⁻ 46 q24 ∷
   rw⁻ 47 q21 ∷
   rw⁻ 48 q24 ∷
   rw⁻ 49 q22 ∷
   rw⁻ 50 q22 ∷
   rw⁻ 51 q22 ∷
   rw⁻ 52 q21 ∷
   rw⁻ 53 q24 ∷
   rw⁻ 54 q22 ∷
   rw⁻ 55 q22 ∷
   rw⁻ 56 q22 ∷
   rw⁻ 57 q22 ∷
   rw⁻ 58 q22 ∷
   rw⁻ 59 q22 ∷
   rw 62 q18 ∷
   re 60 3 (CX31 ∷ []) ∷
   rw⁻ 61 q22 ∷
   rw⁻ 62 q22 ∷
   rw⁻ 63 q21 ∷
   rw⁻ 64 q22 ∷
   rw⁻ 65 q21 ∷
   rw⁻ 66 q21 ∷
   rw 67 q26 ∷
   rw 68 q26 ∷
   rw 71 q18 ∷
   re 69 3 (CK30 ∷ []) ∷
   rw 72 q18 ∷
   re 70 3 (CS03 ∷ []) ∷
   rw 73 q18 ∷
   re 71 3 (CS03 ∷ []) ∷
   rw 74 q18 ∷
   re 72 3 (CK30⁻ ∷ []) ∷
   rw 73 q26 ∷
   rw 74 q23 ∷
   rw 0 q27 ∷
   rw 43 q18 ∷
   rw 42 q19 ∷
   re 41 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 43 q23 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q23 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q23 ∷
   re 38 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 40 q23 ∷
   rw 37 q19 ∷
   rw 36 q19 ∷
   rw 35 q21 ∷
   rw 34 q21 ∷
   rw 33 q22 ∷
   rw 32 q21 ∷
   rw 31 q22 ∷
   rw 30 q22 ∷
   re 29 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 31 q23 ∷
   rw 28 q22 ∷
   rw 27 q22 ∷
   rw 26 q22 ∷
   rw 25 q22 ∷
   rw 24 q22 ∷
   rw 23 q22 ∷
   rw 22 q24 ∷
   rw 21 q21 ∷
   rw 20 q22 ∷
   rw 19 q22 ∷
   rw 18 q22 ∷
   rw 17 q24 ∷
   rw 16 q21 ∷
   rw 15 q24 ∷
   rw 14 q21 ∷
   re 13 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 15 q23 ∷
   re 12 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 14 q23 ∷
   re 11 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 13 q23 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q23 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 11 q23 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q23 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q23 ∷
   rw 6 q19 ∷
   rw 5 q19 ∷
   re 4 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q23 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q23 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q23 ∷
   re 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 3 q23 ∷
   rw 0 q19 ∷
   rw 1 q28 ∷
   rw⁻ 0 q20 ∷
   rw 1 q26 ∷
   rw 4 q18 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 5 q18 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 6 q18 ∷
   re 4 3 (CK30 ∷ []) ∷
   rw 7 q18 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 8 q18 ∷
   re 6 3 (CK30 ∷ []) ∷
   rw 9 q18 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 10 q18 ∷
   re 8 3 (CX31 ∷ []) ∷
   rw⁻ 9 q21 ∷
   rw⁻ 10 q24 ∷
   rw⁻ 11 q21 ∷
   rw⁻ 12 q24 ∷
   rw⁻ 13 q22 ∷
   rw⁻ 14 q22 ∷
   rw⁻ 15 q22 ∷
   rw⁻ 16 q21 ∷
   rw⁻ 17 q24 ∷
   rw⁻ 18 q22 ∷
   rw⁻ 19 q22 ∷
   rw⁻ 20 q22 ∷
   rw⁻ 21 q22 ∷
   rw⁻ 22 q22 ∷
   rw⁻ 23 q22 ∷
   rw 26 q18 ∷
   re 24 3 (CX31 ∷ []) ∷
   rw⁻ 25 q22 ∷
   rw⁻ 26 q22 ∷
   rw⁻ 27 q21 ∷
   rw⁻ 28 q22 ∷
   rw⁻ 29 q21 ∷
   rw⁻ 30 q21 ∷
   rw⁻ 31 q20 ∷
   rw 32 q26 ∷
   rw 33 q23 ∷ []) Eq.refl
