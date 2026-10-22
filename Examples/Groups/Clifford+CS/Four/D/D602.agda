{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD602 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D602 (W : Ws) (Sᴰ : SD602) where

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
  lem-pass-CK30-CS03-CS03-CKd30-vs-X3-TOFF213-X3 : St 1295
  lem-pass-CK30-CS03-CS03-CKd30-vs-X3-TOFF213-X3 = pickᴰ 0 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF213-X3 : St 1299
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF213-X3 = pickᴰ 1 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = wE 1106 W
  q3 : Eqn
  q3 = wE 7 W
  q4 : Eqn
  q4 = wE 140 W
  q5 : Eqn
  q5 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q6 : Eqn
  q6 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = wE 1792 W
  q9 : Eqn
  q9 = wE 142 W
  q10 : Eqn
  q10 = wE 27 W
  q11 : Eqn
  q11 = wE 139 W
  q12 : Eqn
  q12 = wE 31 W
  q13 : Eqn
  q13 = sE 1295 lem-pass-CK30-CS03-CS03-CKd30-vs-X3-TOFF213-X3
  q14 : Eqn
  q14 = sE 1299 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF213-X3
  q15 : Eqn
  q15 = wE 137 W
  q16 : Eqn
  q16 = wE 1793 W
  q17 : Eqn
  q17 = wE 317 W

-- pass [X0 CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02 X0] [X3 TOFF213 X3]: 313 steps
lem-pass-X0-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-X0-vs-X3-TOFF213-X3 : ⟪ (X0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X0 ∷ X3 ∷ Toff213 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff213 ∷ X3 ∷ X0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X0 ∷ []) ⟫ʷ
lem-pass-X0-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-X0-vs-X3-TOFF213-X3 = derive (X0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X0 ∷ X3 ∷ Toff213 ∷ X3 ∷ []) (X3 ∷ Toff213 ∷ X3 ∷ X0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X0 ∷ [])
  (rw 33 q1 ∷
   rw 32 q2 ∷
   rw 31 q3 ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   rw 28 q3 ∷
   rw 27 q3 ∷
   rw 26 q3 ∷
   rw⁻ 25 q5 ∷
   rw 24 q3 ∷
   rw 23 q3 ∷
   rw 22 q3 ∷
   rw 21 q3 ∷
   rw 20 q3 ∷
   rw 19 q3 ∷
   rw 18 q3 ∷
   rw 17 q3 ∷
   rw 16 q3 ∷
   rw⁻ 15 q6 ∷
   rw 14 q4 ∷
   rw 13 q3 ∷
   rw 12 q3 ∷
   rw 11 q3 ∷
   rw 10 q3 ∷
   rw 9 q3 ∷
   rw 8 q3 ∷
   rw⁻ 7 q5 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q7 ∷
   rw 7 q3 ∷
   rw⁻ 6 q7 ∷
   re 7 3 (CS13 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q7 ∷
   rw 6 q3 ∷
   rw⁻ 5 q7 ∷
   re 6 3 (CS13 ∷ []) ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q7 ∷
   rw 5 q4 ∷
   rw⁻ 4 q7 ∷
   re 5 3 (CK31 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q7 ∷
   rw 4 q3 ∷
   rw⁻ 3 q7 ∷
   re 4 3 (CS13 ∷ []) ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q7 ∷
   rw 3 q3 ∷
   rw⁻ 2 q7 ∷
   re 3 3 (CS13 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q7 ∷
   rw 2 q3 ∷
   rw⁻ 1 q7 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 0 q2 ∷
   rw 1 q8 ∷
   re 1 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 0 q7 ∷
   rw 1 q9 ∷
   rw 2 q7 ∷
   re 0 3 (CK30 ∷ []) ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q7 ∷
   rw 2 q10 ∷
   rw 3 q7 ∷
   re 1 3 (CS03 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q7 ∷
   rw 3 q10 ∷
   rw 4 q7 ∷
   re 2 3 (CS03 ∷ []) ∷
   re 4 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   rw 4 q11 ∷
   rw 5 q7 ∷
   re 3 3 (CK30⁻ ∷ []) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw 5 q10 ∷
   rw 6 q7 ∷
   re 4 3 (CS03 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw 6 q10 ∷
   rw 7 q7 ∷
   re 5 3 (CS03 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 7 q10 ∷
   rw 8 q7 ∷
   re 6 3 (CS03 ∷ []) ∷
   re 8 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw 8 q9 ∷
   rw 9 q7 ∷
   re 7 3 (CK30 ∷ []) ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   rw 9 q10 ∷
   rw 10 q7 ∷
   re 8 3 (CS03 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q7 ∷
   rw 10 q10 ∷
   rw 11 q7 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q5 ∷
   rw 11 q10 ∷
   rw 12 q10 ∷
   rw 13 q10 ∷
   rw 14 q10 ∷
   rw 15 q10 ∷
   rw 16 q10 ∷
   rw 17 q9 ∷
   rw 18 q6 ∷
   rw 19 q10 ∷
   rw 20 q10 ∷
   rw 21 q10 ∷
   rw 22 q10 ∷
   rw 23 q10 ∷
   rw 24 q10 ∷
   rw 25 q10 ∷
   rw 26 q10 ∷
   rw 27 q10 ∷
   rw 28 q5 ∷
   rw 29 q10 ∷
   rw 30 q10 ∷
   rw 31 q10 ∷
   rw 32 q9 ∷
   rw 33 q10 ∷
   rw 34 q10 ∷
   re 36 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 35 q7 ∷
   rw 36 q9 ∷
   rw 37 q7 ∷
   re 35 3 (CK30 ∷ []) ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q7 ∷
   rw 37 q10 ∷
   rw 38 q7 ∷
   re 36 3 (CS03 ∷ []) ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q7 ∷
   rw 38 q10 ∷
   rw 39 q7 ∷
   re 37 3 (CS03 ∷ []) ∷
   re 39 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 38 q7 ∷
   rw 39 q11 ∷
   rw 40 q7 ∷
   re 38 3 (CK30⁻ ∷ []) ∷
   rw 39 q12 ∷
   rw 35 q13 ∷
   rw 4 q14 ∷
   rw 0 q13 ∷
   rw 42 q1 ∷
   re 41 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q7 ∷
   rw 42 q15 ∷
   rw⁻ 41 q7 ∷
   re 42 3 (CK31⁻ ∷ []) ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q7 ∷
   rw 41 q3 ∷
   rw⁻ 40 q7 ∷
   re 41 3 (CS13 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q7 ∷
   rw 40 q3 ∷
   rw⁻ 39 q7 ∷
   re 40 3 (CS13 ∷ []) ∷
   re 38 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q7 ∷
   rw 39 q4 ∷
   rw⁻ 38 q7 ∷
   re 39 3 (CK31 ∷ []) ∷
   rw 37 q3 ∷
   rw 36 q3 ∷
   rw 35 q4 ∷
   rw 34 q3 ∷
   rw 33 q3 ∷
   rw 32 q3 ∷
   rw⁻ 31 q5 ∷
   rw 30 q3 ∷
   rw 29 q3 ∷
   rw 28 q3 ∷
   rw 27 q3 ∷
   rw 26 q3 ∷
   rw 25 q3 ∷
   rw 24 q3 ∷
   rw 23 q3 ∷
   rw 22 q3 ∷
   rw⁻ 21 q6 ∷
   rw 20 q4 ∷
   rw 19 q3 ∷
   rw 18 q3 ∷
   rw 17 q3 ∷
   rw 16 q3 ∷
   rw 15 q3 ∷
   rw 14 q3 ∷
   rw⁻ 13 q5 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q7 ∷
   rw 13 q3 ∷
   rw⁻ 12 q7 ∷
   re 13 3 (CS13 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q7 ∷
   rw 12 q3 ∷
   rw⁻ 11 q7 ∷
   re 12 3 (CS13 ∷ []) ∷
   re 10 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q7 ∷
   rw 11 q4 ∷
   rw⁻ 10 q7 ∷
   re 11 3 (CK31 ∷ []) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q7 ∷
   rw 10 q3 ∷
   rw⁻ 9 q7 ∷
   re 10 3 (CS13 ∷ []) ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q7 ∷
   rw 9 q3 ∷
   rw⁻ 8 q7 ∷
   re 9 3 (CS13 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q7 ∷
   rw 8 q3 ∷
   rw⁻ 7 q7 ∷
   re 8 3 (CS13 ∷ []) ∷
   re 6 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q7 ∷
   rw 7 q15 ∷
   rw⁻ 6 q7 ∷
   re 7 3 (CK31⁻ ∷ []) ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q7 ∷
   rw 6 q3 ∷
   rw⁻ 5 q7 ∷
   re 6 3 (CS13 ∷ []) ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q7 ∷
   rw 5 q3 ∷
   rw⁻ 4 q7 ∷
   re 5 3 (CS13 ∷ []) ∷
   re 3 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q7 ∷
   rw 4 q4 ∷
   rw⁻ 3 q7 ∷
   re 4 3 (CK31 ∷ []) ∷
   rw 4 q16 ∷
   rw 3 q17 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw 5 q10 ∷
   rw 6 q7 ∷
   re 4 3 (CS03 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw 6 q10 ∷
   rw 7 q7 ∷
   re 5 3 (CS03 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 7 q10 ∷
   rw 8 q7 ∷
   re 6 3 (CS03 ∷ []) ∷
   re 8 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw 8 q9 ∷
   rw 9 q7 ∷
   re 7 3 (CK30 ∷ []) ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   rw 9 q10 ∷
   rw 10 q7 ∷
   re 8 3 (CS03 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q7 ∷
   rw 10 q10 ∷
   rw 11 q7 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q5 ∷
   rw 11 q10 ∷
   rw 12 q10 ∷
   rw 13 q10 ∷
   rw 14 q10 ∷
   rw 15 q10 ∷
   rw 16 q10 ∷
   rw 17 q9 ∷
   rw 18 q6 ∷
   rw 19 q10 ∷
   rw 20 q10 ∷
   rw 21 q10 ∷
   rw 22 q10 ∷
   rw 23 q10 ∷
   rw 24 q10 ∷
   rw 25 q10 ∷
   rw 26 q10 ∷
   rw 27 q10 ∷
   rw 28 q5 ∷
   rw 29 q10 ∷
   rw 30 q10 ∷
   rw 31 q10 ∷
   rw 32 q9 ∷
   rw 33 q10 ∷
   rw 34 q10 ∷
   rw 35 q17 ∷
   rw 36 q12 ∷ []) Eq.refl
