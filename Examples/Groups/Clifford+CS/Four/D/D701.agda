{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D701 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D010 W using (lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D510 W using (lem-pass-X3-CK30-X3-vs-TOFF103-CS12-TOFF103-CSd12 ; lem-pass-X3-CKd30-X3-vs-TOFF103-CS12-TOFF103-CSd12 ; lem-pass-X3-CS30-X3-vs-TOFF103-CS12-TOFF103-CSd12 ; lem-pass-X3-CSd30-X3-vs-TOFF103-CS12-TOFF103-CSd12)
open import Examples.Groups.Clifford+CS.Four.D.D513 W using (lem-pass-X3-CK31-X3-vs-CS02-TOFF013-CSd02-TOFF013 ; lem-pass-X3-CKd31-X3-vs-CS02-TOFF013-CSd02-TOFF013 ; lem-pass-X3-CS31-X3-vs-CS02-TOFF013-CSd02-TOFF013 ; lem-pass-X3-CS31-X3-vs-TOFF103-CS12-TOFF103-CSd12 ; lem-pass-X3-CSd31-X3-vs-CS02-TOFF013-CSd02-TOFF013)
open import Examples.Groups.Clifford+CS.Four.D.D538 W using (lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS12 ; lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CSd12)
open import Examples.Groups.Clifford+CS.Four.D.D596 W using (lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-S0 ; lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-Sd0)
open import Examples.Groups.Clifford+CS.Four.D.D651 W using (lem-S2 ; lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-X1-X3-TOFF013-X1-X3 ; lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-X3-TOFF013-X3)
open import Examples.Groups.Clifford+CS.Four.D.D677 W using (lem-C3-PP3 ; lem-S2-at0213 ; lem-S2-at1023)
open import Examples.Groups.Clifford+CS.Four.D.D681 W using (lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS03 ; lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CSd03 ; lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-TOFF012-X1-X2 ; lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X2-TOFF012-X2 ; lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF103-X3 ; lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-TOFF012-CS03-TOFF012-CSd03 ; lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03 ; lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF013-CS02-TOFF013-CSd02)
open import Examples.Groups.Clifford+CS.Four.D.D682 W using (lem-pass-X2-CK20-X2-vs-TOFF012-CS03-TOFF012-CSd03 ; lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF013-CS02-TOFF013-CSd02 ; lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D683 W using (lem-S2-ᵖ-1)

private
  q1 : Eqn
  q1 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q2 : Eqn
  q2 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q3 : Eqn
  q3 = eqn (CS02 ∷ []) (CS02⁻ ∷ CS02 ∷ CS02 ∷ []) (wn 2040 W)
  q4 : Eqn
  q4 = eqn (CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03 ∷ []) lem-C3-PP3
  q5 : Eqn
  q5 = eqn (CS02⁻ ∷ CS02 ∷ []) [] (wn 1358 W)

-- R0: 19 steps
lem-R0 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) ⟫ʷ
lem-R0 = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03 ∷ []) (CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q2 ∷
   rw 4 q3 ∷
   rw 5 q1 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q2 ∷
   rw⁻ 0 q4 ∷
   rw 6 q1 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   re 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q2 ∷
   rw 5 q5 ∷
   rw 4 q2 ∷ []) Eq.refl

private
  q6 : Eqn
  q6 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (lem-S2)
  q7 : Eqn
  q7 = eqn (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF013-CS02-TOFF013-CSd02)
  q8 : Eqn
  q8 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) lem-S2

-- pass [X3 TOFF012 CS03 TOFF012 CSd03 X3] [TOFF012 CS03 TOFF012 CSd03]: 3 steps
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 6 q6 ∷
   rw 0 q7 ∷
   rw⁻ 0 q8 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X2-TOFF012-X2)
  q10 : Eqn
  q10 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ []) (S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-S0)
  q11 : Eqn
  q11 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CSd03)
  q12 : Eqn
  q12 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-Sd0)
  q13 : Eqn
  q13 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03 ∷ []) (CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS03)

-- pass [TOFF012 CS03 TOFF012 CSd03] [X2 TOFF012 X2 S0 CSd03 X2 TOFF012 X2 Sd0 CS03]: 6 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03 = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw 0 q9 ∷
   rw 3 q10 ∷
   rw 4 q11 ∷
   rw 5 q9 ∷
   rw 8 q12 ∷
   rw 9 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-TOFF012-X1-X2)

-- pass [TOFF012 CS03 TOFF012 CSd03] [X1 X2 TOFF012 X1 X2 S0 CSd03 X1 X2 TOFF012 X1 X2 Sd0 CS03]: 6 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-TOFF012-X1-X2-S0-CSd03-X1-X2-TOFF012-X1-X2-Sd0-CS03 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-TOFF012-X1-X2-S0-CSd03-X1-X2-TOFF012-X1-X2-Sd0-CS03 = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw 0 q14 ∷
   rw 5 q10 ∷
   rw 6 q11 ∷
   rw 7 q14 ∷
   rw 12 q12 ∷
   rw 13 q13 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (lem-S2-at1023)
  q16 : Eqn
  q16 = eqn (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-X3-TOFF013-X3)
  q17 : Eqn
  q17 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) lem-S2-at1023

-- pass [TOFF102 CS13 TOFF102 CSd13] [X3 TOFF013 X3]: 3 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF013-X3 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF013-X3 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw 0 q15 ∷
   rw 0 q16 ∷
   rw⁻ 3 q17 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = eqn (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [TOFF012 CS03 TOFF012 CSd03] [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3]: 1 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw⁻ 0 q18 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = eqn (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-X1-X3-TOFF013-X1-X3)

-- pass [TOFF102 CS13 TOFF102 CSd13] [X1 X3 TOFF013 X1 X3]: 3 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw 0 q15 ∷
   rw 0 q19 ∷
   rw⁻ 5 q17 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CSd03

-- pass [CSd03] [TOFF012 CS03 TOFF012 CSd03]: 1 steps
lem-pass-CSd03-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-TOFF012-CS03-TOFF012-CSd03 = derive (CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03⁻ ∷ [])
  (rw⁻ 0 q20 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03 ∷ []) (CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS03

-- pass [CS03] [TOFF012 CS03 TOFF012 CSd03]: 1 steps
lem-pass-CS03-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-TOFF012-CS03-TOFF012-CSd03 = derive (CS03 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03 ∷ [])
  (rw⁻ 0 q21 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q23 : Eqn
  q23 = eqn [] (Toff123 ∷ Toff123 ∷ []) (wn 2041 W)
  q24 : Eqn
  q24 = eqn (Sw01 ∷ K1 ∷ []) (K0 ∷ Sw01 ∷ []) (wn 121 W)
  q25 : Eqn
  q25 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q26 : Eqn
  q26 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q27 : Eqn
  q27 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q28 : Eqn
  q28 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q29 : Eqn
  q29 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q30 : Eqn
  q30 = eqn (Sw01 ∷ ι1 ∷ []) (ι ∷ Sw01 ∷ []) (wn 122 W)
  q31 : Eqn
  q31 = eqn (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) (wn 123 W)
  q32 : Eqn
  q32 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q33 : Eqn
  q33 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q34 : Eqn
  q34 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)
  q35 : Eqn
  q35 = eqn (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wn 125 W)
  q36 : Eqn
  q36 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q37 : Eqn
  q37 = eqn [] (CS01 ∷ CS01⁻ ∷ []) (wn 2042 W)
  q38 : Eqn
  q38 = eqn [] (CS01⁻ ∷ CS01 ∷ []) (wn 1694 W)
  q39 : Eqn
  q39 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff023 ∷ CS01 ∷ Toff023 ∷ CS01⁻ ∷ []) lem-S2-at0213
  q40 : Eqn
  q40 = eqn (Toff012 ∷ Toff012 ∷ []) [] (wn 227 W)
  q41 : Eqn
  q41 = eqn (CS02 ∷ CS02⁻ ∷ []) [] (wn 1342 W)

-- S2 @0213 ^-1: 141 steps
lem-S2-at0213-ᵖ-1 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ []) ⟫ʷ
lem-S2-at0213-ᵖ-1 = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS01 ∷ Toff023 ∷ CS01⁻ ∷ Toff023 ∷ [])
  (rw 4 q22 ∷
   rw 5 q23 ∷
   re 5 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 4 q24 ∷
   rw 5 q25 ∷
   rw 6 q26 ∷
   rw 7 q27 ∷
   rw 8 q26 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q28 ∷
   rw 10 q29 ∷
   rw 11 q28 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q24 ∷
   rw 11 q30 ∷
   rw 4 q22 ∷
   rw 5 q31 ∷
   rw 6 q25 ∷
   rw 7 q32 ∷
   rw 8 q27 ∷
   rw 9 q32 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q28 ∷
   rw 11 q33 ∷
   rw 12 q28 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 11 q31 ∷
   rw 12 q34 ∷
   rw 5 q35 ∷
   re 5 8 (Toff123 ∷ []) ∷
   re 4 3 (Toff023 ∷ []) ∷
   re 6 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 5 q24 ∷
   rw 6 q25 ∷
   rw 7 q26 ∷
   rw 8 q27 ∷
   rw 9 q26 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q28 ∷
   rw 11 q29 ∷
   rw 12 q28 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q24 ∷
   rw 12 q30 ∷
   rw 5 q22 ∷
   rw 6 q31 ∷
   rw 7 q25 ∷
   rw 8 q32 ∷
   rw 9 q27 ∷
   rw 10 q32 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q28 ∷
   rw 12 q33 ∷
   rw 13 q28 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 12 q31 ∷
   rw 13 q34 ∷
   rw 6 q35 ∷
   re 6 8 (Toff123 ∷ []) ∷
   re 5 3 (Toff023 ∷ []) ∷
   rw 6 q36 ∷
   rw 5 q37 ∷
   rw 6 q22 ∷
   rw 7 q23 ∷
   re 7 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 6 q24 ∷
   rw 7 q25 ∷
   rw 8 q26 ∷
   rw 9 q27 ∷
   rw 10 q26 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q28 ∷
   rw 12 q29 ∷
   rw 13 q28 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q24 ∷
   rw 13 q30 ∷
   rw 6 q22 ∷
   rw 7 q31 ∷
   rw 8 q25 ∷
   rw 9 q32 ∷
   rw 10 q27 ∷
   rw 11 q32 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q28 ∷
   rw 13 q33 ∷
   rw 14 q28 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 13 q31 ∷
   rw 14 q34 ∷
   rw 7 q35 ∷
   re 7 8 (Toff123 ∷ []) ∷
   re 6 3 (Toff023 ∷ []) ∷
   re 8 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 7 q24 ∷
   rw 8 q25 ∷
   rw 9 q26 ∷
   rw 10 q27 ∷
   rw 11 q26 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q28 ∷
   rw 13 q29 ∷
   rw 14 q28 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q24 ∷
   rw 14 q30 ∷
   rw 7 q22 ∷
   rw 8 q31 ∷
   rw 9 q25 ∷
   rw 10 q32 ∷
   rw 11 q27 ∷
   rw 12 q32 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q28 ∷
   rw 14 q33 ∷
   rw 15 q28 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 14 q31 ∷
   rw 15 q34 ∷
   rw 8 q35 ∷
   re 8 8 (Toff123 ∷ []) ∷
   re 7 3 (Toff023 ∷ []) ∷
   rw 8 q36 ∷
   rw 7 q38 ∷
   rw⁻ 4 q39 ∷
   rw 3 q40 ∷
   rw 4 q1 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q2 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q2 ∷
   rw 3 q5 ∷
   rw 2 q2 ∷
   rw 1 q40 ∷
   rw 2 q1 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q2 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q2 ∷
   rw 1 q41 ∷
   rw 0 q2 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q43 : Eqn
  q43 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q44 : Eqn
  q44 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ K0 ∷ []) (K0 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 2043 W)
  q45 : Eqn
  q45 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q46 : Eqn
  q46 = eqn (X3 ∷ CS03 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
  q47 : Eqn
  q47 = eqn (X3 ∷ CK30 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03)
  q48 : Eqn
  q48 = eqn (K0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑)))
  q49 : Eqn
  q49 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ K0⁻ ∷ []) (K0⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 2044 W)

-- pass [X3 CSd30 X3] [K0 TOFF012 CS03 TOFF012 CSd03 Kd0]: 45 steps
lem-pass-X3-CSd30-X3-vs-K0-TOFF012-CS03-TOFF012-CSd03-Kd0 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-K0-TOFF012-CS03-TOFF012-CSd03-Kd0 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ []) (K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 4 q1 ∷
   rw 3 q42 ∷
   rw 2 q43 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q2 ∷
   rw 0 q43 ∷
   rw 1 q44 ∷
   rw⁻ 0 q42 ∷
   rw 1 q45 ∷
   rw 4 q1 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q45 ∷
   rw 4 q45 ∷
   rw 7 q1 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 6 q45 ∷
   rw 7 q45 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q45 ∷
   rw 10 q2 ∷
   rw 7 q46 ∷
   rw 4 q47 ∷
   rw 1 q46 ∷
   rw 15 q1 ∷
   rw 14 q48 ∷
   rw 13 q43 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q2 ∷
   rw 11 q43 ∷
   rw 10 q43 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 11 q2 ∷
   rw 8 q43 ∷
   rw 7 q43 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   rw 5 q43 ∷
   rw 6 q49 ∷
   rw⁻ 5 q48 ∷
   rw 6 q45 ∷
   rw 9 q1 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw 8 q45 ∷
   rw 9 q2 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q51 : Eqn
  q51 = eqn (X2 ∷ CK20 ∷ X2 ∷ S0 ∷ K0 ∷ []) (S0 ∷ K0 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 2045 W)
  q52 : Eqn
  q52 = eqn (S0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑)))
  q53 : Eqn
  q53 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ K0⁻ ∷ S0⁻ ∷ []) (K0⁻ ∷ S0⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 2046 W)

-- pass [X3 CK30 X3] [S0 K0 TOFF012 CS03 TOFF012 CSd03 Kd0 Sd0]: 67 steps
lem-pass-X3-CK30-X3-vs-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0 = derive (X3 ∷ CK30 ∷ X3 ∷ S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (S0 ∷ K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  (rw 5 q1 ∷
   rw 4 q42 ∷
   rw 3 q50 ∷
   rw 2 q43 ∷
   re 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 3 q2 ∷
   rw 0 q43 ∷
   rw 1 q51 ∷
   rw⁻ 0 q50 ∷
   rw⁻ 1 q42 ∷
   rw 2 q45 ∷
   rw 5 q1 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q45 ∷
   rw 5 q45 ∷
   rw 8 q1 ∷
   re 6 3 (CK30 ∷ []) ∷
   rw 7 q45 ∷
   rw 8 q45 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q45 ∷
   rw 11 q45 ∷
   rw 14 q1 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q45 ∷
   rw 14 q45 ∷
   rw 17 q1 ∷
   re 15 3 (CK30 ∷ []) ∷
   rw 16 q45 ∷
   rw 17 q2 ∷
   rw 14 q47 ∷
   rw 11 q46 ∷
   rw 8 q46 ∷
   rw 5 q47 ∷
   rw 2 q46 ∷
   rw 23 q1 ∷
   rw 22 q52 ∷
   rw 21 q48 ∷
   rw 20 q43 ∷
   re 19 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 21 q2 ∷
   rw 18 q43 ∷
   rw 17 q43 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q2 ∷
   rw 15 q43 ∷
   rw 14 q43 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q2 ∷
   rw 12 q43 ∷
   rw 11 q43 ∷
   re 10 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 12 q2 ∷
   rw 9 q43 ∷
   rw 8 q43 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q2 ∷
   rw 6 q43 ∷
   rw 7 q53 ∷
   rw⁻ 6 q48 ∷
   rw⁻ 7 q52 ∷
   rw 8 q45 ∷
   rw 11 q1 ∷
   re 9 3 (CK30 ∷ []) ∷
   rw 10 q45 ∷
   rw 11 q2 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ []) (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 2047 W)
  q55 : Eqn
  q55 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ S0 ∷ K0 ∷ S0 ∷ []) (S0 ∷ K0 ∷ S0 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 2048 W)

-- pass [X3 CSd30 X3] [Sd0 Kd0 Sd0 TOFF012 CS03 TOFF012 CSd03 S0 K0 S0]: 53 steps
lem-pass-X3-CSd30-X3-vs-Sd0-Kd0-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-K0-S0 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-Sd0-Kd0-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-K0-S0 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ K0 ∷ S0 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 6 q1 ∷
   rw 5 q52 ∷
   rw 4 q48 ∷
   rw 3 q52 ∷
   rw 2 q43 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q2 ∷
   rw 0 q43 ∷
   rw 1 q54 ∷
   rw⁻ 0 q52 ∷
   rw⁻ 1 q48 ∷
   rw⁻ 2 q52 ∷
   rw 3 q45 ∷
   rw 6 q1 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q45 ∷
   rw 6 q45 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q45 ∷
   rw 9 q45 ∷
   rw 12 q1 ∷
   re 10 3 (CK30 ∷ []) ∷
   rw 11 q45 ∷
   rw 12 q2 ∷
   rw 9 q47 ∷
   rw 6 q46 ∷
   rw 3 q46 ∷
   rw 19 q1 ∷
   rw 18 q50 ∷
   rw 17 q42 ∷
   rw 16 q50 ∷
   rw 15 q43 ∷
   re 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 16 q2 ∷
   rw 13 q43 ∷
   rw 12 q43 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q2 ∷
   rw 10 q43 ∷
   rw 9 q43 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   rw 7 q43 ∷
   rw 8 q55 ∷
   rw⁻ 7 q50 ∷
   rw⁻ 8 q42 ∷
   rw⁻ 9 q50 ∷
   rw 10 q45 ∷
   rw 13 q1 ∷
   re 11 3 (CS03⁻ ∷ []) ∷
   rw 12 q45 ∷
   rw 13 q2 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = eqn [] (CS02 ∷ CS02⁻ ∷ []) (wn 1357 W)
  q57 : Eqn
  q57 = eqn [] (Toff012 ∷ Toff012 ∷ []) (wn 45 W)
  q58 : Eqn
  q58 = eqn [] (CS02⁻ ∷ CS02 ∷ []) (wn 231 W)
  q59 : Eqn
  q59 = eqn (X3 ∷ CS03 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [X3 CS30 X3] [CS03 TOFF012 CSd03 TOFF012]: 33 steps
lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X3 ∷ CS03 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  (rw 0 q1 ∷
   rw 1 q56 ∷
   rw 2 q1 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q2 ∷
   rw 1 q57 ∷
   rw 2 q1 ∷
   rw 3 q58 ∷
   rw 4 q1 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 5 q1 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q2 ∷
   rw 3 q57 ∷
   rw⁻ 4 q59 ∷
   rw 12 q1 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q2 ∷
   re 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q2 ∷
   rw 11 q5 ∷
   rw 10 q2 ∷
   rw 9 q40 ∷
   rw 10 q1 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q2 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   rw 9 q41 ∷
   rw 8 q2 ∷
   rw 7 q40 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = eqn (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [CS03 TOFF012 CSd03 TOFF012] [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  (rw⁻ 0 q60 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-TOFF103-CS12-TOFF103-CSd12)

-- pass [X3 CSd30 X3] [TOFF102 CS13 TOFF102 CSd13]: 3 steps
lem-pass-X3-CSd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 3 q15 ∷
   rw 0 q61 ∷
   rw⁻ 0 q17 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = eqn (X3 ∷ CK30⁻ ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd30-X3-vs-TOFF103-CS12-TOFF103-CSd12)

-- pass [X3 CKd30 X3] [TOFF102 CS13 TOFF102 CSd13]: 3 steps
lem-pass-X3-CKd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (X3 ∷ CK30⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  (rw 3 q15 ∷
   rw 0 q62 ∷
   rw⁻ 0 q17 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = eqn (X3 ∷ CK30 ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) (lem-pass-X3-CK30-X3-vs-TOFF103-CS12-TOFF103-CSd12)

-- pass [X3 CK30 X3] [TOFF102 CS13 TOFF102 CSd13]: 3 steps
lem-pass-X3-CK30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (X3 ∷ CK30 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  (rw 3 q15 ∷
   rw 0 q63 ∷
   rw⁻ 0 q17 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = eqn (X3 ∷ CS03 ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-pass-X3-CS30-X3-vs-TOFF103-CS12-TOFF103-CSd12)

-- pass [X3 CS30 X3] [TOFF102 CS13 TOFF102 CSd13]: 3 steps
lem-pass-X3-CS30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (X3 ∷ CS03 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  (rw 3 q15 ∷
   rw 0 q64 ∷
   rw⁻ 0 q17 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff103 ∷ X3 ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF103-X3)
  q66 : Eqn
  q66 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12 ∷ []) (CS12 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS12)
  q67 : Eqn
  q67 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CSd12)

-- pass [TOFF012 CS03 TOFF012 CSd03] [X3 TOFF103 X3 CS12 X3 TOFF103 X3 CSd12]: 4 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF103-X3-CS12-X3-TOFF103-X3-CSd12 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff103 ∷ X3 ∷ CS12 ∷ X3 ∷ Toff103 ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff103 ∷ X3 ∷ CS12 ∷ X3 ∷ Toff103 ∷ X3 ∷ CS12⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF103-X3-CS12-X3-TOFF103-X3-CSd12 = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ Toff103 ∷ X3 ∷ CS12 ∷ X3 ∷ Toff103 ∷ X3 ∷ CS12⁻ ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ CS12 ∷ X3 ∷ Toff103 ∷ X3 ∷ CS12⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw 0 q65 ∷
   rw 3 q66 ∷
   rw 4 q65 ∷
   rw 7 q67 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = eqn (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF013-CS02-TOFF013-CSd02)

-- pass [X3 CS03 TOFF012 CSd03 TOFF012 X3] [TOFF012 CS03 TOFF012 CSd03]: 3 steps
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ [])
  (rw 6 q6 ∷
   rw 0 q68 ∷
   rw⁻ 0 q8 ∷ []) Eq.refl

private
  q69 : Eqn
  q69 = eqn (X2 ∷ CK20 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) lem-pass-X2-CK20-X2-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [X2 CK20 X2] [CS03 TOFF012 CSd03 TOFF012]: 33 steps
lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X2 ∷ CK20 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20 ∷ X2 ∷ [])
  (rw 0 q1 ∷
   rw 1 q56 ∷
   rw 2 q1 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q2 ∷
   rw 1 q57 ∷
   rw 2 q1 ∷
   rw 3 q58 ∷
   rw 4 q1 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 5 q1 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q2 ∷
   rw 3 q57 ∷
   rw⁻ 4 q69 ∷
   rw 12 q1 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q2 ∷
   re 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q2 ∷
   rw 11 q5 ∷
   rw 10 q2 ∷
   rw 9 q40 ∷
   rw 10 q1 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q2 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   rw 9 q41 ∷
   rw 8 q2 ∷
   rw 7 q40 ∷ []) Eq.refl

-- pass [TOFF012 CS03 TOFF012 CSd03] [S0 CSd03]: 2 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-S0-CSd03 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-S0-CSd03 = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ CS03⁻ ∷ []) (S0 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw 0 q10 ∷
   rw 1 q11 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [X3 CSd30 X3] [CS03 TOFF012 CSd03 TOFF012]: 33 steps
lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 0 q1 ∷
   rw 1 q56 ∷
   rw 2 q1 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q2 ∷
   rw 1 q57 ∷
   rw 2 q1 ∷
   rw 3 q58 ∷
   rw 4 q1 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 5 q1 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q2 ∷
   rw 3 q57 ∷
   rw⁻ 4 q70 ∷
   rw 12 q1 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q2 ∷
   re 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q2 ∷
   rw 11 q5 ∷
   rw 10 q2 ∷
   rw 9 q40 ∷
   rw 10 q1 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q2 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   rw 9 q41 ∷
   rw 8 q2 ∷
   rw 7 q40 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = eqn (X3 ∷ CS13 ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) (lem-pass-X3-CS31-X3-vs-TOFF103-CS12-TOFF103-CSd12)

-- pass [X3 CS31 X3] [TOFF102 CS13 TOFF102 CSd13]: 3 steps
lem-pass-X3-CS31-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS31-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (X3 ∷ CS13 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ [])
  (rw 3 q15 ∷
   rw 0 q71 ∷
   rw⁻ 0 q17 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = eqn (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) (lem-S2-ᵖ-1)
  q73 : Eqn
  q73 = eqn (X3 ∷ CS13 ∷ X3 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (lem-pass-X3-CS31-X3-vs-CS02-TOFF013-CSd02-TOFF013)
  q74 : Eqn
  q74 = eqn (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) lem-S2-ᵖ-1

-- pass [X3 CS31 X3] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X3-CS31-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS31-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X3 ∷ CS13 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS13 ∷ X3 ∷ [])
  (rw 3 q72 ∷
   rw 0 q73 ∷
   rw⁻ 0 q74 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = eqn (X3 ∷ CK31 ∷ X3 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (lem-pass-X3-CK31-X3-vs-CS02-TOFF013-CSd02-TOFF013)

-- pass [X3 CK31 X3] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X3-CK31-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK31-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X3 ∷ CK31 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK31 ∷ X3 ∷ [])
  (rw 3 q72 ∷
   rw 0 q75 ∷
   rw⁻ 0 q74 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = eqn (X3 ∷ CK31⁻ ∷ X3 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd31-X3-vs-CS02-TOFF013-CSd02-TOFF013)

-- pass [X3 CKd31 X3] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X3-CKd31-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd31-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X3 ∷ CK31⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ [])
  (rw 3 q72 ∷
   rw 0 q76 ∷
   rw⁻ 0 q74 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = eqn (X3 ∷ CS13⁻ ∷ X3 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd31-X3-vs-CS02-TOFF013-CSd02-TOFF013)

-- pass [X3 CSd31 X3] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X3-CSd31-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd31-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X3 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ [])
  (rw 3 q72 ∷
   rw 0 q77 ∷
   rw⁻ 0 q74 ∷ []) Eq.refl

-- pass [TOFF012 CS03 TOFF012 CSd03] [CS03 X2 TOFF012 X2 CSd03 X2 TOFF012 X2]: 4 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2 = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw 0 q13 ∷
   rw 1 q9 ∷
   rw 4 q11 ∷
   rw 5 q9 ∷ []) Eq.refl

private
  q78 : Eqn
  q78 = eqn [] (X2 ∷ X2 ∷ []) (wn 871 W)
  q79 : Eqn
  q79 = eqn [] (CK20 ∷ CK20⁻ ∷ []) (wn 1355 W)
  q80 : Eqn
  q80 = eqn (X2 ∷ X2 ∷ []) [] (wn 389 W)
  q81 : Eqn
  q81 = eqn (CK20⁻ ∷ CK20 ∷ []) [] (wn 1356 W)

-- pass [X2 CKd20 X2] [TOFF012 CS03 TOFF012 CSd03]: 7 steps
lem-pass-X2-CKd20-X2-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd20-X2-vs-TOFF012-CS03-TOFF012-CSd03 = derive (X2 ∷ CK20⁻ ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  (rw 7 q78 ∷
   rw 8 q79 ∷
   rw 9 q78 ∷
   rw⁻ 3 q69 ∷
   rw 2 q80 ∷
   rw 1 q81 ∷
   rw 0 q80 ∷ []) Eq.refl
