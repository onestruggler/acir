{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D664 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D614 W using (lem-pass-CK30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3)
open import Examples.Groups.Clifford+CS.Four.D.D623 W using (lem-pass-CS20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 ; lem-pass-CSd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3)
open import Examples.Groups.Clifford+CS.Four.D.D644 W using (lem-pass-CKd30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 ; lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-CZ13-CCZ123)

private
  q1 : Eqn
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q3 : Eqn
  q3 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q4 : Eqn
  q4 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q5 : Eqn
  q5 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q6 : Eqn
  q6 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = eqn (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) (CK31 ∷ CS12 ∷ CK31⁻ ∷ CS12⁻ ∷ []) (wn 2004 W)
  q8 : Eqn
  q8 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CK21⁻ ∷ []) (CK20⁻ ∷ Sw01 ∷ []) (wn 139 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q13 : Eqn
  q13 = eqn (CS02⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS02⁻ ∷ []) (lem-pass-CSd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3)
  q14 : Eqn
  q14 = eqn (CK30⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK30⁻ ∷ []) (lem-pass-CKd30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3)
  q15 : Eqn
  q15 = eqn (CS02 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS02 ∷ []) (lem-pass-CS20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3)
  q16 : Eqn
  q16 = eqn (CK30 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CK30 ∷ []) (lem-pass-CK30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3)
  q17 : Eqn
  q17 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q18 : Eqn
  q18 = eqn (CK20⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK21⁻ ∷ []) (wn 137 W)
  q19 : Eqn
  q19 = eqn (CK31 ∷ CS12 ∷ CK31⁻ ∷ CS12⁻ ∷ []) (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) (wn 2005 W)

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 140 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 29 q1 ∷
   rw 28 q2 ∷
   rw 27 q2 ∷
   rw 26 q3 ∷
   rw 25 q2 ∷
   rw 24 q3 ∷
   rw 23 q3 ∷
   rw⁻ 22 q4 ∷
   rw 21 q3 ∷
   rw 20 q3 ∷
   rw 19 q3 ∷
   rw 18 q3 ∷
   rw 17 q3 ∷
   rw 16 q3 ∷
   rw⁻ 15 q5 ∷
   rw 14 q2 ∷
   rw 13 q3 ∷
   rw 12 q3 ∷
   rw 11 q3 ∷
   rw⁻ 10 q5 ∷
   rw 9 q2 ∷
   rw⁻ 8 q5 ∷
   rw 7 q2 ∷
   rw⁻ 6 q4 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q6 ∷
   rw 6 q2 ∷
   rw⁻ 5 q6 ∷
   re 6 3 (CK31 ∷ []) ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q6 ∷
   rw 5 q2 ∷
   rw⁻ 4 q6 ∷
   re 5 3 (CK31 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q6 ∷
   rw 4 q3 ∷
   rw⁻ 3 q6 ∷
   re 4 3 (CS13 ∷ []) ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q6 ∷
   rw 3 q2 ∷
   rw⁻ 2 q6 ∷
   re 3 3 (CK31 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q6 ∷
   rw 2 q3 ∷
   rw⁻ 1 q6 ∷
   re 2 3 (CS13 ∷ []) ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q6 ∷
   rw 1 q3 ∷
   rw⁻ 0 q6 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q7 ∷
   re 1 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 0 q6 ∷
   rw 1 q8 ∷
   rw 2 q6 ∷
   re 0 3 (CK30 ∷ []) ∷
   rw 1 q9 ∷
   re 3 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q6 ∷
   rw 3 q10 ∷
   rw 4 q6 ∷
   re 2 3 (CK30⁻ ∷ []) ∷
   rw 3 q11 ∷
   rw 4 q12 ∷
   rw 3 q13 ∷
   rw 2 q14 ∷
   rw 1 q15 ∷
   rw 0 q16 ∷
   rw 12 q1 ∷
   rw 11 q17 ∷
   re 10 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q6 ∷
   rw 11 q18 ∷
   rw⁻ 10 q6 ∷
   re 11 3 (CK31⁻ ∷ []) ∷
   rw 9 q3 ∷
   re 8 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q6 ∷
   rw 9 q2 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (CK31 ∷ []) ∷
   rw 9 q19 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 9 q9 ∷
   rw 10 q6 ∷
   re 8 3 (CS03 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 10 q9 ∷
   rw 11 q6 ∷
   re 9 3 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw 11 q8 ∷
   rw 12 q6 ∷
   re 10 3 (CK30 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   rw 12 q9 ∷
   rw 13 q6 ∷
   re 11 3 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   rw 13 q8 ∷
   rw 14 q6 ∷
   re 12 3 (CK30 ∷ []) ∷
   re 14 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 13 q6 ∷
   rw 14 q8 ∷
   rw 15 q6 ∷
   re 13 3 (CK30 ∷ []) ∷
   rw 14 q4 ∷
   rw 15 q8 ∷
   rw 16 q5 ∷
   rw 17 q8 ∷
   rw 18 q5 ∷
   rw 19 q9 ∷
   rw 20 q9 ∷
   rw 21 q9 ∷
   rw 22 q8 ∷
   rw 23 q5 ∷
   rw 24 q9 ∷
   rw 25 q9 ∷
   rw 26 q9 ∷
   rw 27 q9 ∷
   rw 28 q9 ∷
   rw 29 q9 ∷
   rw 30 q4 ∷
   rw 31 q9 ∷
   rw 32 q9 ∷
   rw 33 q8 ∷
   rw 34 q9 ∷
   rw 35 q8 ∷
   rw 36 q8 ∷
   rw 37 q12 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = eqn (X2 ∷ CCZ123 ∷ []) (CZ13 ∷ CCZ123 ∷ X2 ∷ []) (wn 1987 W)
  q21 : Eqn
  q21 = eqn (X0 ∷ CZ13 ∷ []) (CZ13 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑ • CZ • Swap ↑)))
  q22 : Eqn
  q22 = eqn (X0 ∷ CCZ123 ∷ []) (CCZ123 ∷ X0 ∷ []) (low₁-comm (X) (CCZ))
  q23 : Eqn
  q23 = eqn (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CZ13 ∷ CCZ123 ∷ []) (CZ13 ∷ CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-CZ13-CCZ123)
  q24 : Eqn
  q24 = eqn (X2 ∷ CZ13 ∷ []) (CZ13 ∷ X2 ∷ []) (wn 1989 W)
  q25 : Eqn
  q25 = eqn (CZ13 ∷ CZ13 ∷ CCZ123 ∷ []) (CCZ123 ∷ []) (wn 2006 W)

-- pass [X0 X2 CS13 TOFF102 CSd13 TOFF102 X0 X2] [CCZ123]: 10 steps
lem-pass-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2-vs-CCZ123 : ⟪ (X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2-vs-CCZ123 = derive (X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ CCZ123 ∷ []) (CCZ123 ∷ X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ [])
  (rw 7 q20 ∷
   rw 6 q21 ∷
   rw 7 q22 ∷
   rw 2 q23 ∷
   rw 1 q24 ∷
   rw 2 q20 ∷
   rw 0 q21 ∷
   rw 1 q21 ∷
   rw 2 q22 ∷
   rw 0 q25 ∷ []) Eq.refl
