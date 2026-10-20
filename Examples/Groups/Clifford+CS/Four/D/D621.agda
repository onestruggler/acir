{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D621 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D002 W using (lem-N23-D ; lem-comm-CCZ123-CCZ023)
open import Examples.Groups.Clifford+CS.Four.D.D003 W using (lem-comm-CCZ123-CCZ012)
open import Examples.Groups.Clifford+CS.Four.D.D004 W using (lem-comm-CCZ012-CZ13 ; lem-comm-CCZ013-CCZ012 ; lem-comm-CCZ013-CS12 ; lem-comm-CCZ123-CCZ013)
open import Examples.Groups.Clifford+CS.Four.D.D008 W using (lem-CCZ123-passes-CKd10 ; lem-comm-CZ01-CCZ023 ; lem-comm-CZ01-CCZ123)
open import Examples.Groups.Clifford+CS.Four.D.D510 W using (lem-CCZ012-passes-PP3 ; lem-CS12-passes-PP3 ; lem-CS13-passes-PP3 ; lem-CZ13-passes-PP3 ; lem-N23-PP3)
open import Examples.Groups.Clifford+CS.Four.D.D536 W using (lem-CCZ013-passes-PP3 ; lem-N32-PP3)
open import Examples.Groups.Clifford+CS.Four.D.D596 W using (lem-CCZ123-passes-PP3 ; lem-ROT≡cF)

private
  q1 : Eqn
  q1 = eqn (Sw23 ∷ []) (CX23 ∷ CX32 ∷ CX23 ∷ []) (wn 1863 W)
  q2 : Eqn
  q2 = eqn (CX23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX23 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12 ∷ CCZ012 ∷ CCZ123 ∷ []) (lem-N23-PP3)
  q3 : Eqn
  q3 = eqn [] (CX32 ∷ CX32 ∷ []) (wn 105 W)
  q4 : Eqn
  q4 = eqn (CX32 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX32 ∷ []) (CS13 ∷ CCZ013 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-N32-PP3)
  q5 : Eqn
  q5 = eqn (CX32 ∷ CS12 ∷ CX32 ∷ []) (CS12 ∷ CS13 ∷ CCZ123 ∷ []) (wn 1864 W)
  q6 : Eqn
  q6 = eqn (CX32 ∷ CCZ012 ∷ CX32 ∷ []) (CCZ012 ∷ CCZ013 ∷ []) (ax cx-ccz)
  q7 : Eqn
  q7 = eqn (CX32 ∷ CCZ123 ∷ CX32 ∷ []) (CCZ123 ∷ CZ13 ∷ []) (wn 1865 W)
  q8 : Eqn
  q8 = eqn (CS12 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12 ∷ []) lem-CS12-passes-PP3
  q9 : Eqn
  q9 = eqn (CS13 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS13 ∷ []) lem-CS13-passes-PP3
  q10 : Eqn
  q10 = eqn (CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ123 ∷ []) lem-CCZ123-passes-PP3
  q11 : Eqn
  q11 = eqn (CCZ012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ012 ∷ []) lem-CCZ012-passes-PP3
  q12 : Eqn
  q12 = eqn (CCZ013 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ013 ∷ []) lem-CCZ013-passes-PP3
  q13 : Eqn
  q13 = eqn (CZ13 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CZ13 ∷ []) lem-CZ13-passes-PP3
  q14 : Eqn
  q14 = eqn (CCZ123 ∷ CS12 ∷ []) (CS12 ∷ CCZ123 ∷ []) (wn 1187 W)
  q15 : Eqn
  q15 = eqn (CCZ123 ∷ CS13 ∷ []) (CS13 ∷ CCZ123 ∷ []) (wn 259 W)
  q16 : Eqn
  q16 = eqn (CCZ123 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CCZ012)
  q17 : Eqn
  q17 = eqn (CCZ123 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CCZ013)
  q18 : Eqn
  q18 = eqn (CCZ123 ∷ CZ13 ∷ []) (CZ13 ∷ CCZ123 ∷ []) (wn 1866 W)
  q19 : Eqn
  q19 = eqn (CCZ013 ∷ CS12 ∷ []) (CS12 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CS12)
  q20 : Eqn
  q20 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q21 : Eqn
  q21 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q22 : Eqn
  q22 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q23 : Eqn
  q23 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 43 W)
  q24 : Eqn
  q24 = eqn (CCZ012 ∷ CS12 ∷ []) (CS12 ∷ CCZ012 ∷ []) (wn 177 W)
  q25 : Eqn
  q25 = eqn (CS13 ∷ CS12 ∷ []) (CS12 ∷ CS13 ∷ []) (wn 101 W)
  q26 : Eqn
  q26 = eqn (CCZ013 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CCZ012)
  q27 : Eqn
  q27 = eqn (CCZ012 ∷ CZ12 ∷ []) (CZ12 ∷ CCZ012 ∷ []) (wn 178 W)
  q28 : Eqn
  q28 = eqn (CCZ012 ∷ CZ13 ∷ []) (CZ13 ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CZ13)
  q29 : Eqn
  q29 = eqn (CS13 ∷ CZ13 ∷ []) (CZ13 ∷ CS13 ∷ []) (wn 1867 W)
  q30 : Eqn
  q30 = eqn (CS12 ∷ CZ13 ∷ []) (CZ13 ∷ CS12 ∷ []) (wn 106 W)
  q31 : Eqn
  q31 = eqn (CS13 ∷ CS13 ∷ []) (CZ13 ∷ []) (wn 1868 W)
  q32 : Eqn
  q32 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wn 32 W)
  q33 : Eqn
  q33 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wn 33 W)
  q34 : Eqn
  q34 = eqn (CZ13 ∷ CZ13 ∷ []) [] (wn 1436 W)
  q35 : Eqn
  q35 = eqn (CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ123 ∷ []) (lem-CCZ123-passes-PP3)
  q36 : Eqn
  q36 = eqn (CCZ012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ012 ∷ []) (lem-CCZ012-passes-PP3)
  q37 : Eqn
  q37 = eqn (CS12 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12 ∷ []) (lem-CS12-passes-PP3)
  q38 : Eqn
  q38 = eqn [] (CX23 ∷ CX23 ∷ []) (wn 42 W)
  q39 : Eqn
  q39 = eqn (CX23 ∷ CS12 ∷ CX23 ∷ []) (CS12 ∷ []) (wn 1869 W)
  q40 : Eqn
  q40 = eqn (CX23 ∷ CCZ012 ∷ CX23 ∷ []) (CCZ012 ∷ []) (lem-N23-D)
  q41 : Eqn
  q41 = eqn (CX23 ∷ CCZ123 ∷ CX23 ∷ []) (CCZ123 ∷ CZ12 ∷ []) (wn 1870 W)
  q42 : Eqn
  q42 = eqn (CCZ123 ∷ CZ12 ∷ []) (CZ12 ∷ CCZ123 ∷ []) (wn 1871 W)
  q43 : Eqn
  q43 = eqn (CS12 ∷ CZ12 ∷ []) (CZ12 ∷ CS12 ∷ []) (wn 1872 W)
  q44 : Eqn
  q44 = eqn (CS12 ∷ CS12 ∷ []) (CZ12 ∷ []) (wn 1873 W)
  q45 : Eqn
  q45 = eqn (CZ12 ∷ CZ12 ∷ []) [] (wn 1453 W)

-- S3: 252 steps
lem-S3 : ⟪ (Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-S3 = derive (Sw23 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Sw23 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw 0 q1 ∷
   rw 7 q1 ∷
   rw 2 q2 ∷
   rw 6 q3 ∷
   rw 1 q4 ∷
   rw 11 q3 ∷
   rw 10 q3 ∷
   rw 8 q5 ∷
   rw 11 q6 ∷
   rw 13 q7 ∷
   rw⁻ 4 q8 ∷
   rw⁻ 5 q9 ∷
   rw⁻ 6 q10 ∷
   rw⁻ 7 q11 ∷
   rw⁻ 8 q12 ∷
   rw⁻ 9 q10 ∷
   rw⁻ 10 q13 ∷
   rw 3 q14 ∷
   rw 4 q15 ∷
   rw 6 q16 ∷
   rw 7 q17 ∷
   rw 9 q18 ∷
   rw 2 q19 ∷
   rw 5 q20 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q21 ∷
   re 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 5 q20 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q22 ∷
   rw 7 q20 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q22 ∷
   rw 9 q20 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q21 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q21 ∷
   rw 6 q22 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q21 ∷
   rw 4 q22 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q21 ∷
   rw 4 q23 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   rw 4 q24 ∷
   rw 5 q20 ∷
   re 3 3 (CS13 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 6 q20 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q22 ∷
   rw 8 q20 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q22 ∷
   rw 10 q20 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 4 q20 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q21 ∷
   rw⁻ 6 q22 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q21 ∷
   rw⁻ 8 q22 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q21 ∷
   rw 5 q23 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   re 4 3 (CCZ013 ∷ []) ∷
   rw 5 q21 ∷
   rw 5 q16 ∷
   rw 6 q17 ∷
   rw 8 q18 ∷
   rw 1 q25 ∷
   rw 4 q26 ∷
   rw 7 q18 ∷
   rw 8 q20 ∷
   re 7 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 9 q21 ∷
   re 6 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 8 q20 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q22 ∷
   rw 10 q20 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q22 ∷
   rw 12 q20 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q21 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q21 ∷
   rw 9 q22 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q21 ∷
   rw 7 q22 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q21 ∷
   rw 7 q23 ∷
   re 7 5 (CCZ012 ∷ []) ∷
   rw 7 q27 ∷
   rw 8 q20 ∷
   re 6 3 (CZ13 ∷ []) ∷
   re 8 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 9 q20 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q22 ∷
   rw 11 q20 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q22 ∷
   rw 13 q20 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 7 q20 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q21 ∷
   rw⁻ 9 q22 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q21 ∷
   rw⁻ 11 q22 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q21 ∷
   rw 8 q23 ∷
   re 8 5 (CCZ012 ∷ []) ∷
   re 7 3 (CCZ013 ∷ []) ∷
   rw 8 q21 ∷
   rw 7 q20 ∷
   re 6 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 8 q21 ∷
   re 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q20 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q22 ∷
   rw 9 q20 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q22 ∷
   rw 11 q20 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q21 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q21 ∷
   rw 8 q22 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q21 ∷
   rw 6 q22 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q21 ∷
   rw 6 q23 ∷
   re 6 5 (CCZ012 ∷ []) ∷
   rw 6 q27 ∷
   rw 7 q20 ∷
   re 5 3 (CZ13 ∷ []) ∷
   re 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 8 q20 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q22 ∷
   rw 10 q20 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q22 ∷
   rw 12 q20 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 6 q20 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q21 ∷
   rw⁻ 8 q22 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q21 ∷
   rw⁻ 10 q22 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q21 ∷
   rw 7 q23 ∷
   re 7 5 (CCZ012 ∷ []) ∷
   re 6 3 (CCZ013 ∷ []) ∷
   rw 7 q21 ∷
   rw 4 q28 ∷
   rw 3 q29 ∷
   rw 2 q29 ∷
   rw 1 q30 ∷
   rw 3 q31 ∷
   rw 7 q20 ∷
   re 6 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 8 q20 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q22 ∷
   rw 10 q20 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q22 ∷
   rw 12 q20 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q21 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q21 ∷
   rw 9 q22 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q21 ∷
   rw 7 q22 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q21 ∷
   rw 7 q23 ∷
   re 7 5 (CCZ012 ∷ []) ∷
   re 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q20 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q22 ∷
   rw 9 q20 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q22 ∷
   rw 11 q20 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q21 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q21 ∷
   rw 8 q22 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q21 ∷
   rw 6 q22 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q21 ∷
   rw 6 q23 ∷
   re 6 5 (CCZ012 ∷ []) ∷
   rw 6 q32 ∷
   rw 5 q21 ∷
   rw 5 q33 ∷
   rw 2 q30 ∷
   rw 1 q34 ∷
   rw 3 q35 ∷
   rw 2 q36 ∷
   rw 1 q37 ∷
   rw 5 q38 ∷
   rw 0 q2 ∷
   rw 10 q38 ∷
   rw 9 q38 ∷
   rw 7 q39 ∷
   rw 8 q40 ∷
   rw 9 q41 ∷
   rw 6 q14 ∷
   rw 7 q16 ∷
   rw 9 q42 ∷
   rw 5 q24 ∷
   rw 8 q42 ∷
   rw 7 q27 ∷
   rw 6 q27 ∷
   rw 5 q43 ∷
   rw 4 q43 ∷
   rw 5 q44 ∷
   rw 6 q32 ∷
   rw 6 q33 ∷
   rw 4 q45 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = eqn (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ023 ∷ []) (lem-ROT≡cF)
  q47 : Eqn
  q47 = eqn [] (X0 ∷ X0 ∷ []) (wn 873 W)
  q48 : Eqn
  q48 = eqn (X0 ∷ CK10 ∷ X0 ∷ []) (CK10 ∷ CZ01 ∷ CX10 ∷ []) (wn 1874 W)
  q49 : Eqn
  q49 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q50 : Eqn
  q50 = eqn (X0 ∷ Sw01 ∷ []) (Sw01 ∷ X1 ∷ []) (wn 1106 W)
  q51 : Eqn
  q51 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q52 : Eqn
  q52 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q53 : Eqn
  q53 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q54 : Eqn
  q54 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q55 : Eqn
  q55 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q56 : Eqn
  q56 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q57 : Eqn
  q57 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q58 : Eqn
  q58 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q59 : Eqn
  q59 = eqn (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 26 W)
  q60 : Eqn
  q60 = eqn (X1 ∷ CCZ123 ∷ X1 ∷ []) (CCZ123 ∷ CZ23 ∷ []) (wn 1875 W)
  q61 : Eqn
  q61 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q62 : Eqn
  q62 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q63 : Eqn
  q63 = eqn (Sw01 ∷ CZ23 ∷ []) (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ))
  q64 : Eqn
  q64 = eqn (X0 ∷ CK10⁻ ∷ X0 ∷ []) (CX10 ∷ CZ01 ∷ CK10⁻ ∷ []) (wn 1876 W)
  q65 : Eqn
  q65 = eqn (CX10 ∷ CZ23 ∷ []) (CZ23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (CZ))
  q66 : Eqn
  q66 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q67 : Eqn
  q67 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q68 : Eqn
  q68 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q69 : Eqn
  q69 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q70 : Eqn
  q70 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q71 : Eqn
  q71 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wn 47 W)
  q72 : Eqn
  q72 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wn 48 W)
  q73 : Eqn
  q73 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q74 : Eqn
  q74 = eqn (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) (wn 8 W)
  q75 : Eqn
  q75 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wn 9 W)
  q76 : Eqn
  q76 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wn 10 W)
  q77 : Eqn
  q77 = eqn (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 11 W)
  q78 : Eqn
  q78 = eqn (CX31 ∷ Sw12 ∷ []) (Sw12 ∷ CX32 ∷ []) (wn 13 W)
  q79 : Eqn
  q79 = eqn (CS12⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS12⁻ ∷ []) (wn 15 W)
  q80 : Eqn
  q80 = eqn (CS12 ∷ Sw12 ∷ []) (Sw12 ∷ CS12 ∷ []) (wn 16 W)
  q81 : Eqn
  q81 = eqn (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 17 W)
  q82 : Eqn
  q82 = eqn (Sw12 ∷ CS12 ∷ []) (CS12 ∷ Sw12 ∷ []) (wn 18 W)
  q83 : Eqn
  q83 = eqn (Sw12 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Sw12 ∷ []) (wn 19 W)
  q84 : Eqn
  q84 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q85 : Eqn
  q85 = eqn (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) (wn 21 W)
  q86 : Eqn
  q86 = eqn (Sw01 ∷ CX01 ∷ []) (CX10 ∷ Sw01 ∷ []) (wn 28 W)
  q87 : Eqn
  q87 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q88 : Eqn
  q88 = eqn (Sw23 ∷ CS23 ∷ []) (CS23 ∷ Sw23 ∷ []) (wn 71 W)
  q89 : Eqn
  q89 = eqn (Sw23 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw23 ∷ []) (wn 72 W)
  q90 : Eqn
  q90 = eqn (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 73 W)
  q91 : Eqn
  q91 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)
  q92 : Eqn
  q92 = eqn (Sw12 ∷ CX12 ∷ []) (CX21 ∷ Sw12 ∷ []) (wn 50 W)
  q93 : Eqn
  q93 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q94 : Eqn
  q94 = eqn (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 52 W)
  q95 : Eqn
  q95 = eqn (CZ01 ∷ CCZ023 ∷ []) (CCZ023 ∷ CZ01 ∷ []) (lem-comm-CZ01-CCZ023)
  q96 : Eqn
  q96 = eqn (CZ01 ∷ CCZ123 ∷ []) (CCZ123 ∷ CZ01 ∷ []) (lem-comm-CZ01-CCZ123)
  q97 : Eqn
  q97 = eqn (CZ01 ∷ CZ23 ∷ []) (CZ23 ∷ CZ01 ∷ []) (low-comm (CZ) (CZ))
  q98 : Eqn
  q98 = eqn (CZ01 ∷ CZ01 ∷ []) [] (wn 1877 W)
  q99 : Eqn
  q99 = eqn (CK10⁻ ∷ CZ23 ∷ []) (CZ23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CZ))
  q100 : Eqn
  q100 = eqn (CCZ123 ∷ CK10⁻ ∷ []) (CK10⁻ ∷ CCZ123 ∷ []) (lem-CCZ123-passes-CKd10)
  q101 : Eqn
  q101 = eqn (CZ23 ∷ CCZ123 ∷ []) (CCZ123 ∷ CZ23 ∷ []) (wn 1878 W)
  q102 : Eqn
  q102 = eqn (CCZ123 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CCZ023)
  q103 : Eqn
  q103 = eqn (CZ23 ∷ CZ23 ∷ []) [] (wn 1879 W)
  q104 : Eqn
  q104 = eqn (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ023 ∷ []) lem-ROT≡cF

-- X0-ROT: 427 steps
lem-X0-ROT : ⟪ (X0 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ CCZ123 ∷ []) ⟫ʷ
lem-X0-ROT = derive (X0 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ X0 ∷ []) (CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ S1 ∷ CK10 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ CCZ123 ∷ [])
  (rw 1 q46 ∷
   rw 4 q47 ∷
   rw 3 q47 ∷
   rw 2 q47 ∷
   rw 0 q48 ∷
   rw 6 q49 ∷
   rw 5 q50 ∷
   re 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q51 ∷
   rw 5 q52 ∷
   rw 6 q53 ∷
   rw 7 q52 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q54 ∷
   rw 9 q55 ∷
   rw 10 q54 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q56 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q54 ∷
   rw 9 q57 ∷
   rw⁻ 8 q54 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 7 q58 ∷
   rw⁻ 6 q53 ∷
   rw 5 q58 ∷
   rw⁻ 4 q51 ∷
   rw 5 q59 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   rw 3 q50 ∷
   rw 4 q60 ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 3 q51 ∷
   rw 4 q52 ∷
   rw 5 q53 ∷
   rw 6 q52 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q54 ∷
   rw 8 q55 ∷
   rw 9 q54 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 3 q49 ∷
   rw 4 q51 ∷
   rw 5 q61 ∷
   rw 6 q53 ∷
   rw 7 q61 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q54 ∷
   rw 9 q62 ∷
   rw 10 q54 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 4 q59 ∷
   re 4 5 (CCZ123 ∷ []) ∷
   re 3 3 (CCZ023 ∷ []) ∷
   rw 4 q63 ∷
   rw 5 q56 ∷
   rw 5 q64 ∷
   rw 11 q49 ∷
   rw 10 q50 ∷
   re 9 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 10 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 9 q51 ∷
   rw 10 q52 ∷
   rw 11 q53 ∷
   rw 12 q52 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q54 ∷
   rw 14 q55 ∷
   rw 15 q54 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 14 q56 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q54 ∷
   rw 14 q57 ∷
   rw⁻ 13 q54 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 12 q58 ∷
   rw⁻ 11 q53 ∷
   rw 10 q58 ∷
   rw⁻ 9 q51 ∷
   rw 10 q59 ∷
   re 10 5 (CCZ123 ∷ []) ∷
   rw 8 q50 ∷
   rw 9 q60 ∷
   re 9 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 8 q51 ∷
   rw 9 q52 ∷
   rw 10 q53 ∷
   rw 11 q52 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q54 ∷
   rw 13 q55 ∷
   rw 14 q54 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 8 q49 ∷
   rw 9 q51 ∷
   rw 10 q61 ∷
   rw 11 q53 ∷
   rw 12 q61 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q54 ∷
   rw 14 q62 ∷
   rw 15 q54 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 9 q59 ∷
   re 9 5 (CCZ123 ∷ []) ∷
   re 8 3 (CCZ023 ∷ []) ∷
   rw 9 q63 ∷
   rw 10 q56 ∷
   rw⁻ 4 q65 ∷
   rw 5 q66 ∷
   rw 4 q66 ∷
   re 5 3 (CX20 ∷ []) ∷
   re 3 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 3 q51 ∷
   rw 4 q52 ∷
   rw 5 q53 ∷
   rw 6 q52 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q54 ∷
   rw 8 q55 ∷
   rw 9 q54 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q56 ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 10 q67 ∷
   rw 9 q68 ∷
   rw 7 q69 ∷
   re 8 5 (CS03 ∷ []) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 8 q70 ∷
   rw 5 q71 ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 q70 ∷
   rw 3 q72 ∷
   rw 4 q20 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q21 ∷
   rw⁻ 6 q22 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q21 ∷
   rw⁻ 8 q22 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q21 ∷
   rw 5 q23 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   re 4 3 (CCZ013 ∷ []) ∷
   rw 2 q66 ∷
   re 3 3 (CX20 ∷ []) ∷
   rw 6 q20 ∷
   rw 5 q20 ∷
   re 6 3 (CX30 ∷ []) ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 6 q20 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q22 ∷
   rw 8 q20 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q22 ∷
   rw 10 q20 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q21 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q21 ∷
   rw 7 q22 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q21 ∷
   rw 5 q22 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q21 ∷
   rw 5 q23 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   rw 3 q20 ∷
   re 4 3 (CX30 ∷ []) ∷
   rw 7 q49 ∷
   re 6 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q54 ∷
   rw 7 q73 ∷
   rw⁻ 6 q54 ∷
   re 7 3 (CX31 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 9 q57 ∷
   rw 8 q74 ∷
   rw 7 q75 ∷
   rw 6 q74 ∷
   rw 5 q76 ∷
   rw 6 q77 ∷
   re 6 5 (CCZ012 ∷ []) ∷
   re 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q54 ∷
   rw 5 q73 ∷
   rw⁻ 4 q54 ∷
   re 5 3 (CX31 ∷ []) ∷
   rw 8 q66 ∷
   rw 7 q78 ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   re 10 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 12 q70 ∷
   rw 9 q66 ∷
   re 10 3 (CX02 ∷ []) ∷
   rw 8 q79 ∷
   rw 7 q66 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q80 ∷
   rw 7 q81 ∷
   re 7 5 (CCZ012 ∷ []) ∷
   rw 5 q78 ∷
   rw 6 q6 ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 5 q82 ∷
   rw 8 q66 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 7 q83 ∷
   rw 10 q66 ∷
   re 8 3 (CX02 ∷ []) ∷
   re 10 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 9 q70 ∷
   rw 5 q81 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   re 7 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 8 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 9 q20 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q22 ∷
   rw 11 q20 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q22 ∷
   rw 13 q20 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q21 ∷
   rw 6 q84 ∷
   rw 9 q66 ∷
   re 7 3 (CX02 ∷ []) ∷
   rw 8 q85 ∷
   rw 11 q66 ∷
   re 9 3 (CX02 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 10 q67 ∷
   rw⁻ 12 q68 ∷
   rw 13 q69 ∷
   re 10 5 (CS03 ∷ []) ∷
   rw 6 q49 ∷
   rw 7 q51 ∷
   rw 8 q61 ∷
   rw 9 q53 ∷
   rw 10 q61 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q54 ∷
   rw 12 q62 ∷
   rw 13 q54 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 7 q59 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   re 6 3 (CCZ023 ∷ []) ∷
   rw 7 q70 ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q55 ∷
   rw 5 q86 ∷
   rw 6 q87 ∷
   rw 7 q86 ∷
   rw 8 q62 ∷
   rw 4 q77 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   re 6 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 6 q51 ∷
   rw 7 q52 ∷
   rw 8 q53 ∷
   rw 9 q52 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q54 ∷
   rw 11 q55 ∷
   rw 12 q54 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q56 ∷
   rw 5 q51 ∷
   rw 6 q61 ∷
   rw 7 q53 ∷
   rw 8 q61 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q54 ∷
   rw 10 q62 ∷
   rw 11 q54 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q59 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   rw 6 q56 ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 5 q20 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q22 ∷
   rw 7 q20 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q22 ∷
   rw 9 q20 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 3 q20 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q21 ∷
   rw⁻ 5 q22 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q21 ∷
   rw⁻ 7 q22 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q21 ∷
   rw 4 q23 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   re 3 3 (CCZ013 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q88 ∷
   rw 7 q20 ∷
   re 5 3 (CX13 ∷ []) ∷
   rw 6 q89 ∷
   rw 9 q20 ∷
   re 7 3 (CX13 ∷ []) ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q21 ∷
   rw 4 q90 ∷
   re 4 5 (CCZ123 ∷ []) ∷
   rw 5 q21 ∷
   re 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 5 q20 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q22 ∷
   rw 7 q20 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q22 ∷
   rw 9 q20 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q21 ∷
   rw 2 q84 ∷
   rw 5 q66 ∷
   re 3 3 (CX02 ∷ []) ∷
   rw 4 q85 ∷
   rw 7 q66 ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 6 q67 ∷
   rw⁻ 8 q68 ∷
   rw 9 q69 ∷
   re 6 5 (CS03 ∷ []) ∷
   rw 2 q49 ∷
   rw 3 q51 ∷
   rw 4 q61 ∷
   rw 5 q53 ∷
   rw 6 q61 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q54 ∷
   rw 8 q62 ∷
   rw 9 q54 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 3 q59 ∷
   re 3 5 (CCZ123 ∷ []) ∷
   re 2 3 (CCZ023 ∷ []) ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 3 q91 ∷
   rw 4 q92 ∷
   rw 5 q93 ∷
   rw 6 q92 ∷
   rw 7 q84 ∷
   rw 3 q94 ∷
   re 3 5 (CCZ123 ∷ []) ∷
   rw 4 q70 ∷
   rw 1 q95 ∷
   rw 2 q96 ∷
   rw 3 q97 ∷
   rw 4 q98 ∷
   rw⁻ 3 q99 ∷
   rw 2 q100 ∷
   rw 6 q49 ∷
   re 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q51 ∷
   rw 6 q52 ∷
   rw 7 q53 ∷
   rw 8 q52 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q54 ∷
   rw 10 q55 ∷
   rw 11 q54 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q56 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q54 ∷
   rw 10 q57 ∷
   rw⁻ 9 q54 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 8 q58 ∷
   rw⁻ 7 q53 ∷
   rw 6 q58 ∷
   rw⁻ 5 q51 ∷
   rw 6 q59 ∷
   re 6 5 (CCZ123 ∷ []) ∷
   rw⁻ 4 q63 ∷
   rw 5 q101 ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q51 ∷
   rw 5 q52 ∷
   rw 6 q53 ∷
   rw 7 q52 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q54 ∷
   rw 9 q55 ∷
   rw 10 q54 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 4 q49 ∷
   rw 5 q51 ∷
   rw 6 q61 ∷
   rw 7 q53 ∷
   rw 8 q61 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q54 ∷
   rw 10 q62 ∷
   rw 11 q54 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q59 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 4 3 (CCZ023 ∷ []) ∷
   rw 5 q63 ∷
   rw 6 q56 ∷
   rw 3 q102 ∷
   rw 5 q103 ∷
   rw⁻ 0 q104 ∷ []) Eq.refl
