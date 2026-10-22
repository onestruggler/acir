{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D447 (W : Ws) where

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
  q1 = wE 1194 W
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 20 W
  q4 : Eqn
  q4 = eqn (CK10⁻ ∷ CS23 ∷ []) (CS23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CS))
  q5 : Eqn
  q5 = wE 49 W
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q8 : Eqn
  q8 = wE 102 W
  q9 : Eqn
  q9 = eqn (CK10⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap))
  q10 : Eqn
  q10 = wE 1140 W
  q11 : Eqn
  q11 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q12 : Eqn
  q12 = wE 103 W
  q13 : Eqn
  q13 = eqn (CK10 ∷ CS23 ∷ []) (CS23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CS))
  q14 : Eqn
  q14 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q15 : Eqn
  q15 = wE 607 W
  q16 : Eqn
  q16 = wE 5 W
  q17 : Eqn
  q17 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q18 : Eqn
  q18 = wE 137 W
  q19 : Eqn
  q19 = wE 1193 W
  q20 : Eqn
  q20 = wE 139 W
  q21 : Eqn
  q21 = wE 31 W
  q22 : Eqn
  q22 = eqn (CS01⁻ ∷ CX23 ∷ []) (CX23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CX₀₁))
  q23 : Eqn
  q23 = eqn (CK10⁻ ∷ CX23 ∷ []) (CX23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₀₁))
  q24 : Eqn
  q24 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q25 : Eqn
  q25 = wE 140 W
  q26 : Eqn
  q26 = wE 917 W
  q27 : Eqn
  q27 = wE 142 W
  q28 : Eqn
  q28 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q29 : Eqn
  q29 = wE 21 W
  q30 : Eqn
  q30 = eqn (CK10⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) ((CS • CS • CS)))
  q31 : Eqn
  q31 = wE 51 W
  q32 : Eqn
  q32 = wE 199 W
  q33 : Eqn
  q33 = wE 1142 W
  q34 : Eqn
  q34 = wE 200 W
  q35 : Eqn
  q35 = eqn (CK10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((CS • CS • CS)))
  q36 : Eqn
  q36 = wE 609 W

-- groups [CS01 CK10 CSd01 CK20 CS01 CKd10 CSd01 CKd20] [CS12 CS13 CX23 CSd13 CX23]: 209 steps
lem-groups-CS01-CK10-CSd01-CK20-CS01-CKd10-CSd01-CKd20-vs-CS12-CS13-CX23-CSd13-CX23 : ⟪ (CS01 ∷ CK10 ∷ CS01⁻ ∷ CK20 ∷ CS01 ∷ CK10⁻ ∷ CS01⁻ ∷ CK20⁻ ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS01 ∷ CK10 ∷ CS01⁻ ∷ CK20 ∷ CS01 ∷ CK10⁻ ∷ CS01⁻ ∷ CK20⁻ ∷ []) ⟫ʷ
lem-groups-CS01-CK10-CSd01-CK20-CS01-CKd10-CSd01-CKd20-vs-CS12-CS13-CX23-CSd13-CX23 = derive (CS01 ∷ CK10 ∷ CS01⁻ ∷ CK20 ∷ CS01 ∷ CK10⁻ ∷ CS01⁻ ∷ CK20⁻ ∷ CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS01 ∷ CK10 ∷ CS01⁻ ∷ CK20 ∷ CS01 ∷ CK10⁻ ∷ CS01⁻ ∷ CK20⁻ ∷ [])
  (rw 0 q1 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   re 9 3 (CK30⁻ ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q2 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 12 q3 ∷
   rw 11 q4 ∷
   rw 10 q5 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   re 10 5 (CK30⁻ ∷ []) ∷
   re 10 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 9 q2 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw 7 q7 ∷
   rw 8 q8 ∷
   rw 9 q2 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q7 ∷
   rw 9 q6 ∷
   rw 8 q2 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 6 q9 ∷
   rw 7 q10 ∷
   rw 8 q2 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q9 ∷
   rw 8 q6 ∷
   rw 7 q2 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q11 ∷
   rw 6 q12 ∷
   rw 7 q2 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q11 ∷
   rw 7 q6 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q2 ∷
   re 5 3 (CK30 ∷ []) ∷
   re 5 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 11 q2 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 8 q3 ∷
   rw 7 q13 ∷
   rw 6 q5 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   re 6 5 (CK30 ∷ []) ∷
   re 6 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 5 q2 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 3 q7 ∷
   rw 4 q8 ∷
   rw 5 q2 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q7 ∷
   rw 5 q6 ∷
   rw 4 q2 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 2 q14 ∷
   rw 3 q15 ∷
   rw 4 q2 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q14 ∷
   rw 4 q6 ∷
   rw 3 q2 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw 1 q11 ∷
   rw 2 q12 ∷
   rw 3 q2 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q11 ∷
   rw 3 q6 ∷
   rw 11 q16 ∷
   rw⁻ 10 q17 ∷
   rw 9 q18 ∷
   rw 10 q19 ∷
   rw 9 q17 ∷
   rw 10 q20 ∷
   rw 11 q21 ∷
   rw 8 q22 ∷
   rw 7 q23 ∷
   rw 6 q24 ∷
   rw 7 q16 ∷
   rw⁻ 6 q17 ∷
   rw 5 q25 ∷
   rw 6 q26 ∷
   rw 5 q17 ∷
   rw 6 q27 ∷
   rw 7 q21 ∷
   rw 4 q22 ∷
   rw 3 q28 ∷
   rw 2 q24 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   re 11 3 (CK30⁻ ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q2 ∷
   re 15 3 (CS13⁻ ∷ []) ∷
   rw 14 q29 ∷
   rw 13 q30 ∷
   rw 12 q31 ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   re 12 5 (CK30⁻ ∷ []) ∷
   re 12 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q6 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw 11 q2 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   rw 9 q7 ∷
   rw 10 q32 ∷
   rw 11 q2 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q7 ∷
   rw 11 q6 ∷
   rw 10 q2 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   rw 8 q9 ∷
   rw 9 q33 ∷
   rw 10 q2 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q9 ∷
   rw 10 q6 ∷
   rw 9 q2 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw 7 q11 ∷
   rw 8 q34 ∷
   rw 9 q2 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q11 ∷
   rw 9 q6 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q2 ∷
   re 7 3 (CK30 ∷ []) ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 13 q2 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw 10 q29 ∷
   rw 9 q35 ∷
   rw 8 q31 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   re 8 5 (CK30 ∷ []) ∷
   re 8 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw 7 q2 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q7 ∷
   rw 6 q32 ∷
   rw 7 q2 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q7 ∷
   rw 7 q6 ∷
   rw 6 q2 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 4 q14 ∷
   rw 5 q36 ∷
   rw 6 q2 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q14 ∷
   rw 6 q6 ∷
   rw 5 q2 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 3 q11 ∷
   rw 4 q34 ∷
   rw 5 q2 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q11 ∷
   rw 5 q6 ∷
   rw 13 q16 ∷
   rw⁻ 12 q17 ∷
   rw 11 q18 ∷
   rw 12 q19 ∷
   rw 11 q17 ∷
   rw 12 q20 ∷
   rw 13 q21 ∷
   rw 10 q22 ∷
   rw 9 q23 ∷
   rw 8 q24 ∷
   rw 9 q16 ∷
   rw⁻ 8 q17 ∷
   rw 7 q25 ∷
   rw 8 q26 ∷
   rw 7 q17 ∷
   rw 8 q27 ∷
   rw 9 q21 ∷
   rw 6 q22 ∷
   rw 5 q28 ∷
   rw 4 q24 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS)))
  q38 : Eqn
  q38 = wE 457 W
  q39 : Eqn
  q39 = eqn (S1 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S1 ∷ []) (low-comm ((S ↑)) ((CS • CS • CS)))
  q40 : Eqn
  q40 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q41 : Eqn
  q41 = wE 7 W
  q42 : Eqn
  q42 = wE 416 W
  q43 : Eqn
  q43 = wE 27 W
  q44 : Eqn
  q44 = wE 626 W

-- groups [CS02 CS02 CK20 CS02 CX21 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01] [CSd23]: 45 steps
lem-groups-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-vs-CSd23 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ []) ⟫ʷ
lem-groups-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-vs-CSd23 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ [])
  (rw 20 q37 ∷
   rw 19 q35 ∷
   rw 18 q37 ∷
   rw 17 q37 ∷
   rw 16 q38 ∷
   rw 15 q37 ∷
   rw 14 q37 ∷
   rw 13 q37 ∷
   rw 12 q37 ∷
   rw 11 q37 ∷
   rw 10 q37 ∷
   rw 9 q39 ∷
   rw 8 q35 ∷
   rw 7 q37 ∷
   rw 6 q37 ∷
   rw 5 q37 ∷
   rw 4 q38 ∷
   rw 5 q16 ∷
   rw⁻ 4 q40 ∷
   rw 3 q41 ∷
   rw 4 q42 ∷
   rw 3 q40 ∷
   rw 4 q43 ∷
   rw 5 q21 ∷
   rw 4 q16 ∷
   rw⁻ 3 q40 ∷
   rw 2 q25 ∷
   rw 3 q44 ∷
   rw 2 q40 ∷
   rw 3 q27 ∷
   rw 4 q21 ∷
   rw 3 q16 ∷
   rw⁻ 2 q40 ∷
   rw 1 q41 ∷
   rw 2 q42 ∷
   rw 1 q40 ∷
   rw 2 q43 ∷
   rw 3 q21 ∷
   rw 2 q16 ∷
   rw⁻ 1 q40 ∷
   rw 0 q41 ∷
   rw 1 q42 ∷
   rw 0 q40 ∷
   rw 1 q43 ∷
   rw 2 q21 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = wE 12 W
  q46 : Eqn
  q46 = wE 338 W
  q47 : Eqn
  q47 = wE 14 W
  q48 : Eqn
  q48 = wE 379 W
  q49 : Eqn
  q49 = wE 361 W
  q50 : Eqn
  q50 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q51 : Eqn
  q51 = wE 151 W
  q52 : Eqn
  q52 = eqn (Sw12 ∷ S3 ∷ []) (S3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (S))
  q53 : Eqn
  q53 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q54 : Eqn
  q54 = wE 1195 W

-- bridge G-ki: 86 steps
lem-bridge-G-ki : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ Sw12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sw12 ∷ CX12 ∷ Sw12 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ Sw12 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CK23 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ Sw12 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ Sw12 ∷ CX12 ∷ Sw12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sw12 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ S2 ∷ CK23 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) ⟫ʷ
lem-bridge-G-ki = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ Sw12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sw12 ∷ CX12 ∷ Sw12 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ Sw12 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ CK23 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX12 ∷ Sw12 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ Sw12 ∷ CX12 ∷ Sw12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sw12 ∷ Sw01 ∷ Sw12 ∷ Sw23 ∷ S2 ∷ CK23 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ [])
  (rw 7 q45 ∷
   re 5 3 (CS02 ∷ []) ∷
   rw 8 q45 ∷
   re 6 3 (CS02 ∷ []) ∷
   rw 9 q45 ∷
   re 7 3 (CS02 ∷ []) ∷
   rw 10 q45 ∷
   re 8 3 (CK20 ∷ []) ∷
   rw 9 q46 ∷
   rw 12 q45 ∷
   re 10 3 (CS02 ∷ []) ∷
   rw 13 q45 ∷
   re 11 3 (CS02 ∷ []) ∷
   rw 14 q45 ∷
   re 12 3 (CS02 ∷ []) ∷
   rw 15 q45 ∷
   re 13 3 (CS02 ∷ []) ∷
   rw 16 q45 ∷
   re 14 3 (CS02 ∷ []) ∷
   rw 17 q45 ∷
   re 15 3 (CS02 ∷ []) ∷
   rw 16 q47 ∷
   rw 19 q45 ∷
   re 17 3 (CS02 ∷ []) ∷
   rw 20 q45 ∷
   re 18 3 (CS02 ∷ []) ∷
   rw 21 q45 ∷
   re 19 3 (CK20 ∷ []) ∷
   rw 22 q45 ∷
   re 20 3 (CS02 ∷ []) ∷
   rw 21 q47 ∷
   rw 42 q45 ∷
   re 40 3 (CS02 ∷ []) ∷
   rw 43 q45 ∷
   re 41 3 (CS02 ∷ []) ∷
   rw 44 q45 ∷
   re 42 3 (CK20 ∷ []) ∷
   rw 45 q45 ∷
   re 43 3 (CS02 ∷ []) ∷
   rw 44 q47 ∷
   rw 47 q45 ∷
   re 45 3 (CS02 ∷ []) ∷
   rw 48 q45 ∷
   re 46 3 (CS02 ∷ []) ∷
   rw 49 q45 ∷
   re 47 3 (CS02 ∷ []) ∷
   rw 50 q45 ∷
   re 48 3 (CK20 ∷ []) ∷
   rw 49 q46 ∷
   rw 52 q45 ∷
   re 50 3 (CS02 ∷ []) ∷
   rw 53 q45 ∷
   re 51 3 (CS02 ∷ []) ∷
   rw 54 q45 ∷
   re 52 3 (CS02 ∷ []) ∷
   rw 55 q45 ∷
   re 53 3 (CS02 ∷ []) ∷
   rw 56 q45 ∷
   re 54 3 (CS02 ∷ []) ∷
   rw 57 q45 ∷
   re 55 3 (CS02 ∷ []) ∷
   rw 56 q47 ∷
   rw 23 q48 ∷
   rw 24 q6 ∷
   rw 22 q49 ∷
   rw 23 q47 ∷
   re 22 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 21 q50 ∷
   rw 22 q27 ∷
   rw 23 q50 ∷
   re 21 3 (CK30 ∷ []) ∷
   rw 22 q21 ∷
   rw 52 q51 ∷
   rw 53 q48 ∷
   rw 54 q6 ∷
   rw 51 q52 ∷
   rw 52 q49 ∷
   rw 53 q47 ∷
   rw 50 q53 ∷
   re 52 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 51 q50 ∷
   rw 52 q27 ∷
   rw 53 q50 ∷
   re 51 3 (CK30 ∷ []) ∷
   rw 52 q21 ∷
   rw 22 q54 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = wE 1196 W
  q56 : Eqn
  q56 = wE 1197 W
  q57 : Eqn
  q57 = wE 1198 W
  q58 : Eqn
  q58 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) [] (trans (by-assoc Eq.refl) (trans (ax hyb-sq) (by-assoc Eq.refl)))
  q59 : Eqn
  q59 = wE 387 W

-- top ki-sq: 8 steps
lem-top-ki-sq : ⟪ (X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X0 ∷ X1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X0 ∷ X1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-top-ki-sq = derive (X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X0 ∷ X1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X0 ∷ X1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ []) []
  (rw 194 q55 ∷
   rw 186 q56 ∷
   rw 178 q56 ∷
   rw 171 q57 ∷
   rw 88 q55 ∷
   rw 81 q57 ∷
   rw 1 q58 ∷
   rw 0 q59 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = eqn (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X1 ∷ X1 ∷ X2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X1 ∷ X2 ∷ X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X1 ∷ X2 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X0 ∷ X1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X1 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ X0 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK31 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X0 ∷ X1 ∷ X1 ∷ X2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X0 ∷ X1 ∷ X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X0 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X0 ∷ X1 ∷ X2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X1 ∷ X2 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ X0 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK31 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X0 ∷ X1 ∷ X1 ∷ X2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X0 ∷ X1 ∷ X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X0 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X0 ∷ X1 ∷ X2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X1 ∷ X2 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X1 ∷ X1 ∷ X2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X1 ∷ X2 ∷ X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X1 ∷ X2 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X0 ∷ X1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ []) (trans (by-assoc Eq.refl) (trans (ax hyb-yb) (by-assoc Eq.refl)))

-- top ki-yb: 1 steps
lem-top-ki-yb : ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X1 ∷ X1 ∷ X2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X1 ∷ X2 ∷ X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X1 ∷ X2 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X0 ∷ X1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X1 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ X0 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK31 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X0 ∷ X1 ∷ X1 ∷ X2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X0 ∷ X1 ∷ X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X0 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X0 ∷ X1 ∷ X2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X1 ∷ X2 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ X0 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK31 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X0 ∷ X1 ∷ X1 ∷ X2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X0 ∷ X1 ∷ X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X0 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X0 ∷ X1 ∷ X2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X1 ∷ X2 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X1 ∷ X1 ∷ X2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X1 ∷ X2 ∷ X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X1 ∷ X2 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X0 ∷ X1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ []) ⟫ʷ
lem-top-ki-yb = derive (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X1 ∷ X1 ∷ X2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X1 ∷ X2 ∷ X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X1 ∷ X2 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X0 ∷ X1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ X1 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ X0 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK31 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X0 ∷ X1 ∷ X1 ∷ X2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X0 ∷ X1 ∷ X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X0 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X0 ∷ X1 ∷ X2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X1 ∷ X2 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ []) (X1 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X1 ∷ X0 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK31 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X0 ∷ X1 ∷ X1 ∷ X2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X0 ∷ X1 ∷ X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X0 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X0 ∷ X1 ∷ X2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X1 ∷ X2 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X1 ∷ X1 ∷ X2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X1 ∷ X2 ∷ X0 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ X0 ∷ X1 ∷ X2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X1 ∷ X2 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X0 ∷ X1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X1 ∷ [])
  (rw 0 q60 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = wE 1199 W
  q62 : Eqn
  q62 = wE 1200 W

-- respell hyb CS02 CS02 CK20 CS02 CX21 CS01 CS01 CS01  -> CS01 CS01 CK10 CS01 CX12 CS02 CS02 CS02 : 2 steps
lem-respell-hyb-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01---⟶-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02- : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S3 ∷ CK30 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) ⟫ʷ
lem-respell-hyb-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01---⟶-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02- = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S3 ∷ CK30 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ [])
  (rw 0 q61 ∷
   rw 22 q62 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = wE 1201 W
  q64 : Eqn
  q64 = wE 1202 W

-- respell hyb CS12 CS12 CK21 CS12 CX20 CS01 CS01 CS01  -> CS01 CS01 CK01 CS01 CX02 CS12 CS12 CS12 : 2 steps
lem-respell-hyb-CS12-CS12-CK21-CS12-CX20-CS01-CS01-CS01---⟶-CS01-CS01-CK01-CS01-CX02-CS12-CS12-CS12- : ⟪ (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S3 ∷ CK31 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK31 ∷ []) ⟫ʷ
lem-respell-hyb-CS12-CS12-CK21-CS12-CX20-CS01-CS01-CS01---⟶-CS01-CS01-CK01-CS01-CX02-CS12-CS12-CS12- = derive (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX20 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S3 ∷ CK31 ∷ []) (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK31 ∷ [])
  (rw 0 q63 ∷
   rw 22 q64 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = wE 1203 W
  q66 : Eqn
  q66 = wE 1204 W

-- respell hyb CS01 CS01 CK10 CS01 CX12 CS02 CS02 CS02  -> CS02 CS02 CK20 CS02 CX21 CS01 CS01 CS01 : 2 steps
lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01- : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S3 ∷ CK30 ∷ []) ⟫ʷ
lem-respell-hyb-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02---⟶-CS02-CS02-CK20-CS02-CX21-CS01-CS01-CS01- = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S3 ∷ CK30 ∷ [])
  (rw 0 q65 ∷
   rw 22 q66 ∷ []) Eq.refl
