{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D446 (W : Ws) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Four.Str using (ℓ)

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 3 W
  q3 : Eqn
  q3 = wE 1189 W
  q4 : Eqn
  q4 = wE 5 W
  q5 : Eqn
  q5 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q6 : Eqn
  q6 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = wE 137 W
  q8 : Eqn
  q8 = wE 1190 W
  q9 : Eqn
  q9 = wE 139 W
  q10 : Eqn
  q10 = wE 31 W
  q11 : Eqn
  q11 = wE 157 W
  q12 : Eqn
  q12 = eqn (ℓ "丵乌") (ℓ "乌丵") (low-comm ((S ↑ • CK₁₀)) (CX₀₁))
  q13 : Eqn
  q13 = wE 158 W
  q14 : Eqn
  q14 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q15 : Eqn
  q15 = wE 1191 W

-- groups [CKd30] [CS13 CS23 CX12 CSd23 CX12]: 59 steps
lem-groups-CKd30-vs-CS13-CS23-CX12-CSd23-CX12 : ⟪ (ℓ "乒丽义丹乊丹") ⟫ʷ ≈ ⟪ (ℓ "丽义丹乊丹乒") ⟫ʷ
lem-groups-CKd30-vs-CS13-CS23-CX12-CSd23-CX12 = derive (ℓ "乒丽义丹乊丹") (ℓ "丽义丹乊丹乒")
  (rw 2 q1 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q2 ∷
   re 0 1 (ℓ "乏久乏") ∷
   rw 2 q2 ∷
   rw 1 q3 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "丽") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "乒") ∷
   rw 2 q2 ∷
   rw 3 q4 ∷
   rw⁻ 2 q5 ∷
   re 1 1 (ℓ "乏久乏") ∷
   rw⁻ 3 q6 ∷
   rw 2 q7 ∷
   rw⁻ 1 q6 ∷
   re 2 3 (ℓ "乕") ∷
   rw 2 q8 ∷
   rw 1 q5 ∷
   re 3 1 (ℓ "乏么乏") ∷
   rw 2 q6 ∷
   rw 3 q9 ∷
   rw 4 q6 ∷
   re 2 3 (ℓ "乒") ∷
   rw 3 q10 ∷
   re 2 1 (ℓ "乏丼丵丼乏") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乀") ∷
   rw 5 q11 ∷
   rw 4 q12 ∷
   rw 3 q13 ∷
   re 3 1 (ℓ "乏丹乏") ∷
   rw 2 q2 ∷
   re 3 5 (ℓ "乒") ∷
   rw 5 q4 ∷
   rw⁻ 4 q14 ∷
   re 3 1 (ℓ "乏久乏") ∷
   rw⁻ 5 q6 ∷
   rw 4 q7 ∷
   rw⁻ 3 q6 ∷
   re 4 3 (ℓ "乕") ∷
   rw 4 q15 ∷
   rw 3 q14 ∷
   re 5 1 (ℓ "乏么乏") ∷
   rw 4 q6 ∷
   rw 5 q9 ∷
   rw 6 q6 ∷
   re 4 3 (ℓ "乒") ∷
   rw 5 q10 ∷
   re 4 1 (ℓ "乏丼丵丼乏") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "乀") ∷
   rw 7 q11 ∷
   rw 6 q12 ∷
   rw 5 q13 ∷
   re 5 1 (ℓ "乏丹乏") ∷
   rw 4 q2 ∷
   re 5 5 (ℓ "乒") ∷ []) Eq.refl

-- groups [CKd30] [CSd23]: 15 steps
lem-groups-CKd30-vs-CSd23 : ⟪ (ℓ "乒乊") ⟫ʷ ≈ ⟪ (ℓ "乊乒") ⟫ʷ
lem-groups-CKd30-vs-CSd23 = derive (ℓ "乒乊") (ℓ "乊乒")
  (rw 2 q4 ∷
   rw⁻ 1 q14 ∷
   re 0 1 (ℓ "乏久乏") ∷
   rw⁻ 2 q6 ∷
   rw 1 q7 ∷
   rw⁻ 0 q6 ∷
   re 1 3 (ℓ "乕") ∷
   rw 1 q15 ∷
   rw 0 q14 ∷
   re 2 1 (ℓ "乏么乏") ∷
   rw 1 q6 ∷
   rw 2 q9 ∷
   rw 3 q6 ∷
   re 1 3 (ℓ "乒") ∷
   rw 2 q10 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = wE 1192 W
  q17 : Eqn
  q17 = wE 20 W
  q18 : Eqn
  q18 = eqn (ℓ "両义") (ℓ "义両") (low-comm ((CS • CS • CS)) (CS))
  q19 : Eqn
  q19 = wE 49 W
  q20 : Eqn
  q20 = eqn (ℓ "丵义") (ℓ "义丵") (low-comm ((S ↑ • CK₁₀)) (CS))
  q21 : Eqn
  q21 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q22 : Eqn
  q22 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))
  q23 : Eqn
  q23 = wE 1140 W
  q24 : Eqn
  q24 = eqn (ℓ "临义") (ℓ "义临") (low-comm (CK₁₀) (CS))
  q25 : Eqn
  q25 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q26 : Eqn
  q26 = wE 607 W
  q27 : Eqn
  q27 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q28 : Eqn
  q28 = wE 76 W
  q29 : Eqn
  q29 = wE 1170 W
  q30 : Eqn
  q30 = wE 29 W
  q31 : Eqn
  q31 = wE 1193 W
  q32 : Eqn
  q32 = wE 7 W
  q33 : Eqn
  q33 = wE 915 W
  q34 : Eqn
  q34 = wE 27 W
  q35 : Eqn
  q35 = wE 140 W
  q36 : Eqn
  q36 = wE 917 W
  q37 : Eqn
  q37 = wE 142 W
  q38 : Eqn
  q38 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q39 : Eqn
  q39 = wE 21 W
  q40 : Eqn
  q40 = eqn (ℓ "両乊") (ℓ "乊両") (low-comm ((CS • CS • CS)) ((CS • CS • CS)))
  q41 : Eqn
  q41 = wE 51 W
  q42 : Eqn
  q42 = eqn (ℓ "丵乊") (ℓ "乊丵") (low-comm ((S ↑ • CK₁₀)) ((CS • CS • CS)))
  q43 : Eqn
  q43 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q44 : Eqn
  q44 = wE 1142 W
  q45 : Eqn
  q45 = eqn (ℓ "临乊") (ℓ "乊临") (low-comm (CK₁₀) ((CS • CS • CS)))
  q46 : Eqn
  q46 = wE 609 W

-- groups [CK10 CS02 CK20 CSd02 CKd10 CS02 CKd20 CSd02] [CS12 CS13 CX23 CSd13 CX23]: 305 steps
lem-groups-CK10-CS02-CK20-CSd02-CKd10-CS02-CKd20-CSd02-vs-CS12-CS13-CX23-CSd13-CX23 : ⟪ (ℓ "临丧乄丨丵丧久丨丶丽乌举乌") ⟫ʷ ≈ ⟪ (ℓ "丶丽乌举乌临丧乄丨丵丧久丨") ⟫ʷ
lem-groups-CK10-CS02-CK20-CSd02-CKd10-CS02-CKd20-CSd02-vs-CS12-CS13-CX23-CSd13-CX23 = derive (ℓ "临丧乄丨丵丧久丨丶丽乌举乌") (ℓ "丶丽乌举乌临丧乄丨丵丧久丨")
  (rw 0 q16 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q1 ∷
   re 9 3 (ℓ "丮") ∷
   re 9 1 (ℓ "乏丼両丼乏") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "丽") ∷
   rw 12 q17 ∷
   rw 11 q18 ∷
   rw 10 q19 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q2 ∷
   re 10 5 (ℓ "丮") ∷
   re 10 1 (ℓ "乏丨乏") ∷
   rw 12 q2 ∷
   re 8 3 (ℓ "丽") ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q1 ∷
   re 8 3 (ℓ "乒") ∷
   re 8 1 (ℓ "乏丼丵丼乏") ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "丽") ∷
   rw 11 q17 ∷
   rw 10 q20 ∷
   rw 9 q19 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q2 ∷
   re 9 5 (ℓ "乒") ∷
   re 9 1 (ℓ "乏久乏") ∷
   rw 11 q2 ∷
   re 7 3 (ℓ "丽") ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q1 ∷
   re 7 3 (ℓ "中") ∷
   re 7 1 (ℓ "乏丼丠丼乏") ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "丽") ∷
   rw 10 q17 ∷
   rw 9 q21 ∷
   rw 8 q19 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q2 ∷
   re 8 5 (ℓ "中") ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q2 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q1 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 8 q2 ∷
   rw 5 q22 ∷
   rw 6 q23 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q22 ∷
   rw 7 q2 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q1 ∷
   re 5 3 (ℓ "丮") ∷
   re 5 1 (ℓ "乏丼両丼乏") ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "丽") ∷
   rw 8 q17 ∷
   rw 7 q18 ∷
   rw 6 q19 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q2 ∷
   re 6 5 (ℓ "丮") ∷
   re 6 1 (ℓ "乏丨乏") ∷
   rw 8 q2 ∷
   re 4 3 (ℓ "丽") ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q1 ∷
   re 4 3 (ℓ "乑") ∷
   re 4 1 (ℓ "乏丼临丼乏") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "丽") ∷
   rw 7 q17 ∷
   rw 6 q24 ∷
   rw 5 q19 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q2 ∷
   re 5 5 (ℓ "乑") ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw 7 q2 ∷
   re 3 3 (ℓ "丽") ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q1 ∷
   re 3 3 (ℓ "中") ∷
   re 3 1 (ℓ "乏丼丠丼乏") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "丽") ∷
   rw 6 q17 ∷
   rw 5 q21 ∷
   rw 4 q19 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q2 ∷
   re 4 5 (ℓ "中") ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q2 ∷
   re 2 3 (ℓ "丽") ∷
   rw 3 q1 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q2 ∷
   rw 1 q25 ∷
   rw 2 q26 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q25 ∷
   rw 3 q2 ∷
   rw 11 q4 ∷
   rw⁻ 10 q27 ∷
   rw 9 q28 ∷
   rw 10 q29 ∷
   rw 9 q27 ∷
   rw 10 q30 ∷
   rw 11 q10 ∷
   rw 10 q4 ∷
   rw⁻ 9 q27 ∷
   rw 8 q7 ∷
   rw 9 q31 ∷
   rw 8 q27 ∷
   rw 9 q9 ∷
   rw 10 q10 ∷
   rw 9 q4 ∷
   rw⁻ 8 q27 ∷
   rw 7 q32 ∷
   rw 8 q33 ∷
   rw 7 q27 ∷
   rw 8 q34 ∷
   rw 9 q10 ∷
   rw 6 q12 ∷
   rw 7 q4 ∷
   rw⁻ 6 q27 ∷
   rw 5 q28 ∷
   rw 6 q29 ∷
   rw 5 q27 ∷
   rw 6 q30 ∷
   rw 7 q10 ∷
   rw 6 q4 ∷
   rw⁻ 5 q27 ∷
   rw 4 q35 ∷
   rw 5 q36 ∷
   rw 4 q27 ∷
   rw 5 q37 ∷
   rw 6 q10 ∷
   rw 5 q4 ∷
   rw⁻ 4 q27 ∷
   rw 3 q32 ∷
   rw 4 q33 ∷
   rw 3 q27 ∷
   rw 4 q34 ∷
   rw 5 q10 ∷
   rw 2 q38 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q1 ∷
   re 11 3 (ℓ "丮") ∷
   re 11 1 (ℓ "乏丼両丼乏") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "举") ∷
   rw 14 q39 ∷
   rw 13 q40 ∷
   rw 12 q41 ∷
   re 12 1 (ℓ "乏丷乏") ∷
   rw 11 q2 ∷
   re 12 5 (ℓ "丮") ∷
   re 12 1 (ℓ "乏丨乏") ∷
   rw 14 q2 ∷
   re 10 3 (ℓ "举") ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q1 ∷
   re 10 3 (ℓ "乒") ∷
   re 10 1 (ℓ "乏丼丵丼乏") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "举") ∷
   rw 13 q39 ∷
   rw 12 q42 ∷
   rw 11 q41 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q2 ∷
   re 11 5 (ℓ "乒") ∷
   re 11 1 (ℓ "乏久乏") ∷
   rw 13 q2 ∷
   re 9 3 (ℓ "举") ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q1 ∷
   re 9 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "举") ∷
   rw 12 q39 ∷
   rw 11 q43 ∷
   rw 10 q41 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q2 ∷
   re 10 5 (ℓ "中") ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q2 ∷
   re 8 3 (ℓ "举") ∷
   rw 9 q1 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 10 q2 ∷
   rw 7 q22 ∷
   rw 8 q44 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q22 ∷
   rw 9 q2 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q1 ∷
   re 7 3 (ℓ "丮") ∷
   re 7 1 (ℓ "乏丼両丼乏") ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "举") ∷
   rw 10 q39 ∷
   rw 9 q40 ∷
   rw 8 q41 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q2 ∷
   re 8 5 (ℓ "丮") ∷
   re 8 1 (ℓ "乏丨乏") ∷
   rw 10 q2 ∷
   re 6 3 (ℓ "举") ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q1 ∷
   re 6 3 (ℓ "乑") ∷
   re 6 1 (ℓ "乏丼临丼乏") ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "举") ∷
   rw 9 q39 ∷
   rw 8 q45 ∷
   rw 7 q41 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q2 ∷
   re 7 5 (ℓ "乑") ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw 9 q2 ∷
   re 5 3 (ℓ "举") ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q1 ∷
   re 5 3 (ℓ "中") ∷
   re 5 1 (ℓ "乏丼丠丼乏") ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "举") ∷
   rw 8 q39 ∷
   rw 7 q43 ∷
   rw 6 q41 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q2 ∷
   re 6 5 (ℓ "中") ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q2 ∷
   re 4 3 (ℓ "举") ∷
   rw 5 q1 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q2 ∷
   rw 3 q25 ∷
   rw 4 q46 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q25 ∷
   rw 5 q2 ∷
   rw 13 q4 ∷
   rw⁻ 12 q27 ∷
   rw 11 q28 ∷
   rw 12 q29 ∷
   rw 11 q27 ∷
   rw 12 q30 ∷
   rw 13 q10 ∷
   rw 12 q4 ∷
   rw⁻ 11 q27 ∷
   rw 10 q7 ∷
   rw 11 q31 ∷
   rw 10 q27 ∷
   rw 11 q9 ∷
   rw 12 q10 ∷
   rw 11 q4 ∷
   rw⁻ 10 q27 ∷
   rw 9 q32 ∷
   rw 10 q33 ∷
   rw 9 q27 ∷
   rw 10 q34 ∷
   rw 11 q10 ∷
   rw 8 q12 ∷
   rw 9 q4 ∷
   rw⁻ 8 q27 ∷
   rw 7 q28 ∷
   rw 8 q29 ∷
   rw 7 q27 ∷
   rw 8 q30 ∷
   rw 9 q10 ∷
   rw 8 q4 ∷
   rw⁻ 7 q27 ∷
   rw 6 q35 ∷
   rw 7 q36 ∷
   rw 6 q27 ∷
   rw 7 q37 ∷
   rw 8 q10 ∷
   rw 7 q4 ∷
   rw⁻ 6 q27 ∷
   rw 5 q32 ∷
   rw 6 q33 ∷
   rw 5 q27 ∷
   rw 6 q34 ∷
   rw 7 q10 ∷
   rw 4 q38 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = eqn (ℓ "与乊") (ℓ "乊与") (low-comm ((S ↑)) ((CS • CS • CS)))
  q48 : Eqn
  q48 = wE 457 W
  q49 : Eqn
  q49 = wE 416 W
  q50 : Eqn
  q50 = wE 445 W
  q51 : Eqn
  q51 = wE 626 W

-- groups [CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 S1 S1 S1 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01] [CSd23]: 116 steps
lem-groups-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S1-S1-S1-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-vs-CSd23 : ⟪ (ℓ "丧丧丧乄且丧丧丧丧丧丧乆丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠乆丠丠丠临与丠丠丠丠丠丠乊") ⟫ʷ ≈ ⟪ (ℓ "乊丧丧丧乄且丧丧丧丧丧丧乆丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠乆丠丠丠临与丠丠丠丠丠丠") ⟫ʷ
lem-groups-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S1-S1-S1-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-vs-CSd23 = derive (ℓ "丧丧丧乄且丧丧丧丧丧丧乆丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠乆丠丠丠临与丠丠丠丠丠丠乊") (ℓ "乊丧丧丧乄且丧丧丧丧丧丧乆丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠与与与临与丠丠丠丠丠丠丠丠丠乆丠丠丠临与丠丠丠丠丠丠")
  (rw 55 q43 ∷
   rw 54 q43 ∷
   rw 53 q43 ∷
   rw 52 q43 ∷
   rw 51 q43 ∷
   rw 50 q43 ∷
   rw 49 q47 ∷
   rw 48 q45 ∷
   rw 47 q43 ∷
   rw 46 q43 ∷
   rw 45 q43 ∷
   rw 44 q48 ∷
   rw 43 q43 ∷
   rw 42 q43 ∷
   rw 41 q43 ∷
   rw 40 q43 ∷
   rw 39 q43 ∷
   rw 38 q43 ∷
   rw 37 q43 ∷
   rw 36 q43 ∷
   rw 35 q43 ∷
   rw 34 q47 ∷
   rw 33 q45 ∷
   rw 32 q47 ∷
   rw 31 q47 ∷
   rw 30 q47 ∷
   rw 29 q43 ∷
   rw 28 q43 ∷
   rw 27 q43 ∷
   rw 26 q43 ∷
   rw 25 q43 ∷
   rw 24 q43 ∷
   rw 23 q43 ∷
   rw 22 q43 ∷
   rw 21 q43 ∷
   rw 20 q43 ∷
   rw 19 q43 ∷
   rw 18 q43 ∷
   rw 17 q43 ∷
   rw 16 q43 ∷
   rw 15 q43 ∷
   rw 14 q43 ∷
   rw 13 q43 ∷
   rw 12 q43 ∷
   rw 11 q48 ∷
   rw 12 q4 ∷
   rw⁻ 11 q14 ∷
   rw 10 q32 ∷
   rw 11 q49 ∷
   rw 10 q14 ∷
   rw 11 q34 ∷
   rw 12 q10 ∷
   rw 11 q4 ∷
   rw⁻ 10 q14 ∷
   rw 9 q32 ∷
   rw 10 q49 ∷
   rw 9 q14 ∷
   rw 10 q34 ∷
   rw 11 q10 ∷
   rw 10 q4 ∷
   rw⁻ 9 q14 ∷
   rw 8 q32 ∷
   rw 9 q49 ∷
   rw 8 q14 ∷
   rw 9 q34 ∷
   rw 10 q10 ∷
   rw 9 q4 ∷
   rw⁻ 8 q14 ∷
   rw 7 q32 ∷
   rw 8 q49 ∷
   rw 7 q14 ∷
   rw 8 q34 ∷
   rw 9 q10 ∷
   rw 8 q4 ∷
   rw⁻ 7 q14 ∷
   rw 6 q32 ∷
   rw 7 q49 ∷
   rw 6 q14 ∷
   rw 7 q34 ∷
   rw 8 q10 ∷
   rw 7 q4 ∷
   rw⁻ 6 q14 ∷
   rw 5 q32 ∷
   rw 6 q49 ∷
   rw 5 q14 ∷
   rw 6 q34 ∷
   rw 7 q10 ∷
   rw 4 q50 ∷
   rw 5 q4 ∷
   rw⁻ 4 q14 ∷
   rw 3 q35 ∷
   rw 4 q51 ∷
   rw 3 q14 ∷
   rw 4 q37 ∷
   rw 5 q10 ∷
   rw 4 q4 ∷
   rw⁻ 3 q14 ∷
   rw 2 q32 ∷
   rw 3 q49 ∷
   rw 2 q14 ∷
   rw 3 q34 ∷
   rw 4 q10 ∷
   rw 3 q4 ∷
   rw⁻ 2 q14 ∷
   rw 1 q32 ∷
   rw 2 q49 ∷
   rw 1 q14 ∷
   rw 2 q34 ∷
   rw 3 q10 ∷
   rw 2 q4 ∷
   rw⁻ 1 q14 ∷
   rw 0 q32 ∷
   rw 1 q49 ∷
   rw 0 q14 ∷
   rw 1 q34 ∷
   rw 2 q10 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = wE 523 W
  q53 : Eqn
  q53 = wE 588 W
  q54 : Eqn
  q54 = wE 593 W

-- groups [CK30] [CS13 CS23 CX12 CSd23 CX12]: 59 steps
lem-groups-CK30-vs-CS13-CS23-CX12-CSd23-CX12 : ⟪ (ℓ "乑丽义丹乊丹") ⟫ʷ ≈ ⟪ (ℓ "丽义丹乊丹乑") ⟫ʷ
lem-groups-CK30-vs-CS13-CS23-CX12-CSd23-CX12 = derive (ℓ "乑丽义丹乊丹") (ℓ "丽义丹乊丹乑")
  (rw 2 q1 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q2 ∷
   re 0 1 (ℓ "乏乄乏") ∷
   rw 2 q2 ∷
   rw 1 q52 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "丽") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "乑") ∷
   rw 2 q2 ∷
   rw 3 q4 ∷
   rw⁻ 2 q5 ∷
   re 1 1 (ℓ "乏乄乏") ∷
   rw⁻ 3 q6 ∷
   rw 2 q35 ∷
   rw⁻ 1 q6 ∷
   re 2 3 (ℓ "乔") ∷
   rw 2 q53 ∷
   rw 1 q5 ∷
   re 3 1 (ℓ "乏乇乏") ∷
   rw 2 q6 ∷
   rw 3 q37 ∷
   rw 4 q6 ∷
   re 2 3 (ℓ "乑") ∷
   rw 3 q10 ∷
   re 2 1 (ℓ "乏丼临丼乏") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乀") ∷
   rw 5 q11 ∷
   rw 4 q38 ∷
   rw 3 q13 ∷
   re 3 1 (ℓ "乏丹乏") ∷
   rw 2 q2 ∷
   re 3 5 (ℓ "乑") ∷
   rw 5 q4 ∷
   rw⁻ 4 q14 ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw⁻ 5 q6 ∷
   rw 4 q35 ∷
   rw⁻ 3 q6 ∷
   re 4 3 (ℓ "乔") ∷
   rw 4 q54 ∷
   rw 3 q14 ∷
   re 5 1 (ℓ "乏乇乏") ∷
   rw 4 q6 ∷
   rw 5 q37 ∷
   rw 6 q6 ∷
   re 4 3 (ℓ "乑") ∷
   rw 5 q10 ∷
   re 4 1 (ℓ "乏丼临丼乏") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "乀") ∷
   rw 7 q11 ∷
   rw 6 q38 ∷
   rw 5 q13 ∷
   re 5 1 (ℓ "乏丹乏") ∷
   rw 4 q2 ∷
   re 5 5 (ℓ "乑") ∷ []) Eq.refl

-- groups [CK30] [CSd23]: 15 steps
lem-groups-CK30-vs-CSd23 : ⟪ (ℓ "乑乊") ⟫ʷ ≈ ⟪ (ℓ "乊乑") ⟫ʷ
lem-groups-CK30-vs-CSd23 = derive (ℓ "乑乊") (ℓ "乊乑")
  (rw 2 q4 ∷
   rw⁻ 1 q14 ∷
   re 0 1 (ℓ "乏乄乏") ∷
   rw⁻ 2 q6 ∷
   rw 1 q35 ∷
   rw⁻ 0 q6 ∷
   re 1 3 (ℓ "乔") ∷
   rw 1 q54 ∷
   rw 0 q14 ∷
   re 2 1 (ℓ "乏乇乏") ∷
   rw 1 q6 ∷
   rw 2 q37 ∷
   rw 3 q6 ∷
   re 1 3 (ℓ "乑") ∷
   rw 2 q10 ∷ []) Eq.refl
