{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D144 (W : Ws) where

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
  q2 = wE 21 W
  q3 : Eqn
  q3 = eqn (ℓ "丳乊") (ℓ "乊丳") (low-comm (CX₁₀) ((CS • CS • CS)))
  q4 : Eqn
  q4 = wE 51 W
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = eqn (ℓ "乃丛") (ℓ "丛乃") (low₃-comm ((Swap ↑ • CX₁₀ • Swap ↑)) ((S • S • S)))
  q7 : Eqn
  q7 = wE 360 W
  q8 : Eqn
  q8 = eqn (ℓ "丳乘") (ℓ "乘丳") (low-comm (CX₁₀) ((S ↑ • CK₁₀)))
  q9 : Eqn
  q9 = wE 362 W
  q10 : Eqn
  q10 = wE 690 W
  q11 : Eqn
  q11 = eqn (ℓ "两丘") (ℓ "丘两") (low-comm (CK₀₁) (X))
  q12 : Eqn
  q12 = eqn (ℓ "两乌") (ℓ "乌两") (low-comm (CK₀₁) (CX₀₁))
  q13 : Eqn
  q13 = eqn (ℓ "丠丘") (ℓ "丘丠") (low-comm (CS) (X))
  q14 : Eqn
  q14 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q15 : Eqn
  q15 = wE 5 W
  q16 : Eqn
  q16 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q17 : Eqn
  q17 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q18 : Eqn
  q18 = wE 6 W
  q19 : Eqn
  q19 = wE 612 W
  q20 : Eqn
  q20 = wE 39 W
  q21 : Eqn
  q21 = wE 31 W
  q22 : Eqn
  q22 = eqn (ℓ "丈丘") (ℓ "丘丈") (low₁-comm (S) ((X ↑)))
  q23 : Eqn
  q23 = eqn (ℓ "丈乌") (ℓ "乌丈") (low₁-comm (S) ((CX₀₁ ↑)))
  q24 : Eqn
  q24 = wE 613 W
  q25 : Eqn
  q25 = wE 543 W
  q26 : Eqn
  q26 = wE 545 W

-- Bar(['S', 'S', 'K', 'S', 'K', 'K'];2,0->1) passes white iX via V2 conjugates 3 part3: 206 steps
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part3 : ⟪ (ℓ "丘乊丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘丶丶乇丶乇乇举举乏乏丼丳丼乏丷乏举举举丛乕举举举两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丘乌丘丘丷么丷丷丘丘丷丷丷丘") ⟫ʷ ≈ ⟪ (ℓ "丘乊丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丷丷丷丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两") ⟫ʷ
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part3 = derive (ℓ "丘乊丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘丶丶乇丶乇乇举举乏乏丼丳丼乏丷乏举举举丛乕举举举两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丘乌丘丘丷么丷丷丘丘丷丷丷丘") (ℓ "丘乊丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丷丷丷丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两")
  (rw 57 q1 ∷
   re 55 3 (ℓ "举") ∷
   rw 54 q2 ∷
   rw 53 q3 ∷
   rw 52 q4 ∷
   re 52 1 (ℓ "乏丷乏") ∷
   rw 51 q5 ∷
   re 52 5 (ℓ "乐") ∷
   re 52 1 (ℓ "乏乃乏") ∷
   rw 54 q5 ∷
   re 50 3 (ℓ "举") ∷
   re 52 1 (ℓ "乏丷乏") ∷
   rw 51 q1 ∷
   re 52 3 (ℓ "乐") ∷
   re 52 1 (ℓ "乏丼丳丼乏") ∷
   rw 58 q1 ∷
   re 56 3 (ℓ "举") ∷
   rw 55 q2 ∷
   rw 54 q3 ∷
   rw 53 q4 ∷
   re 53 1 (ℓ "乏丷乏") ∷
   rw 52 q5 ∷
   re 53 5 (ℓ "乐") ∷
   re 53 1 (ℓ "乏乃乏") ∷
   rw 55 q5 ∷
   re 51 3 (ℓ "举") ∷
   re 53 1 (ℓ "乏丷乏") ∷
   rw 52 q1 ∷
   re 53 3 (ℓ "乐") ∷
   re 53 1 (ℓ "乏丼丳丼乏") ∷
   rw 59 q1 ∷
   re 57 3 (ℓ "举") ∷
   rw 56 q2 ∷
   rw 55 q3 ∷
   rw 54 q4 ∷
   re 54 1 (ℓ "乏丷乏") ∷
   rw 53 q5 ∷
   re 54 5 (ℓ "乐") ∷
   re 54 1 (ℓ "乏乃乏") ∷
   rw 56 q5 ∷
   re 52 3 (ℓ "举") ∷
   re 54 1 (ℓ "乏丷乏") ∷
   rw 53 q1 ∷
   re 54 3 (ℓ "乐") ∷
   re 54 1 (ℓ "乏丼丳丼乏") ∷
   rw 60 q1 ∷
   re 58 3 (ℓ "举") ∷
   rw 57 q2 ∷
   rw 56 q3 ∷
   rw 55 q4 ∷
   re 55 1 (ℓ "乏丷乏") ∷
   rw 54 q5 ∷
   re 55 5 (ℓ "乐") ∷
   re 55 1 (ℓ "乏乃乏") ∷
   rw 57 q5 ∷
   re 53 3 (ℓ "举") ∷
   rw 54 q6 ∷
   re 56 1 (ℓ "乏么乏") ∷
   rw 55 q1 ∷
   re 56 3 (ℓ "乐") ∷
   re 56 1 (ℓ "乏丼丳丼乏") ∷
   rw 62 q1 ∷
   re 60 3 (ℓ "乕") ∷
   rw 59 q7 ∷
   rw 58 q8 ∷
   rw 57 q9 ∷
   re 57 1 (ℓ "乏么乏") ∷
   rw 56 q5 ∷
   re 57 5 (ℓ "乐") ∷
   re 57 1 (ℓ "乏乃乏") ∷
   rw 59 q5 ∷
   re 55 3 (ℓ "乕") ∷
   re 57 1 (ℓ "乏丷乏") ∷
   rw 56 q1 ∷
   re 57 3 (ℓ "乐") ∷
   re 57 1 (ℓ "乏丼丳丼乏") ∷
   rw 63 q1 ∷
   re 61 3 (ℓ "举") ∷
   rw 60 q2 ∷
   rw 59 q3 ∷
   rw 58 q4 ∷
   re 58 1 (ℓ "乏丷乏") ∷
   rw 57 q5 ∷
   re 58 5 (ℓ "乐") ∷
   re 58 1 (ℓ "乏乃乏") ∷
   rw 60 q5 ∷
   re 56 3 (ℓ "举") ∷
   re 58 1 (ℓ "乏丷乏") ∷
   rw 57 q1 ∷
   re 58 3 (ℓ "乐") ∷
   re 58 1 (ℓ "乏丼丳丼乏") ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "举") ∷
   rw 61 q2 ∷
   rw 60 q3 ∷
   rw 59 q4 ∷
   re 59 1 (ℓ "乏丷乏") ∷
   rw 58 q5 ∷
   re 59 5 (ℓ "乐") ∷
   re 59 1 (ℓ "乏乃乏") ∷
   rw 61 q5 ∷
   re 57 3 (ℓ "举") ∷
   re 59 1 (ℓ "乏丷乏") ∷
   rw 58 q1 ∷
   re 59 3 (ℓ "乐") ∷
   re 59 1 (ℓ "乏丼丳丼乏") ∷
   rw 65 q1 ∷
   re 63 3 (ℓ "举") ∷
   rw 62 q2 ∷
   rw 61 q3 ∷
   rw 60 q4 ∷
   re 60 1 (ℓ "乏丷乏") ∷
   rw 59 q5 ∷
   re 60 5 (ℓ "乐") ∷
   re 60 1 (ℓ "乏乃乏") ∷
   rw 62 q5 ∷
   re 58 3 (ℓ "举") ∷
   rw 42 q10 ∷
   rw 81 q11 ∷
   rw 82 q12 ∷
   rw 83 q11 ∷
   rw 80 q11 ∷
   rw 81 q12 ∷
   rw 82 q11 ∷
   rw 79 q13 ∷
   rw 80 q14 ∷
   rw 81 q13 ∷
   rw 78 q11 ∷
   rw 79 q12 ∷
   rw 80 q11 ∷
   rw 77 q13 ∷
   rw 78 q14 ∷
   rw 79 q13 ∷
   rw 76 q13 ∷
   rw 77 q14 ∷
   rw 78 q13 ∷
   rw 79 q15 ∷
   rw⁻ 78 q16 ∷
   rw⁻ 77 q17 ∷
   rw⁻ 76 q16 ∷
   rw 75 q18 ∷
   rw 76 q19 ∷
   rw 75 q16 ∷
   rw 76 q17 ∷
   rw 77 q16 ∷
   rw 78 q20 ∷
   rw 79 q21 ∷
   rw 74 q13 ∷
   rw 75 q14 ∷
   rw 76 q13 ∷
   rw 73 q13 ∷
   rw 74 q14 ∷
   rw 75 q13 ∷
   rw 72 q13 ∷
   rw 73 q14 ∷
   rw 74 q13 ∷
   rw 71 q13 ∷
   rw 72 q14 ∷
   rw 73 q13 ∷
   rw 70 q13 ∷
   rw 71 q14 ∷
   rw 72 q13 ∷
   rw 69 q13 ∷
   rw 70 q14 ∷
   rw 71 q13 ∷
   rw 68 q22 ∷
   rw 69 q23 ∷
   rw 70 q22 ∷
   rw 67 q11 ∷
   rw 68 q12 ∷
   rw 69 q11 ∷
   rw 66 q13 ∷
   rw 67 q14 ∷
   rw 68 q13 ∷
   rw 65 q13 ∷
   rw 66 q14 ∷
   rw 67 q13 ∷
   rw 64 q13 ∷
   rw 65 q14 ∷
   rw 66 q13 ∷
   rw 63 q22 ∷
   rw 64 q23 ∷
   rw 65 q22 ∷
   rw 62 q11 ∷
   rw 63 q12 ∷
   rw 64 q11 ∷
   rw 61 q22 ∷
   rw 62 q23 ∷
   rw 63 q22 ∷
   rw 60 q11 ∷
   rw 61 q12 ∷
   rw 62 q11 ∷
   rw 63 q15 ∷
   rw⁻ 62 q16 ∷
   rw⁻ 61 q17 ∷
   rw⁻ 60 q16 ∷
   rw 59 q18 ∷
   rw 60 q19 ∷
   rw 59 q16 ∷
   rw 60 q17 ∷
   rw 61 q16 ∷
   rw 62 q20 ∷
   rw 63 q21 ∷
   rw 53 q24 ∷
   rw 56 q25 ∷
   rw 62 q26 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = wE 707 W
  q28 : Eqn
  q28 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q29 : Eqn
  q29 = wE 74 W
  q30 : Eqn
  q30 = wE 708 W
  q31 : Eqn
  q31 = wE 30 W
  q32 : Eqn
  q32 = wE 359 W
  q33 : Eqn
  q33 = eqn (ℓ "丣乗") (ℓ "乗丣") (low-comm (CX₀₁) (CK₁₀))
  q34 : Eqn
  q34 = wE 361 W
  q35 : Eqn
  q35 = wE 709 W
  q36 : Eqn
  q36 = wE 710 W
  q37 : Eqn
  q37 = wE 497 W
  q38 : Eqn
  q38 = wE 711 W

-- groups [CK23 CS02 CS23 CX03 CSd23 CX03 CKd23] [X2 CK21 X2]: 83 steps
lem-groups-CK23-CS02-CS23-CX03-CSd23-CX03-CKd23-vs-X2-CK21-X2 : ⟪ (ℓ "乍丧义丰乊丰乎丘乇丘") ⟫ʷ ≈ ⟪ (ℓ "丘乇丘乍丧义丰乊丰乎") ⟫ʷ
lem-groups-CK23-CS02-CS23-CX03-CSd23-CX03-CKd23-vs-X2-CK21-X2 = derive (ℓ "乍丧义丰乊丰乎丘乇丘") (ℓ "丘乇丘乍丧义丰乊丰乎")
  (rw 6 q27 ∷
   rw 7 q15 ∷
   rw⁻ 6 q16 ∷
   re 5 1 (ℓ "乏个乏") ∷
   rw⁻ 7 q28 ∷
   rw 6 q29 ∷
   rw⁻ 5 q28 ∷
   re 6 3 (ℓ "乀") ∷
   rw 6 q30 ∷
   rw 5 q16 ∷
   re 7 1 (ℓ "乏丹乏") ∷
   rw 6 q28 ∷
   rw 7 q31 ∷
   rw 8 q28 ∷
   re 6 3 (ℓ "丰") ∷
   rw 7 q21 ∷
   re 6 1 (ℓ "乏丼丣丼乏") ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "乔") ∷
   rw 9 q32 ∷
   rw 8 q33 ∷
   rw 7 q34 ∷
   re 7 1 (ℓ "乏乇乏") ∷
   rw 6 q5 ∷
   re 7 5 (ℓ "丰") ∷
   rw 9 q15 ∷
   rw⁻ 8 q16 ∷
   re 7 1 (ℓ "乏个乏") ∷
   rw⁻ 9 q28 ∷
   rw 8 q29 ∷
   rw⁻ 7 q28 ∷
   re 8 3 (ℓ "乀") ∷
   rw 8 q30 ∷
   rw 7 q16 ∷
   re 9 1 (ℓ "乏丹乏") ∷
   rw 8 q28 ∷
   rw 9 q31 ∷
   rw 10 q28 ∷
   re 8 3 (ℓ "丰") ∷
   rw 9 q21 ∷
   rw 4 q35 ∷
   rw 5 q15 ∷
   rw⁻ 4 q16 ∷
   re 3 1 (ℓ "乏个乏") ∷
   rw⁻ 5 q28 ∷
   rw 4 q29 ∷
   rw⁻ 3 q28 ∷
   re 4 3 (ℓ "乀") ∷
   rw 4 q30 ∷
   rw 3 q16 ∷
   re 5 1 (ℓ "乏丹乏") ∷
   rw 4 q28 ∷
   rw 5 q31 ∷
   rw 6 q28 ∷
   re 4 3 (ℓ "丰") ∷
   rw 5 q21 ∷
   re 4 1 (ℓ "乏丼丣丼乏") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "乔") ∷
   rw 7 q32 ∷
   rw 6 q33 ∷
   rw 5 q34 ∷
   re 5 1 (ℓ "乏乇乏") ∷
   rw 4 q5 ∷
   re 5 5 (ℓ "丰") ∷
   rw 7 q15 ∷
   rw⁻ 6 q16 ∷
   re 5 1 (ℓ "乏个乏") ∷
   rw⁻ 7 q28 ∷
   rw 6 q29 ∷
   rw⁻ 5 q28 ∷
   re 6 3 (ℓ "乀") ∷
   rw 6 q30 ∷
   rw 5 q16 ∷
   re 7 1 (ℓ "乏丹乏") ∷
   rw 6 q28 ∷
   rw 7 q31 ∷
   rw 8 q28 ∷
   re 6 3 (ℓ "丰") ∷
   rw 7 q21 ∷
   rw 2 q36 ∷
   rw 1 q37 ∷
   rw 0 q38 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = eqn (ℓ "並乍") (ℓ "乍並") (low-comm (Swap) (CK₀₁))
  q40 : Eqn
  q40 = eqn (ℓ "並东") (ℓ "东並") (low-comm (Swap) ((K ↑)))
  q41 : Eqn
  q41 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q42 : Eqn
  q42 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q43 : Eqn
  q43 = wE 27 W
  q44 : Eqn
  q44 = wE 122 W
  q45 : Eqn
  q45 = wE 127 W
  q46 : Eqn
  q46 = wE 7 W
  q47 : Eqn
  q47 = wE 337 W
  q48 : Eqn
  q48 = wE 712 W
  q49 : Eqn
  q49 = wE 24 W
  q50 : Eqn
  q50 = wE 25 W
  q51 : Eqn
  q51 = wE 124 W

-- groups [TOFF302] [X2 CK23 X2]: 67 steps
lem-groups-TOFF302-vs-X2-CK23-X2 : ⟪ (ℓ "乧丘乍丘") ⟫ʷ ≈ ⟪ (ℓ "丘乍丘乧") ⟫ʷ
lem-groups-TOFF302-vs-X2-CK23-X2 = derive (ℓ "乧丘乍丘") (ℓ "丘乍丘乧")
  (rw 4 q15 ∷
   rw⁻ 3 q16 ∷
   rw⁻ 2 q39 ∷
   rw⁻ 1 q16 ∷
   re 0 1 (ℓ "並乨並") ∷
   re 1 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 0 q40 ∷
   rw 1 q41 ∷
   rw 2 q31 ∷
   rw 3 q42 ∷
   rw 4 q31 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q28 ∷
   rw 6 q43 ∷
   rw 7 q28 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q40 ∷
   rw 7 q44 ∷
   rw 8 q21 ∷
   rw 7 q45 ∷
   rw⁻ 6 q40 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q28 ∷
   rw 6 q46 ∷
   rw⁻ 5 q28 ∷
   re 6 3 (ℓ "丽") ∷
   rw 4 q29 ∷
   rw⁻ 3 q42 ∷
   rw 2 q29 ∷
   rw⁻ 1 q41 ∷
   rw⁻ 0 q40 ∷
   rw 1 q47 ∷
   re 1 8 (ℓ "乨") ∷
   rw 1 q48 ∷
   rw 0 q16 ∷
   rw 1 q39 ∷
   rw 2 q16 ∷
   re 4 1 (ℓ "东义丹乊丹丽东丁") ∷
   rw 3 q40 ∷
   rw 4 q41 ∷
   rw 5 q31 ∷
   rw 6 q42 ∷
   rw 7 q31 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q28 ∷
   rw 9 q43 ∷
   rw 10 q28 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q40 ∷
   rw 10 q44 ∷
   rw 3 q15 ∷
   rw 4 q40 ∷
   rw 5 q41 ∷
   rw 6 q49 ∷
   rw 7 q42 ∷
   rw 8 q49 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q28 ∷
   rw 10 q50 ∷
   rw 11 q28 ∷
   re 9 3 (ℓ "丽") ∷
   rw 10 q40 ∷
   rw 11 q51 ∷
   rw 4 q47 ∷
   re 4 8 (ℓ "乨") ∷
   re 3 3 (ℓ "乧") ∷
   rw 4 q21 ∷ []) Eq.refl
