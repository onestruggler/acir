{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D408 (W : Ws) where

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
  q1 = wE 140 W
  q2 : Eqn
  q2 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = wE 1144 W
  q4 : Eqn
  q4 = wE 27 W
  q5 : Eqn
  q5 = wE 142 W
  q6 : Eqn
  q6 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q7 : Eqn
  q7 = wE 31 W
  q8 : Eqn
  q8 = wE 36 W
  q9 : Eqn
  q9 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q10 : Eqn
  q10 = wE 37 W
  q11 : Eqn
  q11 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q12 : Eqn
  q12 = wE 764 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20] part2: 105 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-part2 : ⟪ (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丠丠临丠临临乀乏乄並乏业乔业丽丽丽乔业丽丽丽丽丽丽丶丶乇丶乇乇並乀中中乑中乑乑") ⟫ʷ ≈ ⟪ (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-part2 = derive (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丠丠临丠临临乀乏乄並乏业乔业丽丽丽乔业丽丽丽丽丽丽丶丶乇丶乇乇並乀中中乑中乑乑") (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑")
  (rw 31 q1 ∷
   rw⁻ 30 q2 ∷
   re 31 3 (ℓ "乔") ∷
   rw 31 q3 ∷
   rw 30 q4 ∷
   rw 31 q4 ∷
   rw 32 q5 ∷
   rw 33 q4 ∷
   rw 34 q5 ∷
   rw 35 q5 ∷
   re 37 1 (ℓ "乏乇乏") ∷
   rw 36 q2 ∷
   rw 37 q5 ∷
   rw 38 q2 ∷
   re 36 3 (ℓ "乑") ∷
   rw 37 q6 ∷
   re 39 1 (ℓ "乏乇乏") ∷
   rw 38 q2 ∷
   rw 39 q5 ∷
   rw 40 q2 ∷
   re 38 3 (ℓ "乑") ∷
   rw 39 q6 ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q2 ∷
   rw 41 q4 ∷
   rw 42 q2 ∷
   re 40 3 (ℓ "中") ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 41 q2 ∷
   rw 42 q4 ∷
   rw 43 q2 ∷
   re 41 3 (ℓ "中") ∷
   re 43 1 (ℓ "乏丶乏") ∷
   rw 42 q2 ∷
   rw 43 q4 ∷
   rw 44 q2 ∷
   re 42 3 (ℓ "中") ∷
   re 44 1 (ℓ "乏乇乏") ∷
   rw 43 q2 ∷
   rw 44 q5 ∷
   rw 45 q2 ∷
   re 43 3 (ℓ "乑") ∷
   rw 44 q6 ∷
   re 46 1 (ℓ "乏丶乏") ∷
   rw 45 q2 ∷
   rw 46 q4 ∷
   rw 47 q2 ∷
   re 45 3 (ℓ "中") ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 46 q2 ∷
   rw 47 q4 ∷
   rw 48 q2 ∷
   re 46 3 (ℓ "中") ∷
   re 48 1 (ℓ "乏丶乏") ∷
   rw 47 q2 ∷
   rw 48 q4 ∷
   rw 49 q2 ∷
   re 47 3 (ℓ "中") ∷
   re 49 1 (ℓ "乏丶乏") ∷
   rw 48 q2 ∷
   rw 49 q4 ∷
   rw 50 q2 ∷
   re 48 3 (ℓ "中") ∷
   re 50 1 (ℓ "乏丶乏") ∷
   rw 49 q2 ∷
   rw 50 q4 ∷
   rw 51 q2 ∷
   re 49 3 (ℓ "中") ∷
   re 51 1 (ℓ "乏丶乏") ∷
   rw 50 q2 ∷
   rw 51 q4 ∷
   rw 52 q2 ∷
   re 50 3 (ℓ "中") ∷
   rw 51 q7 ∷
   re 30 1 (ℓ "丼丠丼") ∷
   rw 29 q8 ∷
   rw⁻ 30 q9 ∷
   rw 31 q10 ∷
   re 29 3 (ℓ "丧") ∷
   re 31 1 (ℓ "丼丠丼") ∷
   rw 30 q8 ∷
   rw⁻ 31 q9 ∷
   rw 32 q10 ∷
   re 30 3 (ℓ "丧") ∷
   re 32 1 (ℓ "丼临丼") ∷
   rw 31 q8 ∷
   rw⁻ 32 q11 ∷
   rw 33 q10 ∷
   re 31 3 (ℓ "乄") ∷
   re 33 1 (ℓ "丼丠丼") ∷
   rw 32 q8 ∷
   rw⁻ 33 q9 ∷
   rw 34 q10 ∷
   re 32 3 (ℓ "丧") ∷
   re 34 1 (ℓ "丼临丼") ∷
   rw 33 q8 ∷
   rw⁻ 34 q11 ∷
   rw 35 q10 ∷
   re 33 3 (ℓ "乄") ∷
   re 35 1 (ℓ "丼临丼") ∷
   rw 34 q8 ∷
   rw⁻ 35 q11 ∷
   rw 36 q10 ∷
   re 34 3 (ℓ "乄") ∷
   rw 23 q12 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = eqn (ℓ "丈丞") (ℓ "丞丈") (low₁-comm (S) ((X ↑ ↑)))
  q14 : Eqn
  q14 = eqn (ℓ "上丞") (ℓ "丞上") (low₁-comm (K) ((X ↑ ↑)))
  q15 : Eqn
  q15 = wE 391 W
  q16 : Eqn
  q16 = eqn (ℓ "下丞") (ℓ "丞下") (low₁-comm ((K • iI)) ((X ↑ ↑)))
  q17 : Eqn
  q17 = eqn (ℓ "三丞") (ℓ "丞三") (low₁-comm ((S • S • S)) ((X ↑ ↑)))
  q18 : Eqn
  q18 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q19 : Eqn
  q19 = wE 392 W

-- xconj [0] Gad(t=0, W=(3,), d=SK, e=-1): 9 steps
lem-xconj-0-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "丌丞丈上中九丮九下三丞丌") ⟫ʷ ≈ ⟪ (ℓ "丞三下丈丈中九丮九三三上丈丞") ⟫ʷ
lem-xconj-0-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩ = derive (ℓ "丌丞丈上中九丮九下三丞丌") (ℓ "丞三下丈丈中九丮九三三上丈丞")
  (rw⁻ 1 q13 ∷
   rw⁻ 2 q14 ∷
   rw 0 q15 ∷
   rw 3 q13 ∷
   rw 2 q13 ∷
   rw 1 q16 ∷
   rw 0 q17 ∷
   rw⁻ 11 q18 ∷
   rw 9 q19 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = wE 1145 W
  q21 : Eqn
  q21 = wE 1146 W

-- xconj [0] Gad(t=0, W=(3,), d=SdKdSS, e=-1): 9 steps
lem-xconj-0-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "丌丞三下丈丈中九丮九三三上丈丞丌") ⟫ʷ ≈ ⟪ (ℓ "丞丈上中九丮九下三丞") ⟫ʷ
lem-xconj-0-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "丌丞三下丈丈中九丮九三三上丈丞丌") (ℓ "丞丈上中九丮九下三丞")
  (rw⁻ 1 q17 ∷
   rw⁻ 2 q16 ∷
   rw⁻ 3 q13 ∷
   rw⁻ 4 q13 ∷
   rw 0 q20 ∷
   rw 1 q14 ∷
   rw 0 q13 ∷
   rw⁻ 11 q18 ∷
   rw 7 q21 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = eqn (ℓ "丈丘") (ℓ "丘丈") (low₁-comm (S) ((X ↑)))
  q23 : Eqn
  q23 = eqn (ℓ "上丘") (ℓ "丘上") (low₁-comm (K) ((X ↑)))
  q24 : Eqn
  q24 = eqn (ℓ "下丘") (ℓ "丘下") (low₁-comm ((K • iI)) ((X ↑)))
  q25 : Eqn
  q25 = eqn (ℓ "三丘") (ℓ "丘三") (low₁-comm ((S • S • S)) ((X ↑)))
  q26 : Eqn
  q26 = eqn (ℓ "丌丘") (ℓ "丘丌") (low₁-comm (X) ((X ↑)))

-- xconj [0] Gad(t=0, W=(2,), d=SK, e=-1): 9 steps
lem-xconj-0-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "丌丘丈上中九丮九下三丘丌") ⟫ʷ ≈ ⟪ (ℓ "丘三下丈丈中九丮九三三上丈丘") ⟫ʷ
lem-xconj-0-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩ = derive (ℓ "丌丘丈上中九丮九下三丘丌") (ℓ "丘三下丈丈中九丮九三三上丈丘")
  (rw⁻ 1 q22 ∷
   rw⁻ 2 q23 ∷
   rw 0 q15 ∷
   rw 3 q22 ∷
   rw 2 q22 ∷
   rw 1 q24 ∷
   rw 0 q25 ∷
   rw⁻ 11 q26 ∷
   rw 9 q19 ∷ []) Eq.refl

-- xconj [0] Gad(t=0, W=(2,), d=SdKdSS, e=-1): 9 steps
lem-xconj-0-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "丌丘三下丈丈中九丮九三三上丈丘丌") ⟫ʷ ≈ ⟪ (ℓ "丘丈上中九丮九下三丘") ⟫ʷ
lem-xconj-0-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "丌丘三下丈丈中九丮九三三上丈丘丌") (ℓ "丘丈上中九丮九下三丘")
  (rw⁻ 1 q25 ∷
   rw⁻ 2 q24 ∷
   rw⁻ 3 q22 ∷
   rw⁻ 4 q22 ∷
   rw 0 q20 ∷
   rw 1 q23 ∷
   rw 0 q22 ∷
   rw⁻ 11 q26 ∷
   rw 7 q21 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = wE 5 W
  q28 : Eqn
  q28 = wE 121 W
  q29 : Eqn
  q29 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q30 : Eqn
  q30 = wE 30 W
  q31 : Eqn
  q31 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q32 : Eqn
  q32 = wE 122 W
  q33 : Eqn
  q33 = wE 127 W
  q34 : Eqn
  q34 = wE 118 W
  q35 : Eqn
  q35 = wE 7 W
  q36 : Eqn
  q36 = wE 74 W
  q37 : Eqn
  q37 = wE 125 W
  q38 : Eqn
  q38 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q39 : Eqn
  q39 = eqn (ℓ "並乎") (ℓ "乎並") (low-comm (Swap) ((S • CK₀₁)))
  q40 : Eqn
  q40 = wE 1030 W
  q41 : Eqn
  q41 = wE 123 W
  q42 : Eqn
  q42 = wE 24 W
  q43 : Eqn
  q43 = wE 25 W
  q44 : Eqn
  q44 = wE 124 W

-- pass [X2 CKd23 X2] [TOFF023]: 67 steps
lem-pass-X2-CKd23-X2-vs-TOFF023 : ⟪ (ℓ "丘乎丘也") ⟫ʷ ≈ ⟪ (ℓ "也丘乎丘") ⟫ʷ
lem-pass-X2-CKd23-X2-vs-TOFF023 = derive (ℓ "丘乎丘也") (ℓ "也丘乎丘")
  (rw 4 q27 ∷
   re 3 1 (ℓ "並乢並") ∷
   re 4 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 3 q28 ∷
   rw 4 q29 ∷
   rw 5 q30 ∷
   rw 6 q31 ∷
   rw 7 q30 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q2 ∷
   rw 9 q4 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q28 ∷
   rw 10 q32 ∷
   rw 11 q7 ∷
   rw 10 q33 ∷
   rw 9 q34 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q2 ∷
   rw 9 q35 ∷
   rw⁻ 8 q2 ∷
   re 9 3 (ℓ "丽") ∷
   rw 7 q36 ∷
   rw⁻ 6 q31 ∷
   rw 5 q36 ∷
   rw⁻ 4 q29 ∷
   rw 3 q34 ∷
   rw 4 q37 ∷
   re 4 8 (ℓ "乢") ∷
   rw⁻ 2 q38 ∷
   rw⁻ 1 q39 ∷
   rw⁻ 0 q38 ∷
   rw 1 q40 ∷
   re 1 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 0 q28 ∷
   rw 1 q29 ∷
   rw 2 q30 ∷
   rw 3 q31 ∷
   rw 4 q30 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q2 ∷
   rw 6 q4 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q28 ∷
   rw 7 q32 ∷
   rw 0 q27 ∷
   rw 1 q41 ∷
   rw 2 q29 ∷
   rw 3 q42 ∷
   rw 4 q31 ∷
   rw 5 q42 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q2 ∷
   rw 7 q43 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q41 ∷
   rw 8 q44 ∷
   rw 1 q37 ∷
   re 1 8 (ℓ "乢") ∷
   re 0 3 (ℓ "也") ∷
   rw 1 q38 ∷
   rw 2 q39 ∷
   rw 3 q38 ∷
   rw 4 q7 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = eqn (ℓ "並乍") (ℓ "乍並") (low-comm (Swap) (CK₀₁))
  q46 : Eqn
  q46 = wE 1020 W

-- pass [X2 CK23 X2] [TOFF023]: 67 steps
lem-pass-X2-CK23-X2-vs-TOFF023 : ⟪ (ℓ "丘乍丘也") ⟫ʷ ≈ ⟪ (ℓ "也丘乍丘") ⟫ʷ
lem-pass-X2-CK23-X2-vs-TOFF023 = derive (ℓ "丘乍丘也") (ℓ "也丘乍丘")
  (rw 4 q27 ∷
   re 3 1 (ℓ "並乢並") ∷
   re 4 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 3 q28 ∷
   rw 4 q29 ∷
   rw 5 q30 ∷
   rw 6 q31 ∷
   rw 7 q30 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q2 ∷
   rw 9 q4 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q28 ∷
   rw 10 q32 ∷
   rw 11 q7 ∷
   rw 10 q33 ∷
   rw 9 q34 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q2 ∷
   rw 9 q35 ∷
   rw⁻ 8 q2 ∷
   re 9 3 (ℓ "丽") ∷
   rw 7 q36 ∷
   rw⁻ 6 q31 ∷
   rw 5 q36 ∷
   rw⁻ 4 q29 ∷
   rw 3 q34 ∷
   rw 4 q37 ∷
   re 4 8 (ℓ "乢") ∷
   rw⁻ 2 q38 ∷
   rw⁻ 1 q45 ∷
   rw⁻ 0 q38 ∷
   rw 1 q46 ∷
   re 1 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 0 q28 ∷
   rw 1 q29 ∷
   rw 2 q30 ∷
   rw 3 q31 ∷
   rw 4 q30 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q2 ∷
   rw 6 q4 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q28 ∷
   rw 7 q32 ∷
   rw 0 q27 ∷
   rw 1 q41 ∷
   rw 2 q29 ∷
   rw 3 q42 ∷
   rw 4 q31 ∷
   rw 5 q42 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q2 ∷
   rw 7 q43 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q41 ∷
   rw 8 q44 ∷
   rw 1 q37 ∷
   re 1 8 (ℓ "乢") ∷
   re 0 3 (ℓ "也") ∷
   rw 1 q38 ∷
   rw 2 q45 ∷
   rw 3 q38 ∷
   rw 4 q7 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = wE 76 W
  q48 : Eqn
  q48 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q49 : Eqn
  q49 = wE 1147 W
  q50 : Eqn
  q50 = wE 29 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X2 CSd02 X2]: 247 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd02-X2 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘丨丘") ⟫ʷ ≈ ⟪ (ℓ "丘丨丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd02-X2 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘丨丘") (ℓ "丘丨丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 34 q27 ∷
   rw⁻ 33 q38 ∷
   rw 32 q47 ∷
   rw⁻ 31 q38 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q2 ∷
   rw 31 q35 ∷
   rw⁻ 30 q2 ∷
   re 31 3 (ℓ "丽") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q2 ∷
   rw 30 q35 ∷
   rw⁻ 29 q2 ∷
   re 30 3 (ℓ "丽") ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw⁻ 30 q2 ∷
   rw 29 q1 ∷
   rw⁻ 28 q2 ∷
   re 29 3 (ℓ "乔") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q2 ∷
   rw 28 q35 ∷
   rw⁻ 27 q2 ∷
   re 28 3 (ℓ "丽") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q2 ∷
   rw 27 q35 ∷
   rw⁻ 26 q2 ∷
   re 27 3 (ℓ "丽") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q2 ∷
   rw 26 q35 ∷
   rw⁻ 25 q2 ∷
   re 26 3 (ℓ "丽") ∷
   rw⁻ 24 q48 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q2 ∷
   rw 24 q35 ∷
   rw⁻ 23 q2 ∷
   re 24 3 (ℓ "丽") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw⁻ 24 q2 ∷
   rw 23 q35 ∷
   rw⁻ 22 q2 ∷
   re 23 3 (ℓ "丽") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q2 ∷
   rw 22 q35 ∷
   rw⁻ 21 q2 ∷
   re 22 3 (ℓ "丽") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q2 ∷
   rw 21 q35 ∷
   rw⁻ 20 q2 ∷
   re 21 3 (ℓ "丽") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q2 ∷
   rw 20 q35 ∷
   rw⁻ 19 q2 ∷
   re 20 3 (ℓ "丽") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q2 ∷
   rw 19 q35 ∷
   rw⁻ 18 q2 ∷
   re 19 3 (ℓ "丽") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q2 ∷
   rw 18 q35 ∷
   rw⁻ 17 q2 ∷
   re 18 3 (ℓ "丽") ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q2 ∷
   rw 17 q35 ∷
   rw⁻ 16 q2 ∷
   re 17 3 (ℓ "丽") ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw⁻ 17 q2 ∷
   rw 16 q35 ∷
   rw⁻ 15 q2 ∷
   re 16 3 (ℓ "丽") ∷
   rw⁻ 14 q6 ∷
   re 13 1 (ℓ "乏乄乏") ∷
   rw⁻ 15 q2 ∷
   rw 14 q1 ∷
   rw⁻ 13 q2 ∷
   re 14 3 (ℓ "乔") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q2 ∷
   rw 13 q35 ∷
   rw⁻ 12 q2 ∷
   re 13 3 (ℓ "丽") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q2 ∷
   rw 12 q35 ∷
   rw⁻ 11 q2 ∷
   re 12 3 (ℓ "丽") ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q2 ∷
   rw 11 q35 ∷
   rw⁻ 10 q2 ∷
   re 11 3 (ℓ "丽") ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q2 ∷
   rw 10 q35 ∷
   rw⁻ 9 q2 ∷
   re 10 3 (ℓ "丽") ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q2 ∷
   rw 9 q35 ∷
   rw⁻ 8 q2 ∷
   re 9 3 (ℓ "丽") ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw⁻ 9 q2 ∷
   rw 8 q35 ∷
   rw⁻ 7 q2 ∷
   re 8 3 (ℓ "丽") ∷
   rw⁻ 6 q48 ∷
   rw 5 q35 ∷
   rw 4 q35 ∷
   rw 3 q1 ∷
   rw 2 q35 ∷
   rw 1 q35 ∷
   rw 0 q35 ∷
   rw 1 q49 ∷
   rw 0 q38 ∷
   rw 1 q50 ∷
   rw 2 q38 ∷
   rw 3 q4 ∷
   rw 4 q4 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   rw 8 q4 ∷
   rw 9 q48 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q2 ∷
   rw 11 q4 ∷
   rw 12 q2 ∷
   re 10 3 (ℓ "中") ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q2 ∷
   rw 12 q4 ∷
   rw 13 q2 ∷
   re 11 3 (ℓ "中") ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q2 ∷
   rw 13 q4 ∷
   rw 14 q2 ∷
   re 12 3 (ℓ "中") ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q2 ∷
   rw 14 q4 ∷
   rw 15 q2 ∷
   re 13 3 (ℓ "中") ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q2 ∷
   rw 15 q4 ∷
   rw 16 q2 ∷
   re 14 3 (ℓ "中") ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q2 ∷
   rw 16 q4 ∷
   rw 17 q2 ∷
   re 15 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏乇乏") ∷
   rw 16 q2 ∷
   rw 17 q5 ∷
   rw 18 q2 ∷
   re 16 3 (ℓ "乑") ∷
   rw 17 q6 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q2 ∷
   rw 19 q4 ∷
   rw 20 q2 ∷
   re 18 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q2 ∷
   rw 20 q4 ∷
   rw 21 q2 ∷
   re 19 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q2 ∷
   rw 21 q4 ∷
   rw 22 q2 ∷
   re 20 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q2 ∷
   rw 22 q4 ∷
   rw 23 q2 ∷
   re 21 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q2 ∷
   rw 23 q4 ∷
   rw 24 q2 ∷
   re 22 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q2 ∷
   rw 24 q4 ∷
   rw 25 q2 ∷
   re 23 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q2 ∷
   rw 25 q4 ∷
   rw 26 q2 ∷
   re 24 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q2 ∷
   rw 26 q4 ∷
   rw 27 q2 ∷
   re 25 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q2 ∷
   rw 27 q4 ∷
   rw 28 q2 ∷
   re 26 3 (ℓ "中") ∷
   rw 27 q48 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q2 ∷
   rw 29 q4 ∷
   rw 30 q2 ∷
   re 28 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q2 ∷
   rw 30 q4 ∷
   rw 31 q2 ∷
   re 29 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q2 ∷
   rw 31 q4 ∷
   rw 32 q2 ∷
   re 30 3 (ℓ "中") ∷
   re 32 1 (ℓ "乏乇乏") ∷
   rw 31 q2 ∷
   rw 32 q5 ∷
   rw 33 q2 ∷
   re 31 3 (ℓ "乑") ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q2 ∷
   rw 33 q4 ∷
   rw 34 q2 ∷
   re 32 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q2 ∷
   rw 34 q4 ∷
   rw 35 q2 ∷
   re 33 3 (ℓ "中") ∷
   rw 34 q7 ∷ []) Eq.refl
