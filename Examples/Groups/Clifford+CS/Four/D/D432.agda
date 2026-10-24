{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D432 (W : Ws) where

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
  q1 = wE 391 W
  q2 : Eqn
  q2 = wE 392 W

-- xconj [0] Gad(t=0, W=(), d=SK, e=-1): 2 steps
lem-xconj-0-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "丌丈上中九丮九下三丌") ⟫ʷ ≈ ⟪ (ℓ "三下丈丈中九丮九三三上丈") ⟫ʷ
lem-xconj-0-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ = derive (ℓ "丌丈上中九丮九下三丌") (ℓ "三下丈丈中九丮九三三上丈")
  (rw 0 q1 ∷
   rw 8 q2 ∷ []) Eq.refl

private
  q3 : Eqn
  q3 = wE 1161 W
  q4 : Eqn
  q4 = wE 1162 W
  q5 : Eqn
  q5 = wE 1 W
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = wE 464 W
  q8 : Eqn
  q8 = wE 1163 W

-- HD units: 10 steps
lem-HD-units : ⟪ (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") ⟫ʷ ≈ ⟪ (ℓ "丠临両乄丠丵両久乑乄丠临両久丠丵両乒") ⟫ʷ
lem-HD-units = derive (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") (ℓ "丠临両乄丠丵両久乑乄丠临両久丠丵両乒")
  (rw 0 q3 ∷
   rw 9 q4 ∷
   rw 19 q5 ∷
   re 18 1 (ℓ "乏乄乏") ∷
   rw 20 q6 ∷
   rw 17 q7 ∷
   rw 18 q8 ∷
   rw 19 q5 ∷
   re 17 3 (ℓ "乒") ∷
   rw 18 q6 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = wE 1164 W
  q10 : Eqn
  q10 = wE 1165 W

-- xconj [0] Gad(t=0, W=(), d=KKKK, e=-1): 2 steps
lem-xconj-0-Gad⟨t≡0-W≡⟨⟩-d≡KKKK-e≡-1⟩ : ⟪ (ℓ "丌上上上上中九丮九下下下下丌") ⟫ʷ ≈ ⟪ (ℓ "丈下丈丈下丈中九丮九三上三三上三") ⟫ʷ
lem-xconj-0-Gad⟨t≡0-W≡⟨⟩-d≡KKKK-e≡-1⟩ = derive (ℓ "丌上上上上中九丮九下下下下丌") (ℓ "丈下丈丈下丈中九丮九三上三三上三")
  (rw 0 q9 ∷
   rw 10 q10 ∷ []) Eq.refl

private
  q11 : Eqn
  q11 = wE 1112 W
  q12 : Eqn
  q12 = wE 1113 W

-- xconj [0] Gad(t=0, W=(), d=1, e=1): 2 steps
lem-xconj-0-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩ : ⟪ (ℓ "丌九中九丮丌") ⟫ʷ ≈ ⟪ (ℓ "上丈丈下九中九丮上三三下") ⟫ʷ
lem-xconj-0-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩ = derive (ℓ "丌九中九丮丌") (ℓ "上丈丈下九中九丮上三三下")
  (rw 0 q11 ∷
   rw 8 q12 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = wE 1166 W
  q14 : Eqn
  q14 = wE 1167 W

-- xconj [0] Gad(t=0, W=(), d=KSdKK, e=1): 2 steps
lem-xconj-0-Gad⟨t≡0-W≡⟨⟩-d≡KSdKK-e≡1⟩ : ⟪ (ℓ "丌上三上上九中九丮下下丈下丌") ⟫ʷ ≈ ⟪ (ℓ "三上三上九中九丮下丈下丈") ⟫ʷ
lem-xconj-0-Gad⟨t≡0-W≡⟨⟩-d≡KSdKK-e≡1⟩ = derive (ℓ "丌上三上上九中九丮下下丈下丌") (ℓ "三上三上九中九丮下丈下丈")
  (rw 0 q13 ∷
   rw 8 q14 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = wE 1168 W
  q16 : Eqn
  q16 = wE 1169 W
  q17 : Eqn
  q17 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q18 : Eqn
  q18 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q19 : Eqn
  q19 = wE 151 W
  q20 : Eqn
  q20 = eqn (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") (trans (by-assoc Eq.refl) (trans (ax lf) (by-assoc Eq.refl)))

-- HD X form: 109 steps
lem-HD-X-form : ⟪ (ℓ "乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨") ⟫ʷ ≈ ⟪ (ℓ "丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中") ⟫ʷ
lem-HD-X-form = derive (ℓ "乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨") (ℓ "丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中")
  (rw 0 q15 ∷
   rw 93 q5 ∷
   rw 94 q16 ∷
   rw⁻ 93 q17 ∷
   rw⁻ 94 q17 ∷
   rw⁻ 95 q18 ∷
   rw⁻ 96 q17 ∷
   rw⁻ 97 q18 ∷
   rw⁻ 98 q18 ∷
   rw 101 q5 ∷
   re 99 3 (ℓ "乀") ∷
   rw 102 q5 ∷
   re 100 3 (ℓ "乑") ∷
   rw 101 q19 ∷
   rw 104 q5 ∷
   re 102 3 (ℓ "乑") ∷
   rw 103 q19 ∷
   rw 106 q5 ∷
   re 104 3 (ℓ "中") ∷
   rw 107 q5 ∷
   re 105 3 (ℓ "中") ∷
   rw 108 q5 ∷
   re 106 3 (ℓ "中") ∷
   rw 109 q5 ∷
   re 107 3 (ℓ "乑") ∷
   rw 108 q19 ∷
   rw 111 q5 ∷
   re 109 3 (ℓ "中") ∷
   rw 112 q5 ∷
   re 110 3 (ℓ "中") ∷
   rw 113 q5 ∷
   re 111 3 (ℓ "中") ∷
   rw 114 q5 ∷
   re 112 3 (ℓ "中") ∷
   rw 115 q5 ∷
   re 113 3 (ℓ "中") ∷
   rw 116 q5 ∷
   re 114 3 (ℓ "中") ∷
   rw 117 q5 ∷
   re 115 3 (ℓ "乀") ∷
   rw 118 q5 ∷
   re 116 3 (ℓ "中") ∷
   rw 119 q5 ∷
   re 117 3 (ℓ "中") ∷
   rw 120 q5 ∷
   re 118 3 (ℓ "乑") ∷
   rw 121 q5 ∷
   re 119 3 (ℓ "中") ∷
   rw 122 q5 ∷
   re 120 3 (ℓ "乑") ∷
   rw 123 q5 ∷
   re 121 3 (ℓ "乑") ∷
   rw⁻ 122 q17 ∷
   rw⁻ 123 q17 ∷
   rw⁻ 124 q17 ∷
   rw⁻ 125 q18 ∷
   rw⁻ 126 q17 ∷
   rw⁻ 127 q17 ∷
   rw 130 q5 ∷
   re 128 3 (ℓ "乀") ∷
   rw 131 q5 ∷
   re 129 3 (ℓ "中") ∷
   rw 132 q5 ∷
   re 130 3 (ℓ "中") ∷
   rw 133 q5 ∷
   re 131 3 (ℓ "中") ∷
   rw 134 q5 ∷
   re 132 3 (ℓ "中") ∷
   rw 135 q5 ∷
   re 133 3 (ℓ "中") ∷
   rw 136 q5 ∷
   re 134 3 (ℓ "中") ∷
   rw 137 q5 ∷
   re 135 3 (ℓ "乑") ∷
   rw 136 q19 ∷
   rw 139 q5 ∷
   re 137 3 (ℓ "中") ∷
   rw 140 q5 ∷
   re 138 3 (ℓ "中") ∷
   rw 141 q5 ∷
   re 139 3 (ℓ "中") ∷
   rw 142 q5 ∷
   re 140 3 (ℓ "中") ∷
   rw 143 q5 ∷
   re 141 3 (ℓ "中") ∷
   rw 144 q5 ∷
   re 142 3 (ℓ "中") ∷
   rw 145 q5 ∷
   re 143 3 (ℓ "中") ∷
   rw 146 q5 ∷
   re 144 3 (ℓ "中") ∷
   rw 147 q5 ∷
   re 145 3 (ℓ "中") ∷
   rw 148 q5 ∷
   re 146 3 (ℓ "乀") ∷
   rw 149 q5 ∷
   re 147 3 (ℓ "中") ∷
   rw 150 q5 ∷
   re 148 3 (ℓ "中") ∷
   rw 151 q5 ∷
   re 149 3 (ℓ "中") ∷
   rw 152 q5 ∷
   re 150 3 (ℓ "乑") ∷
   rw 153 q5 ∷
   re 151 3 (ℓ "中") ∷
   rw 154 q5 ∷
   re 152 3 (ℓ "中") ∷
   rw 153 q6 ∷
   rw⁻ 31 q20 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = wE 352 W
  q22 : Eqn
  q22 = eqn (ℓ "両乍") (ℓ "乍両") (low-comm ((CS • CS • CS)) (CK₀₁))
  q23 : Eqn
  q23 = wE 357 W
  q24 : Eqn
  q24 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))
  q25 : Eqn
  q25 = wE 1138 W
  q26 : Eqn
  q26 = eqn (ℓ "丠乍") (ℓ "乍丠") (low-comm (CS) (CK₀₁))
  q27 : Eqn
  q27 = wE 599 W
  q28 : Eqn
  q28 = wE 1139 W
  q29 : Eqn
  q29 = wE 20 W
  q30 : Eqn
  q30 = eqn (ℓ "両义") (ℓ "义両") (low-comm ((CS • CS • CS)) (CS))
  q31 : Eqn
  q31 = wE 49 W
  q32 : Eqn
  q32 = wE 1140 W
  q33 : Eqn
  q33 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q34 : Eqn
  q34 = wE 607 W
  q35 : Eqn
  q35 = wE 5 W
  q36 : Eqn
  q36 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q37 : Eqn
  q37 = wE 76 W
  q38 : Eqn
  q38 = wE 1170 W
  q39 : Eqn
  q39 = wE 29 W
  q40 : Eqn
  q40 = wE 31 W
  q41 : Eqn
  q41 = eqn (ℓ "丵乌") (ℓ "乌丵") (low-comm ((S ↑ • CK₁₀)) (CX₀₁))
  q42 : Eqn
  q42 = wE 7 W
  q43 : Eqn
  q43 = wE 915 W
  q44 : Eqn
  q44 = wE 27 W
  q45 : Eqn
  q45 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q46 : Eqn
  q46 = wE 21 W
  q47 : Eqn
  q47 = eqn (ℓ "両乊") (ℓ "乊両") (low-comm ((CS • CS • CS)) ((CS • CS • CS)))
  q48 : Eqn
  q48 = wE 51 W
  q49 : Eqn
  q49 = wE 1142 W
  q50 : Eqn
  q50 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q51 : Eqn
  q51 = wE 609 W
  q52 : Eqn
  q52 = wE 353 W
  q53 : Eqn
  q53 = eqn (ℓ "両乎") (ℓ "乎両") (low-comm ((CS • CS • CS)) ((S • CK₀₁)))
  q54 : Eqn
  q54 = wE 358 W
  q55 : Eqn
  q55 = wE 1143 W
  q56 : Eqn
  q56 = eqn (ℓ "丠乎") (ℓ "乎丠") (low-comm (CS) ((S • CK₀₁)))
  q57 : Eqn
  q57 = wE 604 W

-- groups [CK10 CS02 CKd10 CSd02] [CK13 CS12 CS13 CX23 CSd13 CX23 CKd13]: 225 steps
lem-groups-CK10-CS02-CKd10-CSd02-vs-CK13-CS12-CS13-CX23-CSd13-CX23-CKd13 : ⟪ (ℓ "临丧丵丨乁丶丽乌举乌乂") ⟫ʷ ≈ ⟪ (ℓ "乁丶丽乌举乌乂临丧丵丨") ⟫ʷ
lem-groups-CK10-CS02-CKd10-CSd02-vs-CK13-CS12-CS13-CX23-CSd13-CX23-CKd13 = derive (ℓ "临丧丵丨乁丶丽乌举乌乂") (ℓ "乁丶丽乌举乌乂临丧丵丨")
  (re 4 1 (ℓ "乏为乏") ∷
   rw 3 q5 ∷
   re 4 3 (ℓ "丮") ∷
   re 4 1 (ℓ "乏丼両丼乏") ∷
   rw 10 q5 ∷
   re 8 3 (ℓ "乁") ∷
   rw 7 q21 ∷
   rw 6 q22 ∷
   rw 5 q23 ∷
   re 5 1 (ℓ "乏为乏") ∷
   rw 4 q6 ∷
   re 5 5 (ℓ "丮") ∷
   re 5 1 (ℓ "乏丨乏") ∷
   rw 7 q6 ∷
   re 3 3 (ℓ "乁") ∷
   rw 4 q5 ∷
   re 3 1 (ℓ "乏为乏") ∷
   rw 5 q6 ∷
   rw 2 q24 ∷
   rw 3 q25 ∷
   rw 4 q5 ∷
   re 2 3 (ℓ "乁") ∷
   rw⁻ 3 q24 ∷
   rw 4 q6 ∷
   re 2 1 (ℓ "乏为乏") ∷
   rw 1 q5 ∷
   re 2 3 (ℓ "中") ∷
   re 2 1 (ℓ "乏丼丠丼乏") ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "乁") ∷
   rw 5 q21 ∷
   rw 4 q26 ∷
   rw 3 q23 ∷
   re 3 1 (ℓ "乏为乏") ∷
   rw 2 q6 ∷
   re 3 5 (ℓ "中") ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q6 ∷
   re 1 3 (ℓ "乁") ∷
   rw 2 q5 ∷
   re 1 1 (ℓ "乏为乏") ∷
   rw 3 q6 ∷
   rw 0 q18 ∷
   rw 1 q27 ∷
   rw 2 q5 ∷
   re 0 3 (ℓ "乁") ∷
   rw⁻ 1 q18 ∷
   rw 2 q6 ∷
   rw 1 q28 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   re 6 3 (ℓ "丮") ∷
   re 6 1 (ℓ "乏丼両丼乏") ∷
   rw 12 q5 ∷
   re 10 3 (ℓ "丽") ∷
   rw 9 q29 ∷
   rw 8 q30 ∷
   rw 7 q31 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q6 ∷
   re 7 5 (ℓ "丮") ∷
   re 7 1 (ℓ "乏丨乏") ∷
   rw 9 q6 ∷
   re 5 3 (ℓ "丽") ∷
   rw 6 q5 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q6 ∷
   rw 4 q24 ∷
   rw 5 q32 ∷
   rw 6 q5 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q24 ∷
   rw 6 q6 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q5 ∷
   re 4 3 (ℓ "中") ∷
   re 4 1 (ℓ "乏丼丠丼乏") ∷
   rw 10 q5 ∷
   re 8 3 (ℓ "丽") ∷
   rw 7 q29 ∷
   rw 6 q33 ∷
   rw 5 q31 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q6 ∷
   re 5 5 (ℓ "中") ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q6 ∷
   re 3 3 (ℓ "丽") ∷
   rw 4 q5 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw 2 q18 ∷
   rw 3 q34 ∷
   rw 4 q5 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q18 ∷
   rw 4 q6 ∷
   rw 8 q35 ∷
   rw⁻ 7 q36 ∷
   rw 6 q37 ∷
   rw 7 q38 ∷
   rw 6 q36 ∷
   rw 7 q39 ∷
   rw 8 q40 ∷
   rw 5 q41 ∷
   rw 6 q35 ∷
   rw⁻ 5 q36 ∷
   rw 4 q42 ∷
   rw 5 q43 ∷
   rw 4 q36 ∷
   rw 5 q44 ∷
   rw 6 q40 ∷
   rw 3 q45 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q5 ∷
   re 8 3 (ℓ "丮") ∷
   re 8 1 (ℓ "乏丼両丼乏") ∷
   rw 14 q5 ∷
   re 12 3 (ℓ "举") ∷
   rw 11 q46 ∷
   rw 10 q47 ∷
   rw 9 q48 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q6 ∷
   re 9 5 (ℓ "丮") ∷
   re 9 1 (ℓ "乏丨乏") ∷
   rw 11 q6 ∷
   re 7 3 (ℓ "举") ∷
   rw 8 q5 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q6 ∷
   rw 6 q24 ∷
   rw 7 q49 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q24 ∷
   rw 8 q6 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q5 ∷
   re 6 3 (ℓ "中") ∷
   re 6 1 (ℓ "乏丼丠丼乏") ∷
   rw 12 q5 ∷
   re 10 3 (ℓ "举") ∷
   rw 9 q46 ∷
   rw 8 q50 ∷
   rw 7 q48 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q6 ∷
   re 7 5 (ℓ "中") ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q6 ∷
   re 5 3 (ℓ "举") ∷
   rw 6 q5 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q6 ∷
   rw 4 q18 ∷
   rw 5 q51 ∷
   rw 6 q5 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q18 ∷
   rw 6 q6 ∷
   rw 10 q35 ∷
   rw⁻ 9 q36 ∷
   rw 8 q37 ∷
   rw 9 q38 ∷
   rw 8 q36 ∷
   rw 9 q39 ∷
   rw 10 q40 ∷
   rw 7 q41 ∷
   rw 8 q35 ∷
   rw⁻ 7 q36 ∷
   rw 6 q42 ∷
   rw 7 q43 ∷
   rw 6 q36 ∷
   rw 7 q44 ∷
   rw 8 q40 ∷
   rw 5 q45 ∷
   re 10 1 (ℓ "乏主乏") ∷
   rw 9 q5 ∷
   re 10 3 (ℓ "丮") ∷
   re 10 1 (ℓ "乏丼両丼乏") ∷
   rw 16 q5 ∷
   re 14 3 (ℓ "乂") ∷
   rw 13 q52 ∷
   rw 12 q53 ∷
   rw 11 q54 ∷
   re 11 1 (ℓ "乏主乏") ∷
   rw 10 q6 ∷
   re 11 5 (ℓ "丮") ∷
   re 11 1 (ℓ "乏丨乏") ∷
   rw 13 q6 ∷
   re 9 3 (ℓ "乂") ∷
   rw 10 q5 ∷
   re 9 1 (ℓ "乏主乏") ∷
   rw 11 q6 ∷
   rw 8 q24 ∷
   rw 9 q55 ∷
   rw 10 q5 ∷
   re 8 3 (ℓ "乂") ∷
   rw⁻ 9 q24 ∷
   rw 10 q6 ∷
   re 8 1 (ℓ "乏主乏") ∷
   rw 7 q5 ∷
   re 8 3 (ℓ "中") ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 14 q5 ∷
   re 12 3 (ℓ "乂") ∷
   rw 11 q52 ∷
   rw 10 q56 ∷
   rw 9 q54 ∷
   re 9 1 (ℓ "乏主乏") ∷
   rw 8 q6 ∷
   re 9 5 (ℓ "中") ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q6 ∷
   re 7 3 (ℓ "乂") ∷
   rw 8 q5 ∷
   re 7 1 (ℓ "乏主乏") ∷
   rw 9 q6 ∷
   rw 6 q18 ∷
   rw 7 q57 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "乂") ∷
   rw⁻ 7 q18 ∷
   rw 8 q6 ∷ []) Eq.refl
