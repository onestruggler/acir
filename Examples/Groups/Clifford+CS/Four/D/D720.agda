{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD720 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D720 (W : Ws) (Sᴰ : SD720) where

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
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-CCZ123-vs-X3-CK30-X3 : St 2109
  lem-pass-CCZ123-vs-X3-CK30-X3 = pickᴰ 0 Sᴰ
  lem-pass-CCZ123-vs-X3-CKd30-X3 : St 2110
  lem-pass-CCZ123-vs-X3-CKd30-X3 = pickᴰ 1 Sᴰ
  lem-pass-CCZ123-vs-X3-CS03-X3 : St 2111
  lem-pass-CCZ123-vs-X3-CS03-X3 = pickᴰ 2 Sᴰ
  lem-pass-CCZ123-vs-X3-CSd03-X3 : St 2112
  lem-pass-CCZ123-vs-X3-CSd03-X3 = pickᴰ 3 Sᴰ
  lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 840
  lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 4 Sᴰ
  lem-pass-X2-CK23-X2-vs-CS01-TOFF123-CSd01-TOFF123 : St 2113
  lem-pass-X2-CK23-X2-vs-CS01-TOFF123-CSd01-TOFF123 = pickᴰ 5 Sᴰ
  lem-pass-X2-CKd23-X2-vs-CS01-TOFF123-CSd01-TOFF123 : St 2114
  lem-pass-X2-CKd23-X2-vs-CS01-TOFF123-CSd01-TOFF123 = pickᴰ 6 Sᴰ
  lem-pass-X2-CS23-X2-vs-CS01-TOFF123-CSd01-TOFF123 : St 2115
  lem-pass-X2-CS23-X2-vs-CS01-TOFF123-CSd01-TOFF123 = pickᴰ 7 Sᴰ
  lem-pass-X2-CSd23-X2-vs-CS01-TOFF123-CSd01-TOFF123 : St 2116
  lem-pass-X2-CSd23-X2-vs-CS01-TOFF123-CSd01-TOFF123 = pickᴰ 8 Sᴰ
  lem-pass-X3-CK31-X3-vs-CS02-TOFF213-CSd02-TOFF213 : St 2117
  lem-pass-X3-CK31-X3-vs-CS02-TOFF213-CSd02-TOFF213 = pickᴰ 9 Sᴰ
  lem-pass-X3-CK32-X3-vs-CS01-TOFF123-CSd01-TOFF123 : St 2118
  lem-pass-X3-CK32-X3-vs-CS01-TOFF123-CSd01-TOFF123 = pickᴰ 10 Sᴰ
  lem-pass-X3-CKd31-X3-vs-CS02-TOFF213-CSd02-TOFF213 : St 2119
  lem-pass-X3-CKd31-X3-vs-CS02-TOFF213-CSd02-TOFF213 = pickᴰ 11 Sᴰ
  lem-pass-X3-CKd32-X3-vs-CS01-TOFF123-CSd01-TOFF123 : St 2120
  lem-pass-X3-CKd32-X3-vs-CS01-TOFF123-CSd01-TOFF123 = pickᴰ 12 Sᴰ
  lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 1146
  lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 13 Sᴰ
  lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2038
  lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 14 Sᴰ
  lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 2049
  lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 15 Sᴰ
  lem-S2-at1023-ᵖ-1 : St 2083
  lem-S2-at1023-ᵖ-1 = pickᴰ 16 Sᴰ
  lem-S2-at1203-ᵖ-1 : St 2084
  lem-S2-at1203-ᵖ-1 = pickᴰ 17 Sᴰ
  lem-S2-at2013-ᵖ-1 : St 2085
  lem-S2-at2013-ᵖ-1 = pickᴰ 18 Sᴰ
  lem-S2-at2103-ᵖ-1 : St 2086
  lem-S2-at2103-ᵖ-1 = pickᴰ 19 Sᴰ
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 : St 2121
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 = pickᴰ 20 Sᴰ
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 : St 2122
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 = pickᴰ 21 Sᴰ
  lem-pass-CCZ123-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : St 2123
  lem-pass-CCZ123-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = pickᴰ 22 Sᴰ
  lem-pass-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3-vs-CCZ123 : St 2124
  lem-pass-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3-vs-CCZ123 = pickᴰ 23 Sᴰ
  lem-pass-X1-CK13-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 2125
  lem-pass-X1-CK13-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 24 Sᴰ
  lem-pass-X1-CKd13-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 2126
  lem-pass-X1-CKd13-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 25 Sᴰ
  lem-pass-X1-CS13-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 2127
  lem-pass-X1-CS13-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 26 Sᴰ
  lem-pass-X1-CSd13-X1-vs-CS03-TOFF012-CSd03-TOFF012 : St 2128
  lem-pass-X1-CSd13-X1-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 27 Sᴰ
  lem-pass-X3-CS13-TOFF102-CSd13-TOFF102-X3-vs-CCZ123 : St 2129
  lem-pass-X3-CS13-TOFF102-CSd13-TOFF102-X3-vs-CCZ123 = pickᴰ 28 Sᴰ
  lem-pass-X3-CS23-TOFF201-CSd23-TOFF201-X3-vs-CCZ123 : St 2130
  lem-pass-X3-CS23-TOFF201-CSd23-TOFF201-X3-vs-CCZ123 = pickᴰ 29 Sᴰ

private
  q1 : Eqn
  q1 = wE 1660 W
  q2 : Eqn
  q2 = sE 2121 lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2
  q3 : Eqn
  q3 = wE 1661 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X0 X1 X2 CS12 CS12 CK21 CS12 CK21 CK21 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX20 CS01 CS01 CK01 CS01 CK01 CK01 X0 X1 X2]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丌丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丌丒丘") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丌丒丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丌丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丌丒丘") (ℓ "丌丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丌丒丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 29 q1 ∷
   rw 0 q2 ∷
   rw 0 q3 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = sE 2122 lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X0 X1 X2 CS12 CS12 CK21 CS12 CK21 CK21 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX20 CS01 CS01 CK01 CS01 CK01 CK01 X0 X1 X2]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丌丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丌丒丘") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丌丒丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X0-X1-X2 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丌丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丌丒丘") (ℓ "丌丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丌丒丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 31 q1 ∷
   rw 0 q4 ∷
   rw 0 q3 ∷ []) Eq.refl

private
  q5 : Eqn
  q5 = wE 1 W
  q6 : Eqn
  q6 = eqn (ℓ "三乏") (ℓ "乏三") (low₁-comm ((S • S • S)) ((Swap ↑)))
  q7 : Eqn
  q7 = wE 173 W
  q8 : Eqn
  q8 = wE 3 W
  q9 : Eqn
  q9 = wE 2059 W
  q10 : Eqn
  q10 = wE 175 W
  q11 : Eqn
  q11 = sE 2049 lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q12 : Eqn
  q12 = sE 1146 lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q13 : Eqn
  q13 = sE 2038 lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q14 : Eqn
  q14 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q15 : Eqn
  q15 = wE 2060 W

-- pass [X3 CKd30 X3] [Sd0 CS03 TOFF012 CSd03 TOFF012 S0]: 45 steps
lem-pass-X3-CKd30-X3-vs-Sd0-CS03-TOFF012-CSd03-TOFF012-S0 : ⟪ (ℓ "丞乒丞三中九丮九丈") ⟫ʷ ≈ ⟪ (ℓ "三中九丮九丈丞乒丞") ⟫ʷ
lem-pass-X3-CKd30-X3-vs-Sd0-CS03-TOFF012-CSd03-TOFF012-S0 = derive (ℓ "丞乒丞三中九丮九丈") (ℓ "三中九丮九丈丞乒丞")
  (rw 4 q5 ∷
   rw 3 q6 ∷
   rw 2 q7 ∷
   re 1 1 (ℓ "乏久乏") ∷
   rw 3 q8 ∷
   rw 0 q7 ∷
   rw 1 q9 ∷
   rw⁻ 0 q6 ∷
   rw 1 q10 ∷
   rw 4 q5 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q10 ∷
   rw 4 q10 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "乒") ∷
   rw 6 q10 ∷
   rw 7 q10 ∷
   rw 10 q5 ∷
   re 8 3 (ℓ "丮") ∷
   rw 9 q10 ∷
   rw 10 q8 ∷
   rw 7 q11 ∷
   rw 4 q12 ∷
   rw 1 q13 ∷
   rw 15 q5 ∷
   rw 14 q14 ∷
   rw 13 q7 ∷
   re 12 1 (ℓ "乏丨乏") ∷
   rw 14 q8 ∷
   rw 11 q7 ∷
   rw 10 q7 ∷
   re 9 1 (ℓ "乏久乏") ∷
   rw 11 q8 ∷
   rw 8 q7 ∷
   rw 7 q7 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q8 ∷
   rw 5 q7 ∷
   rw 6 q15 ∷
   rw⁻ 5 q14 ∷
   rw 6 q10 ∷
   rw 9 q5 ∷
   re 7 3 (ℓ "乒") ∷
   rw 8 q10 ∷
   rw 9 q8 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = sE 2111 lem-pass-CCZ123-vs-X3-CS03-X3
  q17 : Eqn
  q17 = sE 2109 lem-pass-CCZ123-vs-X3-CK30-X3
  q18 : Eqn
  q18 = sE 2123 lem-pass-CCZ123-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3
  q19 : Eqn
  q19 = sE 2110 lem-pass-CCZ123-vs-X3-CKd30-X3
  q20 : Eqn
  q20 = sE 2112 lem-pass-CCZ123-vs-X3-CSd03-X3

-- CCZ(3,1,2) passes split Gad(t=0, W=(3,), d=SK, e=-1): 5 steps
lem-CCZ⟨312⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "乜丞中丞丞乑丞丞中九丮九丞丞乒丞丞丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞中丞丞乑丞丞中九丮九丞丞乒丞丞丮丞乜") ⟫ʷ
lem-CCZ⟨312⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SK-e≡-1⟩ = derive (ℓ "乜丞中丞丞乑丞丞中九丮九丞丞乒丞丞丮丞") (ℓ "丞中丞丞乑丞丞中九丮九丞丞乒丞丞丮丞乜")
  (rw 0 q16 ∷
   rw 3 q17 ∷
   rw 6 q18 ∷
   rw 12 q19 ∷
   rw 15 q20 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = eqn (ℓ "下乏") (ℓ "乏下") (low₁-comm ((K • iI)) ((Swap ↑)))
  q22 : Eqn
  q22 = wE 2061 W
  q23 : Eqn
  q23 = sE 840 lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q24 : Eqn
  q24 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q25 : Eqn
  q25 = wE 2062 W

-- pass [X3 CSd30 X3] [Kd0 CS03 TOFF012 CSd03 TOFF012 K0]: 45 steps
lem-pass-X3-CSd30-X3-vs-Kd0-CS03-TOFF012-CSd03-TOFF012-K0 : ⟪ (ℓ "丞丮丞下中九丮九上") ⟫ʷ ≈ ⟪ (ℓ "下中九丮九上丞丮丞") ⟫ʷ
lem-pass-X3-CSd30-X3-vs-Kd0-CS03-TOFF012-CSd03-TOFF012-K0 = derive (ℓ "丞丮丞下中九丮九上") (ℓ "下中九丮九上丞丮丞")
  (rw 4 q5 ∷
   rw 3 q21 ∷
   rw 2 q7 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw 3 q8 ∷
   rw 0 q7 ∷
   rw 1 q22 ∷
   rw⁻ 0 q21 ∷
   rw 1 q10 ∷
   rw 4 q5 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q10 ∷
   rw 4 q10 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "乑") ∷
   rw 6 q10 ∷
   rw 7 q10 ∷
   rw 10 q5 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q10 ∷
   rw 10 q8 ∷
   rw 7 q13 ∷
   rw 4 q23 ∷
   rw 1 q13 ∷
   rw 15 q5 ∷
   rw 14 q24 ∷
   rw 13 q7 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q8 ∷
   rw 11 q7 ∷
   rw 10 q7 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw 11 q8 ∷
   rw 8 q7 ∷
   rw 7 q7 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q8 ∷
   rw 5 q7 ∷
   rw 6 q25 ∷
   rw⁻ 5 q24 ∷
   rw 6 q10 ∷
   rw 9 q5 ∷
   re 7 3 (ℓ "丮") ∷
   rw 8 q10 ∷
   rw 9 q8 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = sE 2083 lem-S2-at1023-ᵖ-1
  q27 : Eqn
  q27 = wE 225 W
  q28 : Eqn
  q28 = eqn (ℓ "丶丞") (ℓ "丞丶") (low₃-comm ((CS ↑)) (X))
  q29 : Eqn
  q29 = wE 390 W
  q30 : Eqn
  q30 = eqn (ℓ "丷丞") (ℓ "丞丷") (low₃-comm (((CS • CS • CS) ↑)) (X))

-- distribute Gad(t=1, W=(3,), d=1, e=-1) CS12 TOFF103 CSd12 TOFF103: 8 steps
lem-distribute-Gad⟨t≡1-W≡⟨3⟩-d≡1-e≡-1⟩-CS12-TOFF103-CSd12-TOFF103 : ⟪ (ℓ "丞丽习举习丞") ⟫ʷ ≈ ⟪ (ℓ "丶丞乡丞丷丞乡丞") ⟫ʷ
lem-distribute-Gad⟨t≡1-W≡⟨3⟩-d≡1-e≡-1⟩-CS12-TOFF103-CSd12-TOFF103 = derive (ℓ "丞丽习举习丞") (ℓ "丶丞乡丞丷丞乡丞")
  (rw 1 q26 ∷
   rw 2 q27 ∷
   rw 5 q27 ∷
   rw 8 q27 ∷
   rw⁻ 0 q28 ∷
   rw 1 q29 ∷
   rw⁻ 4 q30 ∷
   rw 5 q29 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = sE 2084 lem-S2-at1203-ᵖ-1
  q32 : Eqn
  q32 = sE 2120 lem-pass-X3-CKd32-X3-vs-CS01-TOFF123-CSd01-TOFF123
  q33 : Eqn
  q33 = sE 2084 lem-S2-at1203-ᵖ-1

-- pass [X3 CKd32 X3] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X3-CKd32-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丞乘丞丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丞乘丞") ⟫ʷ
lem-pass-X3-CKd32-X3-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丞乘丞丽习举习") (ℓ "丽习举习丞乘丞")
  (rw 3 q31 ∷
   rw 0 q32 ∷
   rw⁻ 0 q33 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = sE 2129 lem-pass-X3-CS13-TOFF102-CSd13-TOFF102-X3-vs-CCZ123

-- pass [CCZ123] [X3 CS13 TOFF102 CSd13 TOFF102 X3]: 1 steps
lem-pass-CCZ123-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : ⟪ (ℓ "乜丞丽习举习丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽习举习丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = derive (ℓ "乜丞丽习举习丞") (ℓ "丞丽习举习丞乜")
  (rw⁻ 0 q34 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = sE 2118 lem-pass-X3-CK32-X3-vs-CS01-TOFF123-CSd01-TOFF123

-- pass [X3 CK32 X3] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X3-CK32-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丞乗丞丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丞乗丞") ⟫ʷ
lem-pass-X3-CK32-X3-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丞乗丞丽习举习") (ℓ "丽习举习丞乗丞")
  (rw 3 q31 ∷
   rw 0 q35 ∷
   rw⁻ 0 q33 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = sE 2115 lem-pass-X2-CS23-X2-vs-CS01-TOFF123-CSd01-TOFF123

-- pass [X2 CS23 X2] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X2-CS23-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丘义丘丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丘义丘") ⟫ʷ
lem-pass-X2-CS23-X2-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丘义丘丽习举习") (ℓ "丽习举习丘义丘")
  (rw 3 q31 ∷
   rw 0 q36 ∷
   rw⁻ 0 q33 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = sE 2113 lem-pass-X2-CK23-X2-vs-CS01-TOFF123-CSd01-TOFF123

-- pass [X2 CK23 X2] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X2-CK23-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丘乍丘丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丘乍丘") ⟫ʷ
lem-pass-X2-CK23-X2-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丘乍丘丽习举习") (ℓ "丽习举习丘乍丘")
  (rw 3 q31 ∷
   rw 0 q37 ∷
   rw⁻ 0 q33 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = sE 2116 lem-pass-X2-CSd23-X2-vs-CS01-TOFF123-CSd01-TOFF123

-- pass [X2 CSd23 X2] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X2-CSd23-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丘乊丘丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丘乊丘") ⟫ʷ
lem-pass-X2-CSd23-X2-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丘乊丘丽习举习") (ℓ "丽习举习丘乊丘")
  (rw 3 q31 ∷
   rw 0 q38 ∷
   rw⁻ 0 q33 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = sE 2114 lem-pass-X2-CKd23-X2-vs-CS01-TOFF123-CSd01-TOFF123

-- pass [X2 CKd23 X2] [CS13 TOFF102 CSd13 TOFF102]: 3 steps
lem-pass-X2-CKd23-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丘乎丘丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丘乎丘") ⟫ʷ
lem-pass-X2-CKd23-X2-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丘乎丘丽习举习") (ℓ "丽习举习丘乎丘")
  (rw 3 q31 ∷
   rw 0 q39 ∷
   rw⁻ 0 q33 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = sE 2085 lem-S2-at2013-ᵖ-1

-- distribute Gad(t=2, W=(3,), d=1, e=-1) CS12 TOFF203 CSd12 TOFF203: 8 steps
lem-distribute-Gad⟨t≡2-W≡⟨3⟩-d≡1-e≡-1⟩-CS12-TOFF203-CSd12-TOFF203 : ⟪ (ℓ "丞义乣乊乣丞") ⟫ʷ ≈ ⟪ (ℓ "丶丞乤丞丷丞乤丞") ⟫ʷ
lem-distribute-Gad⟨t≡2-W≡⟨3⟩-d≡1-e≡-1⟩-CS12-TOFF203-CSd12-TOFF203 = derive (ℓ "丞义乣乊乣丞") (ℓ "丶丞乤丞丷丞乤丞")
  (rw 1 q40 ∷
   rw 2 q27 ∷
   rw 5 q27 ∷
   rw 8 q27 ∷
   rw⁻ 0 q28 ∷
   rw 1 q29 ∷
   rw⁻ 4 q30 ∷
   rw 5 q29 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = sE 2086 lem-S2-at2103-ᵖ-1
  q42 : Eqn
  q42 = sE 2119 lem-pass-X3-CKd31-X3-vs-CS02-TOFF213-CSd02-TOFF213
  q43 : Eqn
  q43 = sE 2086 lem-S2-at2103-ᵖ-1

-- pass [X3 CKd31 X3] [CS23 TOFF201 CSd23 TOFF201]: 3 steps
lem-pass-X3-CKd31-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (ℓ "丞乕丞义乣乊乣") ⟫ʷ ≈ ⟪ (ℓ "义乣乊乣丞乕丞") ⟫ʷ
lem-pass-X3-CKd31-X3-vs-CS23-TOFF201-CSd23-TOFF201 = derive (ℓ "丞乕丞义乣乊乣") (ℓ "义乣乊乣丞乕丞")
  (rw 3 q41 ∷
   rw 0 q42 ∷
   rw⁻ 0 q43 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = sE 2130 lem-pass-X3-CS23-TOFF201-CSd23-TOFF201-X3-vs-CCZ123

-- pass [CCZ123] [X3 CS23 TOFF201 CSd23 TOFF201 X3]: 1 steps
lem-pass-CCZ123-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 : ⟪ (ℓ "乜丞义乣乊乣丞") ⟫ʷ ≈ ⟪ (ℓ "丞义乣乊乣丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 = derive (ℓ "乜丞义乣乊乣丞") (ℓ "丞义乣乊乣丞乜")
  (rw⁻ 0 q44 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = sE 2117 lem-pass-X3-CK31-X3-vs-CS02-TOFF213-CSd02-TOFF213

-- pass [X3 CK31 X3] [CS23 TOFF201 CSd23 TOFF201]: 3 steps
lem-pass-X3-CK31-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (ℓ "丞乔丞义乣乊乣") ⟫ʷ ≈ ⟪ (ℓ "义乣乊乣丞乔丞") ⟫ʷ
lem-pass-X3-CK31-X3-vs-CS23-TOFF201-CSd23-TOFF201 = derive (ℓ "丞乔丞义乣乊乣") (ℓ "义乣乊乣丞乔丞")
  (rw 3 q41 ∷
   rw 0 q45 ∷
   rw⁻ 0 q43 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q47 : Eqn
  q47 = wE 1681 W
  q48 : Eqn
  q48 = wE 5 W
  q49 : Eqn
  q49 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q50 : Eqn
  q50 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q51 : Eqn
  q51 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q52 : Eqn
  q52 = wE 76 W
  q53 : Eqn
  q53 = wE 2063 W
  q54 : Eqn
  q54 = wE 29 W
  q55 : Eqn
  q55 = wE 31 W
  q56 : Eqn
  q56 = wE 1482 W

-- pass [X3 CSd30 X3] [X1 X2 CS03 TOFF012 CSd03 TOFF012 X1 X2]: 87 steps
lem-pass-X3-CSd30-X3-vs-X1-X2-CS03-TOFF012-CSd03-TOFF012-X1-X2 : ⟪ (ℓ "丞丮丞丒丘中九丮九丒丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘中九丮九丒丘丞丮丞") ⟫ʷ
lem-pass-X3-CSd30-X3-vs-X1-X2-CS03-TOFF012-CSd03-TOFF012-X1-X2 = derive (ℓ "丞丮丞丒丘中九丮九丒丘") (ℓ "丒丘中九丮九丒丘丞丮丞")
  (rw 4 q5 ∷
   rw 3 q46 ∷
   rw 2 q7 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw 3 q8 ∷
   rw 0 q7 ∷
   rw 1 q47 ∷
   rw⁻ 0 q46 ∷
   rw 1 q10 ∷
   rw 4 q5 ∷
   re 2 3 (ℓ "丮") ∷
   rw 3 q10 ∷
   rw 4 q8 ∷
   rw 5 q48 ∷
   rw⁻ 4 q49 ∷
   rw⁻ 3 q50 ∷
   re 2 1 (ℓ "乏丨乏") ∷
   rw⁻ 4 q51 ∷
   rw 3 q52 ∷
   rw⁻ 2 q51 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 1 q50 ∷
   rw 2 q53 ∷
   rw 1 q49 ∷
   rw 2 q50 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 3 q51 ∷
   rw 4 q54 ∷
   rw 5 q51 ∷
   re 3 3 (ℓ "丮") ∷
   rw 4 q50 ∷
   rw 5 q55 ∷
   rw 5 q5 ∷
   rw 4 q7 ∷
   re 3 1 (ℓ "乏丨乏") ∷
   rw 5 q8 ∷
   rw 2 q7 ∷
   rw 3 q56 ∷
   rw 2 q10 ∷
   rw 5 q5 ∷
   re 3 3 (ℓ "丮") ∷
   rw 4 q10 ∷
   rw 5 q8 ∷
   rw 2 q11 ∷
   rw 9 q5 ∷
   rw 8 q7 ∷
   re 7 1 (ℓ "乏丨乏") ∷
   rw 9 q8 ∷
   rw 6 q7 ∷
   rw 7 q56 ∷
   rw 6 q10 ∷
   rw 9 q5 ∷
   re 7 3 (ℓ "丮") ∷
   rw 8 q10 ∷
   rw 9 q8 ∷
   rw 10 q5 ∷
   rw 9 q46 ∷
   rw 8 q7 ∷
   re 7 1 (ℓ "乏丨乏") ∷
   rw 9 q8 ∷
   rw 6 q7 ∷
   rw 7 q47 ∷
   rw⁻ 6 q46 ∷
   rw 7 q10 ∷
   rw 10 q5 ∷
   re 8 3 (ℓ "丮") ∷
   rw 9 q10 ∷
   rw 10 q8 ∷
   rw 11 q48 ∷
   rw⁻ 10 q49 ∷
   rw⁻ 9 q50 ∷
   re 8 1 (ℓ "乏丨乏") ∷
   rw⁻ 10 q51 ∷
   rw 9 q52 ∷
   rw⁻ 8 q51 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 7 q50 ∷
   rw 8 q53 ∷
   rw 7 q49 ∷
   rw 8 q50 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q51 ∷
   rw 10 q54 ∷
   rw 11 q51 ∷
   re 9 3 (ℓ "丮") ∷
   rw 10 q50 ∷
   rw 11 q55 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = wE 1682 W
  q58 : Eqn
  q58 = wE 7 W
  q59 : Eqn
  q59 = wE 2064 W
  q60 : Eqn
  q60 = wE 27 W
  q61 : Eqn
  q61 = wE 1490 W

-- pass [X3 CS30 X3] [X1 X2 CS03 TOFF012 CSd03 TOFF012 X1 X2]: 87 steps
lem-pass-X3-CS30-X3-vs-X1-X2-CS03-TOFF012-CSd03-TOFF012-X1-X2 : ⟪ (ℓ "丞中丞丒丘中九丮九丒丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘中九丮九丒丘丞中丞") ⟫ʷ
lem-pass-X3-CS30-X3-vs-X1-X2-CS03-TOFF012-CSd03-TOFF012-X1-X2 = derive (ℓ "丞中丞丒丘中九丮九丒丘") (ℓ "丒丘中九丮九丒丘丞中丞")
  (rw 4 q5 ∷
   rw 3 q46 ∷
   rw 2 q7 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q8 ∷
   rw 0 q7 ∷
   rw 1 q57 ∷
   rw⁻ 0 q46 ∷
   rw 1 q10 ∷
   rw 4 q5 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q10 ∷
   rw 4 q8 ∷
   rw 5 q48 ∷
   rw⁻ 4 q49 ∷
   rw⁻ 3 q50 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw⁻ 4 q51 ∷
   rw 3 q58 ∷
   rw⁻ 2 q51 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 1 q50 ∷
   rw 2 q59 ∷
   rw 1 q49 ∷
   rw 2 q50 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q51 ∷
   rw 4 q60 ∷
   rw 5 q51 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q50 ∷
   rw 5 q55 ∷
   rw 5 q5 ∷
   rw 4 q7 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q8 ∷
   rw 2 q7 ∷
   rw 3 q61 ∷
   rw 2 q10 ∷
   rw 5 q5 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q10 ∷
   rw 5 q8 ∷
   rw 2 q13 ∷
   rw 9 q5 ∷
   rw 8 q7 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q8 ∷
   rw 6 q7 ∷
   rw 7 q61 ∷
   rw 6 q10 ∷
   rw 9 q5 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q10 ∷
   rw 9 q8 ∷
   rw 10 q5 ∷
   rw 9 q46 ∷
   rw 8 q7 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q8 ∷
   rw 6 q7 ∷
   rw 7 q57 ∷
   rw⁻ 6 q46 ∷
   rw 7 q10 ∷
   rw 10 q5 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q10 ∷
   rw 10 q8 ∷
   rw 11 q48 ∷
   rw⁻ 10 q49 ∷
   rw⁻ 9 q50 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q51 ∷
   rw 9 q58 ∷
   rw⁻ 8 q51 ∷
   re 9 3 (ℓ "丽") ∷
   rw⁻ 7 q50 ∷
   rw 8 q59 ∷
   rw 7 q49 ∷
   rw 8 q50 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q51 ∷
   rw 10 q60 ∷
   rw 11 q51 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q50 ∷
   rw 11 q55 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = wE 2065 W
  q63 : Eqn
  q63 = wE 2144 W
  q64 : Eqn
  q64 = sE 2127 lem-pass-X1-CS13-X1-vs-CS03-TOFF012-CSd03-TOFF012
  q65 : Eqn
  q65 = sE 2125 lem-pass-X1-CK13-X1-vs-CS03-TOFF012-CSd03-TOFF012
  q66 : Eqn
  q66 = sE 2128 lem-pass-X1-CSd13-X1-vs-CS03-TOFF012-CSd03-TOFF012
  q67 : Eqn
  q67 = wE 2145 W
  q68 : Eqn
  q68 = wE 2067 W

-- pass [X1 CKd13 X1] [X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2 X3]: 101 steps
lem-pass-X1-CKd13-X1-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : ⟪ (ℓ "丒乂丒丘丞丈上中九丮九下三丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丈上中九丮九下三丘丞丒乂丒") ⟫ʷ
lem-pass-X1-CKd13-X1-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = derive (ℓ "丒乂丒丘丞丈上中九丮九下三丘丞") (ℓ "丘丞丈上中九丮九下三丘丞丒乂丒")
  (rw 0 q62 ∷
   rw 19 q5 ∷
   rw 18 q24 ∷
   rw 17 q14 ∷
   rw 16 q46 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 17 q8 ∷
   rw 14 q46 ∷
   rw 13 q46 ∷
   re 12 1 (ℓ "乏为乏") ∷
   rw 14 q8 ∷
   rw 11 q46 ∷
   rw 10 q46 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 11 q8 ∷
   rw 8 q46 ∷
   rw 7 q46 ∷
   re 6 1 (ℓ "乏为乏") ∷
   rw 8 q8 ∷
   rw 5 q46 ∷
   rw 4 q46 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q8 ∷
   rw 2 q46 ∷
   rw 3 q63 ∷
   rw⁻ 2 q14 ∷
   rw⁻ 3 q24 ∷
   rw⁻ 4 q46 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q46 ∷
   rw⁻ 7 q46 ∷
   rw 10 q5 ∷
   re 8 3 (ℓ "乁") ∷
   rw⁻ 9 q46 ∷
   rw⁻ 10 q46 ∷
   rw 13 q5 ∷
   re 11 3 (ℓ "举") ∷
   rw⁻ 12 q46 ∷
   rw⁻ 13 q46 ∷
   rw 16 q5 ∷
   re 14 3 (ℓ "乁") ∷
   rw⁻ 15 q46 ∷
   rw⁻ 16 q46 ∷
   rw 19 q5 ∷
   re 17 3 (ℓ "丽") ∷
   rw⁻ 18 q46 ∷
   rw 19 q8 ∷
   rw 16 q64 ∷
   rw 13 q65 ∷
   rw 10 q66 ∷
   rw 7 q65 ∷
   rw 4 q64 ∷
   rw 25 q5 ∷
   rw 24 q6 ∷
   rw 23 q21 ∷
   rw 22 q46 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 23 q8 ∷
   rw 20 q46 ∷
   rw 19 q46 ∷
   re 18 1 (ℓ "乏为乏") ∷
   rw 20 q8 ∷
   rw 17 q46 ∷
   rw 16 q46 ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 17 q8 ∷
   rw 14 q46 ∷
   rw 13 q46 ∷
   re 12 1 (ℓ "乏为乏") ∷
   rw 14 q8 ∷
   rw 11 q46 ∷
   rw 10 q46 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 11 q8 ∷
   rw 8 q46 ∷
   rw 9 q67 ∷
   rw⁻ 8 q21 ∷
   rw⁻ 9 q6 ∷
   rw⁻ 10 q46 ∷
   rw 13 q5 ∷
   re 11 3 (ℓ "丽") ∷
   rw⁻ 12 q46 ∷
   rw⁻ 13 q46 ∷
   rw 16 q5 ∷
   re 14 3 (ℓ "乁") ∷
   rw⁻ 15 q46 ∷
   rw⁻ 16 q46 ∷
   rw 19 q5 ∷
   re 17 3 (ℓ "举") ∷
   rw⁻ 18 q46 ∷
   rw⁻ 19 q46 ∷
   rw 22 q5 ∷
   re 20 3 (ℓ "乁") ∷
   rw⁻ 21 q46 ∷
   rw⁻ 22 q46 ∷
   rw 25 q5 ∷
   re 23 3 (ℓ "丽") ∷
   rw⁻ 24 q46 ∷
   rw 25 q8 ∷
   rw 10 q68 ∷ []) Eq.refl

private
  q69 : Eqn
  q69 = wE 2068 W
  q70 : Eqn
  q70 = wE 2146 W
  q71 : Eqn
  q71 = sE 2126 lem-pass-X1-CKd13-X1-vs-CS03-TOFF012-CSd03-TOFF012
  q72 : Eqn
  q72 = wE 2147 W
  q73 : Eqn
  q73 = wE 2070 W

-- pass [X1 CK13 X1] [X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2 X3]: 101 steps
lem-pass-X1-CK13-X1-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : ⟪ (ℓ "丒乁丒丘丞丈上中九丮九下三丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丈上中九丮九下三丘丞丒乁丒") ⟫ʷ
lem-pass-X1-CK13-X1-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = derive (ℓ "丒乁丒丘丞丈上中九丮九下三丘丞") (ℓ "丘丞丈上中九丮九下三丘丞丒乁丒")
  (rw 0 q69 ∷
   rw 19 q5 ∷
   rw 18 q24 ∷
   rw 17 q14 ∷
   rw 16 q46 ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 17 q8 ∷
   rw 14 q46 ∷
   rw 13 q46 ∷
   re 12 1 (ℓ "乏主乏") ∷
   rw 14 q8 ∷
   rw 11 q46 ∷
   rw 10 q46 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 11 q8 ∷
   rw 8 q46 ∷
   rw 7 q46 ∷
   re 6 1 (ℓ "乏主乏") ∷
   rw 8 q8 ∷
   rw 5 q46 ∷
   rw 4 q46 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q8 ∷
   rw 2 q46 ∷
   rw 3 q70 ∷
   rw⁻ 2 q14 ∷
   rw⁻ 3 q24 ∷
   rw⁻ 4 q46 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q46 ∷
   rw⁻ 7 q46 ∷
   rw 10 q5 ∷
   re 8 3 (ℓ "乂") ∷
   rw⁻ 9 q46 ∷
   rw⁻ 10 q46 ∷
   rw 13 q5 ∷
   re 11 3 (ℓ "丽") ∷
   rw⁻ 12 q46 ∷
   rw⁻ 13 q46 ∷
   rw 16 q5 ∷
   re 14 3 (ℓ "乂") ∷
   rw⁻ 15 q46 ∷
   rw⁻ 16 q46 ∷
   rw 19 q5 ∷
   re 17 3 (ℓ "举") ∷
   rw⁻ 18 q46 ∷
   rw 19 q8 ∷
   rw 16 q66 ∷
   rw 13 q71 ∷
   rw 10 q64 ∷
   rw 7 q71 ∷
   rw 4 q66 ∷
   rw 25 q5 ∷
   rw 24 q6 ∷
   rw 23 q21 ∷
   rw 22 q46 ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 23 q8 ∷
   rw 20 q46 ∷
   rw 19 q46 ∷
   re 18 1 (ℓ "乏主乏") ∷
   rw 20 q8 ∷
   rw 17 q46 ∷
   rw 16 q46 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 17 q8 ∷
   rw 14 q46 ∷
   rw 13 q46 ∷
   re 12 1 (ℓ "乏主乏") ∷
   rw 14 q8 ∷
   rw 11 q46 ∷
   rw 10 q46 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 11 q8 ∷
   rw 8 q46 ∷
   rw 9 q72 ∷
   rw⁻ 8 q21 ∷
   rw⁻ 9 q6 ∷
   rw⁻ 10 q46 ∷
   rw 13 q5 ∷
   re 11 3 (ℓ "举") ∷
   rw⁻ 12 q46 ∷
   rw⁻ 13 q46 ∷
   rw 16 q5 ∷
   re 14 3 (ℓ "乂") ∷
   rw⁻ 15 q46 ∷
   rw⁻ 16 q46 ∷
   rw 19 q5 ∷
   re 17 3 (ℓ "丽") ∷
   rw⁻ 18 q46 ∷
   rw⁻ 19 q46 ∷
   rw 22 q5 ∷
   re 20 3 (ℓ "乂") ∷
   rw⁻ 21 q46 ∷
   rw⁻ 22 q46 ∷
   rw 25 q5 ∷
   re 23 3 (ℓ "举") ∷
   rw⁻ 24 q46 ∷
   rw 25 q8 ∷
   rw 10 q73 ∷ []) Eq.refl

private
  q74 : Eqn
  q74 = wE 2071 W
  q75 : Eqn
  q75 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q76 : Eqn
  q76 = eqn (ℓ "丌丶") (ℓ "丶丌") (low₁-comm (X) (CS))
  q77 : Eqn
  q77 = wE 387 W
  q78 : Eqn
  q78 = eqn (ℓ "丌丷") (ℓ "丷丌") (low₁-comm (X) ((CS • CS • CS)))

-- distribute Gad(t=1, W=(0, 3), d=1, e=-1) CS12 TOFF103 CSd12 TOFF103: 14 steps
lem-distribute-Gad⟨t≡1-W≡⟨0-3⟩-d≡1-e≡-1⟩-CS12-TOFF103-CSd12-TOFF103 : ⟪ (ℓ "丌丞丽习举习丌丞") ⟫ʷ ≈ ⟪ (ℓ "丶丌丞乡丌丞丷丌丞乡丌丞") ⟫ʷ
lem-distribute-Gad⟨t≡1-W≡⟨0-3⟩-d≡1-e≡-1⟩-CS12-TOFF103-CSd12-TOFF103 = derive (ℓ "丌丞丽习举习丌丞") (ℓ "丶丌丞乡丌丞丷丌丞乡丌丞")
  (rw 2 q26 ∷
   rw 3 q74 ∷
   rw 8 q74 ∷
   rw 13 q74 ∷
   rw 0 q75 ∷
   rw 1 q76 ∷
   rw 2 q77 ∷
   rw⁻ 0 q28 ∷
   rw 1 q29 ∷
   rw 6 q75 ∷
   rw 7 q78 ∷
   rw 8 q77 ∷
   rw⁻ 6 q30 ∷
   rw 7 q29 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = sE 2124 lem-pass-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3-vs-CCZ123

-- pass [CCZ123] [X0 X3 CS13 TOFF102 CSd13 TOFF102 X0 X3]: 1 steps
lem-pass-CCZ123-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : ⟪ (ℓ "乜丌丞丽习举习丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丽习举习丌丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = derive (ℓ "乜丌丞丽习举习丌丞") (ℓ "丌丞丽习举习丌丞乜")
  (rw⁻ 0 q79 ∷ []) Eq.refl
