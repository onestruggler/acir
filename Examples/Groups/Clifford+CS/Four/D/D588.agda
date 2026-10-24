{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD588 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D588 (W : Ws) (Sᴰ : SD588) where

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
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK21-X2 : St 254
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK21-X2 = pickᴰ 0 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CKd21-X2 : St 257
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CKd21-X2 = pickᴰ 1 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK21-X2 : St 278
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK21-X2 = pickᴰ 2 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CKd21-X2 : St 284
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CKd21-X2 = pickᴰ 3 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CS12-X2 : St 1032
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CS12-X2 = pickᴰ 4 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd12-X2 : St 1033
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd12-X2 = pickᴰ 5 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS12-X2 : St 1034
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS12-X2 = pickᴰ 6 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd12-X2 : St 1035
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd12-X2 = pickᴰ 7 Sᴰ
  lem-T-CZ03-T : St 1036
  lem-T-CZ03-T = pickᴰ 8 Sᴰ
  lem-pass-CCZ123-vs-CSd03 : St 861
  lem-pass-CCZ123-vs-CSd03 = pickᴰ 9 Sᴰ
  lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 840
  lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 10 Sᴰ
  lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 841
  lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 11 Sᴰ
  lem-pass-CCZ123-vs-CS03 : St 843
  lem-pass-CCZ123-vs-CS03 = pickᴰ 12 Sᴰ
  lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 879
  lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 13 Sᴰ
  lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 866
  lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 14 Sᴰ
  lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 867
  lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 15 Sᴰ
  lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03 : St 851
  lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 16 Sᴰ
  lem-pass-X2-CSd20-X2-vs-TOFF012-CS03-TOFF012-CSd03 : St 870
  lem-pass-X2-CSd20-X2-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 17 Sᴰ
  lem-pass-X3-CKd32-X3-vs-TOFF201-CS23-TOFF201-CSd23 : St 905
  lem-pass-X3-CKd32-X3-vs-TOFF201-CS23-TOFF201-CSd23 = pickᴰ 18 Sᴰ
  lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 913
  lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 19 Sᴰ
  lem-pass-CCZ012-vs-CZ13 : St 1037
  lem-pass-CCZ012-vs-CZ13 = pickᴰ 20 Sᴰ
  lem-pass-CCZ012-vs-CZ23 : St 1038
  lem-pass-CCZ012-vs-CZ23 = pickᴰ 21 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 : St 1039
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3 = pickᴰ 22 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : St 1040
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = pickᴰ 23 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : St 1041
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = pickᴰ 24 Sᴰ
  lem-pass-X3-CK30-X3-vs-X1-X2-TOFF012-CS03-TOFF012-CSd03-X1-X2 : St 1042
  lem-pass-X3-CK30-X3-vs-X1-X2-TOFF012-CS03-TOFF012-CSd03-X1-X2 = pickᴰ 25 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = wE 127 W
  q3 : Eqn
  q3 = wE 271 W
  q4 : Eqn
  q4 = wE 7 W
  q5 : Eqn
  q5 = wE 8 W
  q6 : Eqn
  q6 = wE 9 W
  q7 : Eqn
  q7 = wE 10 W
  q8 : Eqn
  q8 = wE 272 W
  q9 : Eqn
  q9 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q10 : Eqn
  q10 = wE 1662 W
  q11 : Eqn
  q11 = sE 1036 lem-T-CZ03-T
  q12 : Eqn
  q12 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q13 : Eqn
  q13 = wE 30 W
  q14 : Eqn
  q14 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q15 : Eqn
  q15 = wE 27 W
  q16 : Eqn
  q16 = wE 24 W
  q17 : Eqn
  q17 = wE 25 W
  q18 : Eqn
  q18 = wE 26 W
  q19 : Eqn
  q19 = wE 323 W
  q20 : Eqn
  q20 = wE 31 W

-- T-CZ03-T @1023: 58 steps
lem-T-CZ03-T-at1023 : ⟪ (ℓ "习丿习") ⟫ʷ ≈ ⟪ (ℓ "乛丿") ⟫ʷ
lem-T-CZ03-T-at1023 = derive (ℓ "习丿习") (ℓ "乛丿")
  (rw 3 q1 ∷
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 9 q2 ∷
   rw 8 q3 ∷
   rw 7 q4 ∷
   rw 6 q5 ∷
   rw 5 q6 ∷
   rw 4 q5 ∷
   rw 3 q7 ∷
   rw 2 q3 ∷
   rw 3 q8 ∷
   re 3 8 (ℓ "九") ∷
   re 1 1 (ℓ "乏丸乏") ∷
   rw⁻ 3 q9 ∷
   rw 2 q10 ∷
   rw⁻ 1 q9 ∷
   re 2 3 (ℓ "丯") ∷
   re 0 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 7 q2 ∷
   rw 6 q3 ∷
   rw 5 q4 ∷
   rw 4 q5 ∷
   rw 3 q6 ∷
   rw 2 q5 ∷
   rw 1 q7 ∷
   rw 0 q3 ∷
   rw 1 q8 ∷
   re 1 8 (ℓ "九") ∷
   rw 1 q11 ∷
   re 1 1 (ℓ "义丹乊丹丽") ∷
   rw 0 q12 ∷
   rw 1 q13 ∷
   rw 2 q14 ∷
   rw 3 q13 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q9 ∷
   rw 5 q15 ∷
   rw 6 q9 ∷
   re 4 3 (ℓ "中") ∷
   rw 0 q1 ∷
   rw 1 q12 ∷
   rw 2 q16 ∷
   rw 3 q14 ∷
   rw 4 q16 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q9 ∷
   rw 6 q17 ∷
   rw 7 q9 ∷
   re 5 3 (ℓ "丽") ∷
   rw 1 q18 ∷
   re 1 5 (ℓ "乜") ∷
   re 0 3 (ℓ "乛") ∷
   re 2 1 (ℓ "乏丩乏") ∷
   rw 1 q9 ∷
   rw 2 q19 ∷
   rw 3 q9 ∷
   re 1 3 (ℓ "丿") ∷
   rw 2 q20 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = sE 1032 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CS12-X2
  q22 : Eqn
  q22 = sE 254 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CK21-X2
  q23 : Eqn
  q23 = sE 1040 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3
  q24 : Eqn
  q24 = sE 257 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CKd21-X2
  q25 : Eqn
  q25 = sE 1033 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CSd12-X2

-- Bar(SSKSKK;2,1->0) passes split Gad(t=1, W=(2, 3), d=SK, e=-1): 5 steps
lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丶丘丘乇丘丘丞丽习举习丘丞丘么丘丘丷丘") ⟫ʷ ≈ ⟪ (ℓ "丘丶丘丘乇丘丘丞丽习举习丘丞丘么丘丘丷丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SK-e≡-1⟩ = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丶丘丘乇丘丘丞丽习举习丘丞丘么丘丘丷丘") (ℓ "丘丶丘丘乇丘丘丞丽习举习丘丞丘么丘丘丷丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 0 q21 ∷
   rw 3 q22 ∷
   rw 6 q23 ∷
   rw 14 q24 ∷
   rw 17 q25 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = sE 843 lem-pass-CCZ123-vs-CS03

-- pass [CS03] [CCZ123]: 1 steps
lem-pass-CS03-vs-CCZ123 : ⟪ (ℓ "中乜") ⟫ʷ ≈ ⟪ (ℓ "乜中") ⟫ʷ
lem-pass-CS03-vs-CCZ123 = derive (ℓ "中乜") (ℓ "乜中")
  (rw⁻ 0 q26 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = wE 53 W
  q28 : Eqn
  q28 = eqn (ℓ "下丿") (ℓ "丿下") (low₁-comm ((K • iI)) ((Swap ↑ • CZ • Swap ↑)))
  q29 : Eqn
  q29 = sE 1037 lem-pass-CCZ012-vs-CZ13
  q30 : Eqn
  q30 = eqn (ℓ "上丿") (ℓ "丿上") (low₁-comm (K) ((Swap ↑ • CZ • Swap ↑)))
  q31 : Eqn
  q31 = wE 55 W

-- pass [TOFF012] [CZ13]: 5 steps
lem-pass-TOFF012-vs-CZ13 : ⟪ (ℓ "九丿") ⟫ʷ ≈ ⟪ (ℓ "丿九") ⟫ʷ
lem-pass-TOFF012-vs-CZ13 = derive (ℓ "九丿") (ℓ "丿九")
  (rw 0 q27 ∷
   rw 2 q28 ∷
   rw 1 q29 ∷
   rw 0 q30 ∷
   rw 1 q31 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = eqn (ℓ "下之") (ℓ "之下") (low₁-comm ((K • iI)) ((CZ ↑)))
  q33 : Eqn
  q33 = sE 1038 lem-pass-CCZ012-vs-CZ23
  q34 : Eqn
  q34 = eqn (ℓ "上之") (ℓ "之上") (low₁-comm (K) ((CZ ↑)))

-- pass [TOFF012] [CZ23]: 5 steps
lem-pass-TOFF012-vs-CZ23 : ⟪ (ℓ "九之") ⟫ʷ ≈ ⟪ (ℓ "之九") ⟫ʷ
lem-pass-TOFF012-vs-CZ23 = derive (ℓ "九之") (ℓ "之九")
  (rw 0 q27 ∷
   rw 2 q32 ∷
   rw 1 q33 ∷
   rw 0 q34 ∷
   rw 1 q31 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = sE 861 lem-pass-CCZ123-vs-CSd03

-- pass [CSd03] [CCZ123]: 1 steps
lem-pass-CSd03-vs-CCZ123 : ⟪ (ℓ "丮乜") ⟫ʷ ≈ ⟪ (ℓ "乜丮") ⟫ʷ
lem-pass-CSd03-vs-CCZ123 = derive (ℓ "丮乜") (ℓ "乜丮")
  (rw⁻ 0 q35 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = wE 1 W
  q37 : Eqn
  q37 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q38 : Eqn
  q38 = wE 173 W
  q39 : Eqn
  q39 = wE 3 W
  q40 : Eqn
  q40 = wE 1411 W
  q41 : Eqn
  q41 = wE 175 W
  q42 : Eqn
  q42 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q43 : Eqn
  q43 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q44 : Eqn
  q44 = wE 140 W
  q45 : Eqn
  q45 = wE 1412 W
  q46 : Eqn
  q46 = wE 142 W
  q47 : Eqn
  q47 = wE 1413 W
  q48 : Eqn
  q48 = sE 840 lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [X3 CK30 X3] [X1 X2 CS03 TOFF012 CSd03 TOFF012 X1 X2]: 87 steps
lem-pass-X3-CK30-X3-vs-X1-X2-CS03-TOFF012-CSd03-TOFF012-X1-X2 : ⟪ (ℓ "丞乑丞丒丘中九丮九丒丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘中九丮九丒丘丞乑丞") ⟫ʷ
lem-pass-X3-CK30-X3-vs-X1-X2-CS03-TOFF012-CSd03-TOFF012-X1-X2 = derive (ℓ "丞乑丞丒丘中九丮九丒丘") (ℓ "丒丘中九丮九丒丘丞乑丞")
  (rw 4 q36 ∷
   rw 3 q37 ∷
   rw 2 q38 ∷
   re 1 1 (ℓ "乏乄乏") ∷
   rw 3 q39 ∷
   rw 0 q38 ∷
   rw 1 q40 ∷
   rw⁻ 0 q37 ∷
   rw 1 q41 ∷
   rw 4 q36 ∷
   re 2 3 (ℓ "乑") ∷
   rw 3 q41 ∷
   rw 4 q39 ∷
   rw 5 q1 ∷
   rw⁻ 4 q42 ∷
   rw⁻ 3 q43 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw⁻ 4 q9 ∷
   rw 3 q44 ∷
   rw⁻ 2 q9 ∷
   re 3 3 (ℓ "乔") ∷
   rw⁻ 1 q43 ∷
   rw 2 q45 ∷
   rw 1 q42 ∷
   rw 2 q43 ∷
   re 4 1 (ℓ "乏乇乏") ∷
   rw 3 q9 ∷
   rw 4 q46 ∷
   rw 5 q9 ∷
   re 3 3 (ℓ "乑") ∷
   rw 4 q43 ∷
   rw 5 q20 ∷
   rw 5 q36 ∷
   rw 4 q38 ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw 5 q39 ∷
   rw 2 q38 ∷
   rw 3 q47 ∷
   rw 2 q41 ∷
   rw 5 q36 ∷
   re 3 3 (ℓ "乑") ∷
   rw 4 q41 ∷
   rw 5 q39 ∷
   rw 2 q48 ∷
   rw 9 q36 ∷
   rw 8 q38 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw 9 q39 ∷
   rw 6 q38 ∷
   rw 7 q47 ∷
   rw 6 q41 ∷
   rw 9 q36 ∷
   re 7 3 (ℓ "乑") ∷
   rw 8 q41 ∷
   rw 9 q39 ∷
   rw 10 q36 ∷
   rw 9 q37 ∷
   rw 8 q38 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw 9 q39 ∷
   rw 6 q38 ∷
   rw 7 q40 ∷
   rw⁻ 6 q37 ∷
   rw 7 q41 ∷
   rw 10 q36 ∷
   re 8 3 (ℓ "乑") ∷
   rw 9 q41 ∷
   rw 10 q39 ∷
   rw 11 q1 ∷
   rw⁻ 10 q42 ∷
   rw⁻ 9 q43 ∷
   re 8 1 (ℓ "乏乄乏") ∷
   rw⁻ 10 q9 ∷
   rw 9 q44 ∷
   rw⁻ 8 q9 ∷
   re 9 3 (ℓ "乔") ∷
   rw⁻ 7 q43 ∷
   rw 8 q45 ∷
   rw 7 q42 ∷
   rw 8 q43 ∷
   re 10 1 (ℓ "乏乇乏") ∷
   rw 9 q9 ∷
   rw 10 q46 ∷
   rw 11 q9 ∷
   re 9 3 (ℓ "乑") ∷
   rw 10 q43 ∷
   rw 11 q20 ∷ []) Eq.refl

-- Bar(SSKSKK;2,1->0) passes split Gad(t=1, W=(2, 3), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丷丘丘么丘丘丶丘丘丶丘丘丞丽习举习丘丞丘丷丘丘丷丘丘乇丘丘丶丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘丘么丘丘丶丘丘丶丘丘丞丽习举习丘丞丘丷丘丘丷丘丘乇丘丘丶丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丷丘丘么丘丘丶丘丘丶丘丘丞丽习举习丘丞丘丷丘丘丷丘丘乇丘丘丶丘") (ℓ "丘丷丘丘么丘丘丶丘丘丶丘丘丞丽习举习丘丞丘丷丘丘丷丘丘乇丘丘丶丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 0 q25 ∷
   rw 3 q24 ∷
   rw 6 q21 ∷
   rw 9 q21 ∷
   rw 12 q23 ∷
   rw 20 q25 ∷
   rw 23 q25 ∷
   rw 26 q22 ∷
   rw 29 q21 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = sE 1035 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd12-X2
  q50 : Eqn
  q50 = sE 284 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CKd21-X2
  q51 : Eqn
  q51 = sE 1034 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CS12-X2
  q52 : Eqn
  q52 = sE 1041 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3
  q53 : Eqn
  q53 = sE 278 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CK21-X2

-- Bar(SSSKSS;2,1->0) passes split Gad(t=1, W=(2, 3), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSSKSS21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丷丘丘么丘丘丶丘丘丶丘丘丞丽习举习丘丞丘丷丘丘丷丘丘乇丘丘丶丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘丘么丘丘丶丘丘丶丘丘丞丽习举习丘丞丘丷丘丘丷丘丘乇丘丘丶丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠") ⟫ʷ
lem-Bar⟨SSSKSS21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘丷丘丘么丘丘丶丘丘丶丘丘丞丽习举习丘丞丘丷丘丘丷丘丘乇丘丘丶丘") (ℓ "丘丷丘丘么丘丘丶丘丘丶丘丘丞丽习举习丘丞丘丷丘丘丷丘丘乇丘丘丶丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠")
  (rw 0 q49 ∷
   rw 3 q50 ∷
   rw 6 q51 ∷
   rw 9 q51 ∷
   rw 12 q52 ∷
   rw 20 q49 ∷
   rw 23 q49 ∷
   rw 26 q53 ∷
   rw 29 q51 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = wE 1497 W
  q55 : Eqn
  q55 = wE 1663 W
  q56 : Eqn
  q56 = sE 867 lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q57 : Eqn
  q57 = wE 1664 W

-- pass [X2 CKd21 X2] [X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X3]: 5 steps
lem-pass-X2-CKd21-X2-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : ⟪ (ℓ "丘么丘丞三下丈丈中九丮九三三上丈丞") ⟫ʷ ≈ ⟪ (ℓ "丞三下丈丈中九丮九三三上丈丞丘么丘") ⟫ʷ
lem-pass-X2-CKd21-X2-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = derive (ℓ "丘么丘丞三下丈丈中九丮九三三上丈丞") (ℓ "丞三下丈丈中九丮九三三上丈丞丘么丘")
  (rw 0 q54 ∷
   rw 1 q55 ∷
   rw 5 q56 ∷
   rw 9 q57 ∷
   rw 13 q54 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = wE 1495 W
  q59 : Eqn
  q59 = wE 1665 W
  q60 : Eqn
  q60 = sE 866 lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q61 : Eqn
  q61 = wE 1666 W

-- pass [X2 CK21 X2] [X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X3]: 5 steps
lem-pass-X2-CK21-X2-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : ⟪ (ℓ "丘乇丘丞三下丈丈中九丮九三三上丈丞") ⟫ʷ ≈ ⟪ (ℓ "丞三下丈丈中九丮九三三上丈丞丘乇丘") ⟫ʷ
lem-pass-X2-CK21-X2-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = derive (ℓ "丘乇丘丞三下丈丈中九丮九三三上丈丞") (ℓ "丞三下丈丈中九丮九三三上丈丞丘乇丘")
  (rw 0 q58 ∷
   rw 1 q59 ∷
   rw 5 q60 ∷
   rw 9 q61 ∷
   rw 13 q58 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = sE 1039 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3

-- Bar(SSKSKK;2,1->0) passes split Gad(t=1, W=(0, 2, 3), d=SK, e=-1): 5 steps
lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丶丘丘乇丘丌丘丞丽习举习丌丘丞丘么丘丘丷丘") ⟫ʷ ≈ ⟪ (ℓ "丘丶丘丘乇丘丌丘丞丽习举习丌丘丞丘么丘丘丷丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SK-e≡-1⟩ = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丶丘丘乇丘丌丘丞丽习举习丌丘丞丘么丘丘丷丘") (ℓ "丘丶丘丘乇丘丌丘丞丽习举习丌丘丞丘么丘丘丷丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 0 q21 ∷
   rw 3 q22 ∷
   rw 6 q62 ∷
   rw 16 q24 ∷
   rw 19 q25 ∷ []) Eq.refl

-- Bar(SSKSKK;2,1->0) passes split Gad(t=1, W=(0, 2, 3), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丷丘丘么丘丘丶丘丘丶丘丌丘丞丽习举习丌丘丞丘丷丘丘丷丘丘乇丘丘丶丘") ⟫ʷ ≈ ⟪ (ℓ "丘丷丘丘么丘丘丶丘丘丶丘丌丘丞丽习举习丌丘丞丘丷丘丘丷丘丘乇丘丘丶丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSKSKK21-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘丷丘丘么丘丘丶丘丘丶丘丌丘丞丽习举习丌丘丞丘丷丘丘丷丘丘乇丘丘丶丘") (ℓ "丘丷丘丘么丘丘丶丘丘丶丘丌丘丞丽习举习丌丘丞丘丷丘丘丷丘丘乇丘丘丶丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 0 q25 ∷
   rw 3 q24 ∷
   rw 6 q21 ∷
   rw 9 q21 ∷
   rw 12 q62 ∷
   rw 22 q25 ∷
   rw 25 q25 ∷
   rw 28 q22 ∷
   rw 31 q21 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = wE 1493 W
  q64 : Eqn
  q64 = wE 1490 W
  q65 : Eqn
  q65 = sE 851 lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [X2 CS20 X2] [X3 TOFF012 CS03 TOFF012 CSd03 X3]: 25 steps
lem-pass-X2-CS20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : ⟪ (ℓ "丘丧丘丞九中九丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞九中九丮丞丘丧丘") ⟫ʷ
lem-pass-X2-CS20-X2-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = derive (ℓ "丘丧丘丞九中九丮丞") (ℓ "丞九中九丮丞丘丧丘")
  (rw 4 q1 ∷
   rw⁻ 3 q43 ∷
   rw⁻ 2 q42 ∷
   rw 1 q4 ∷
   rw⁻ 0 q42 ∷
   rw 1 q63 ∷
   rw 0 q43 ∷
   rw 1 q42 ∷
   rw 2 q15 ∷
   rw 3 q42 ∷
   rw 4 q20 ∷
   rw 1 q64 ∷
   rw 1 q65 ∷
   rw 5 q64 ∷
   rw 9 q1 ∷
   rw⁻ 8 q43 ∷
   rw⁻ 7 q42 ∷
   rw 6 q4 ∷
   rw⁻ 5 q42 ∷
   rw 6 q63 ∷
   rw 5 q43 ∷
   rw 6 q42 ∷
   rw 7 q15 ∷
   rw 8 q42 ∷
   rw 9 q20 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = wE 76 W
  q67 : Eqn
  q67 = wE 1499 W
  q68 : Eqn
  q68 = wE 29 W
  q69 : Eqn
  q69 = wE 1667 W
  q70 : Eqn
  q70 = sE 870 lem-pass-X2-CSd20-X2-vs-TOFF012-CS03-TOFF012-CSd03
  q71 : Eqn
  q71 = wE 1668 W

-- pass [X2 CSd20 X2] [X3 Sd0 TOFF012 CS03 TOFF012 CSd03 S0 X3]: 25 steps
lem-pass-X2-CSd20-X2-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3 : ⟪ (ℓ "丘丨丘丞三九中九丮丈丞") ⟫ʷ ≈ ⟪ (ℓ "丞三九中九丮丈丞丘丨丘") ⟫ʷ
lem-pass-X2-CSd20-X2-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3 = derive (ℓ "丘丨丘丞三九中九丮丈丞") (ℓ "丞三九中九丮丈丞丘丨丘")
  (rw 4 q1 ∷
   rw⁻ 3 q43 ∷
   rw⁻ 2 q42 ∷
   rw 1 q66 ∷
   rw⁻ 0 q42 ∷
   rw 1 q67 ∷
   rw 0 q43 ∷
   rw 1 q42 ∷
   rw 2 q68 ∷
   rw 3 q42 ∷
   rw 4 q20 ∷
   rw 1 q69 ∷
   rw 2 q70 ∷
   rw 6 q71 ∷
   rw 11 q1 ∷
   rw⁻ 10 q43 ∷
   rw⁻ 9 q42 ∷
   rw 8 q66 ∷
   rw⁻ 7 q42 ∷
   rw 8 q67 ∷
   rw 7 q43 ∷
   rw 8 q42 ∷
   rw 9 q68 ∷
   rw 10 q42 ∷
   rw 11 q20 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = wE 1669 W
  q73 : Eqn
  q73 = wE 1670 W
  q74 : Eqn
  q74 = sE 879 lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [X1 CS10 X1] [X3 TOFF012 CS03 TOFF012 CSd03 X3]: 5 steps
lem-pass-X1-CS10-X1-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 : ⟪ (ℓ "丒丠丒丞九中九丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞九中九丮丞丒丠丒") ⟫ʷ
lem-pass-X1-CS10-X1-vs-X3-TOFF012-CS03-TOFF012-CSd03-X3 = derive (ℓ "丒丠丒丞九中九丮丞") (ℓ "丞九中九丮丞丒丠丒")
  (rw 0 q72 ∷
   rw 1 q73 ∷
   rw 1 q74 ∷
   rw 5 q73 ∷
   rw 5 q72 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = wE 1671 W
  q76 : Eqn
  q76 = wE 1672 W
  q77 : Eqn
  q77 = sE 913 lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03
  q78 : Eqn
  q78 = wE 1673 W

-- pass [X1 CSd10 X1] [X3 Sd0 TOFF012 CS03 TOFF012 CSd03 S0 X3]: 5 steps
lem-pass-X1-CSd10-X1-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3 : ⟪ (ℓ "丒両丒丞三九中九丮丈丞") ⟫ʷ ≈ ⟪ (ℓ "丞三九中九丮丈丞丒両丒") ⟫ʷ
lem-pass-X1-CSd10-X1-vs-X3-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X3 = derive (ℓ "丒両丒丞三九中九丮丈丞") (ℓ "丞三九中九丮丈丞丒両丒")
  (rw 0 q75 ∷
   rw 1 q76 ∷
   rw 2 q77 ∷
   rw 6 q78 ∷
   rw 7 q75 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = wE 1674 W
  q80 : Eqn
  q80 = sE 905 lem-pass-X3-CKd32-X3-vs-TOFF201-CS23-TOFF201-CSd23
  q81 : Eqn
  q81 = wE 1675 W

-- pass [CKd32] [X3 TOFF201 CS23 TOFF201 CSd23 X3]: 3 steps
lem-pass-CKd32-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 : ⟪ (ℓ "乘丞乣义乣乊丞") ⟫ʷ ≈ ⟪ (ℓ "丞乣义乣乊丞乘") ⟫ʷ
lem-pass-CKd32-vs-X3-TOFF201-CS23-TOFF201-CSd23-X3 = derive (ℓ "乘丞乣义乣乊丞") (ℓ "丞乣义乣乊丞乘")
  (rw 0 q79 ∷
   rw 1 q80 ∷
   rw 5 q81 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = wE 1676 W
  q83 : Eqn
  q83 = wE 137 W
  q84 : Eqn
  q84 = wE 1677 W
  q85 : Eqn
  q85 = wE 139 W
  q86 : Eqn
  q86 = wE 1485 W
  q87 : Eqn
  q87 = sE 841 lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [X3 CKd30 X3] [X1 X2 TOFF012 CS03 TOFF012 CSd03 X1 X2]: 87 steps
lem-pass-X3-CKd30-X3-vs-X1-X2-TOFF012-CS03-TOFF012-CSd03-X1-X2 : ⟪ (ℓ "丞乒丞丒丘九中九丮丒丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘九中九丮丒丘丞乒丞") ⟫ʷ
lem-pass-X3-CKd30-X3-vs-X1-X2-TOFF012-CS03-TOFF012-CSd03-X1-X2 = derive (ℓ "丞乒丞丒丘九中九丮丒丘") (ℓ "丒丘九中九丮丒丘丞乒丞")
  (rw 4 q36 ∷
   rw 3 q37 ∷
   rw 2 q38 ∷
   re 1 1 (ℓ "乏久乏") ∷
   rw 3 q39 ∷
   rw 0 q38 ∷
   rw 1 q82 ∷
   rw⁻ 0 q37 ∷
   rw 1 q41 ∷
   rw 4 q36 ∷
   re 2 3 (ℓ "乒") ∷
   rw 3 q41 ∷
   rw 4 q39 ∷
   rw 5 q1 ∷
   rw⁻ 4 q42 ∷
   rw⁻ 3 q43 ∷
   re 2 1 (ℓ "乏久乏") ∷
   rw⁻ 4 q9 ∷
   rw 3 q83 ∷
   rw⁻ 2 q9 ∷
   re 3 3 (ℓ "乕") ∷
   rw⁻ 1 q43 ∷
   rw 2 q84 ∷
   rw 1 q42 ∷
   rw 2 q43 ∷
   re 4 1 (ℓ "乏么乏") ∷
   rw 3 q9 ∷
   rw 4 q85 ∷
   rw 5 q9 ∷
   re 3 3 (ℓ "乒") ∷
   rw 4 q43 ∷
   rw 5 q20 ∷
   rw 5 q36 ∷
   rw 4 q38 ∷
   re 3 1 (ℓ "乏久乏") ∷
   rw 5 q39 ∷
   rw 2 q38 ∷
   rw 3 q86 ∷
   rw 2 q41 ∷
   rw 5 q36 ∷
   re 3 3 (ℓ "乒") ∷
   rw 4 q41 ∷
   rw 5 q39 ∷
   rw 2 q87 ∷
   rw 9 q36 ∷
   rw 8 q38 ∷
   re 7 1 (ℓ "乏久乏") ∷
   rw 9 q39 ∷
   rw 6 q38 ∷
   rw 7 q86 ∷
   rw 6 q41 ∷
   rw 9 q36 ∷
   re 7 3 (ℓ "乒") ∷
   rw 8 q41 ∷
   rw 9 q39 ∷
   rw 10 q36 ∷
   rw 9 q37 ∷
   rw 8 q38 ∷
   re 7 1 (ℓ "乏久乏") ∷
   rw 9 q39 ∷
   rw 6 q38 ∷
   rw 7 q82 ∷
   rw⁻ 6 q37 ∷
   rw 7 q41 ∷
   rw 10 q36 ∷
   re 8 3 (ℓ "乒") ∷
   rw 9 q41 ∷
   rw 10 q39 ∷
   rw 11 q1 ∷
   rw⁻ 10 q42 ∷
   rw⁻ 9 q43 ∷
   re 8 1 (ℓ "乏久乏") ∷
   rw⁻ 10 q9 ∷
   rw 9 q83 ∷
   rw⁻ 8 q9 ∷
   re 9 3 (ℓ "乕") ∷
   rw⁻ 7 q43 ∷
   rw 8 q84 ∷
   rw 7 q42 ∷
   rw 8 q43 ∷
   re 10 1 (ℓ "乏么乏") ∷
   rw 9 q9 ∷
   rw 10 q85 ∷
   rw 11 q9 ∷
   re 9 3 (ℓ "乒") ∷
   rw 10 q43 ∷
   rw 11 q20 ∷ []) Eq.refl

private
  q88 : Eqn
  q88 = wE 1678 W
  q89 : Eqn
  q89 = wE 1679 W

-- pass [X1 CSd10 X1] [X2 X3 TOFF012 CS03 TOFF012 CSd03 X2 X3]: 7 steps
lem-pass-X1-CSd10-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : ⟪ (ℓ "丒両丒丘丞九中九丮丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞九中九丮丘丞丒両丒") ⟫ʷ
lem-pass-X1-CSd10-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = derive (ℓ "丒両丒丘丞九中九丮丘丞") (ℓ "丘丞九中九丮丘丞丒両丒")
  (rw 0 q88 ∷
   rw 1 q75 ∷
   rw 2 q89 ∷
   rw 2 q77 ∷
   rw 6 q89 ∷
   rw 6 q88 ∷
   rw 7 q75 ∷ []) Eq.refl

private
  q90 : Eqn
  q90 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q91 : Eqn
  q91 = eqn (ℓ "丒丞") (ℓ "丞丒") (low-comm ((X ↑)) ((X ↑)))
  q92 : Eqn
  q92 = wE 1407 W
  q93 : Eqn
  q93 = sE 1042 lem-pass-X3-CK30-X3-vs-X1-X2-TOFF012-CS03-TOFF012-CSd03-X1-X2
  q94 : Eqn
  q94 = wE 1408 W

-- pass [CK30] [X1 X2 X3 TOFF012 CS03 TOFF012 CSd03 X1 X2 X3]: 27 steps
lem-pass-CK30-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 : ⟪ (ℓ "乑丒丘丞九中九丮丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞九中九丮丒丘丞乑") ⟫ʷ
lem-pass-CK30-vs-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3 = derive (ℓ "乑丒丘丞九中九丮丒丘丞") (ℓ "丒丘丞九中九丮丒丘丞乑")
  (rw 2 q90 ∷
   rw 1 q91 ∷
   rw 2 q36 ∷
   rw 1 q38 ∷
   re 0 1 (ℓ "乏乄乏") ∷
   rw 2 q39 ∷
   rw 1 q92 ∷
   rw 0 q41 ∷
   rw 1 q41 ∷
   rw 4 q36 ∷
   re 2 3 (ℓ "乑") ∷
   rw 3 q41 ∷
   rw 4 q39 ∷
   rw 1 q93 ∷
   rw 13 q36 ∷
   rw 12 q38 ∷
   rw 11 q38 ∷
   re 10 1 (ℓ "乏乄乏") ∷
   rw 12 q39 ∷
   rw 9 q38 ∷
   rw 10 q94 ∷
   rw 9 q41 ∷
   rw 12 q36 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q39 ∷
   rw⁻ 0 q91 ∷
   rw⁻ 1 q90 ∷ []) Eq.refl

private
  q95 : Eqn
  q95 = wE 1680 W

-- pass [X1 CS10 X1] [X2 X3 TOFF012 CS03 TOFF012 CSd03 X2 X3]: 7 steps
lem-pass-X1-CS10-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : ⟪ (ℓ "丒丠丒丘丞九中九丮丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞九中九丮丘丞丒丠丒") ⟫ʷ
lem-pass-X1-CS10-X1-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = derive (ℓ "丒丠丒丘丞九中九丮丘丞") (ℓ "丘丞九中九丮丘丞丒丠丒")
  (rw 0 q95 ∷
   rw 1 q72 ∷
   rw 2 q73 ∷
   rw 2 q74 ∷
   rw 6 q73 ∷
   rw 6 q95 ∷
   rw 7 q72 ∷ []) Eq.refl

private
  q96 : Eqn
  q96 = wE 1681 W
  q97 : Eqn
  q97 = wE 1482 W

-- pass [X2 CSd20 X2] [X1 X3 TOFF012 CS03 TOFF012 CSd03 X1 X3]: 27 steps
lem-pass-X2-CSd20-X2-vs-X1-X3-TOFF012-CS03-TOFF012-CSd03-X1-X3 : ⟪ (ℓ "丘丨丘丒丞九中九丮丒丞") ⟫ʷ ≈ ⟪ (ℓ "丒丞九中九丮丒丞丘丨丘") ⟫ʷ
lem-pass-X2-CSd20-X2-vs-X1-X3-TOFF012-CS03-TOFF012-CSd03-X1-X3 = derive (ℓ "丘丨丘丒丞九中九丮丒丞") (ℓ "丒丞九中九丮丒丞丘丨丘")
  (rw 0 q96 ∷
   rw 5 q1 ∷
   rw⁻ 4 q43 ∷
   rw⁻ 3 q42 ∷
   rw 2 q66 ∷
   rw⁻ 1 q42 ∷
   rw 2 q67 ∷
   rw 1 q43 ∷
   rw 2 q42 ∷
   rw 3 q68 ∷
   rw 4 q42 ∷
   rw 5 q20 ∷
   rw 2 q97 ∷
   rw 2 q70 ∷
   rw 6 q97 ∷
   rw 6 q96 ∷
   rw 11 q1 ∷
   rw⁻ 10 q43 ∷
   rw⁻ 9 q42 ∷
   rw 8 q66 ∷
   rw⁻ 7 q42 ∷
   rw 8 q67 ∷
   rw 7 q43 ∷
   rw 8 q42 ∷
   rw 9 q68 ∷
   rw 10 q42 ∷
   rw 11 q20 ∷ []) Eq.refl

private
  q98 : Eqn
  q98 = wE 1682 W

-- pass [X2 CS20 X2] [X1 X3 TOFF012 CS03 TOFF012 CSd03 X1 X3]: 27 steps
lem-pass-X2-CS20-X2-vs-X1-X3-TOFF012-CS03-TOFF012-CSd03-X1-X3 : ⟪ (ℓ "丘丧丘丒丞九中九丮丒丞") ⟫ʷ ≈ ⟪ (ℓ "丒丞九中九丮丒丞丘丧丘") ⟫ʷ
lem-pass-X2-CS20-X2-vs-X1-X3-TOFF012-CS03-TOFF012-CSd03-X1-X3 = derive (ℓ "丘丧丘丒丞九中九丮丒丞") (ℓ "丒丞九中九丮丒丞丘丧丘")
  (rw 0 q98 ∷
   rw 5 q1 ∷
   rw⁻ 4 q43 ∷
   rw⁻ 3 q42 ∷
   rw 2 q4 ∷
   rw⁻ 1 q42 ∷
   rw 2 q63 ∷
   rw 1 q43 ∷
   rw 2 q42 ∷
   rw 3 q15 ∷
   rw 4 q42 ∷
   rw 5 q20 ∷
   rw 2 q64 ∷
   rw 2 q65 ∷
   rw 6 q64 ∷
   rw 6 q98 ∷
   rw 11 q1 ∷
   rw⁻ 10 q43 ∷
   rw⁻ 9 q42 ∷
   rw 8 q4 ∷
   rw⁻ 7 q42 ∷
   rw 8 q63 ∷
   rw 7 q43 ∷
   rw 8 q42 ∷
   rw 9 q15 ∷
   rw 10 q42 ∷
   rw 11 q20 ∷ []) Eq.refl
