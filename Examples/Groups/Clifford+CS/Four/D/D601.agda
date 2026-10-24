{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD601 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D601 (W : Ws) (Sᴰ : SD601) where

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

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK30-CS03-CS03-CKd30-X3 : St 451
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK30-CS03-CS03-CKd30-X3 = pickᴰ 0 Sᴰ
  lem-pass-CK30-CS03-CS03-CKd30-vs-X3-TOFF213-X3 : St 1295
  lem-pass-CK30-CS03-CS03-CKd30-vs-X3-TOFF213-X3 = pickᴰ 1 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-CS12-CS12-CKd21-X2 : St 1281
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-CS12-CS12-CKd21-X2 = pickᴰ 2 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd12-CKd21-CS12-CS12-X2 : St 1296
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd12-CKd21-CS12-CS12-X2 = pickᴰ 3 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X3 : St 1297
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X3 = pickᴰ 4 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF213-X3 : St 1234
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF213-X3 = pickᴰ 5 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-S3-S3-S3-CK31-S3-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-X2 : St 1298
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-S3-S3-S3-CK31-S3-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-X2 = pickᴰ 6 Sᴰ

private
  q1 : Eqn
  q1 = sE 1281 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-CS12-CS12-CKd21-X2
  q2 : Eqn
  q2 = sE 1296 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd12-CKd21-CS12-CS12-X2
  q3 : Eqn
  q3 = sE 1298 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-S3-S3-S3-CK31-S3-S3-S3-S3-CK31-S3-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-X2

-- Bar(SSSKSS;2,3->0) passes factors of X1 X2 X3 CS12 CS12 CK21 CS12 CK21 CK21 CX23 CK31 S3 CK31 S3 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CX23 CS13 CS13 CK31 CS13 CK31 CK31 X1 X2 X3: 4 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X1-X2-X3-CS12-CS12-CK21-CS12-CK21-CK21-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CK31-CS13-CK31-CK31-X1-X2-X3 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘乇丶丶么丘丘丷么丶丶丘丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽业业业乔业业业业乔业乌乔业乔业丽丽丽乔业丽丽丽丽丽丽丘丘乇丶丶么丘") ⟫ʷ ≈ ⟪ (ℓ "丘乇丶丶么丘丘丷么丶丶丘丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽业业业乔业业业业乔业乌乔业乔业丽丽丽乔业丽丽丽丽丽丽丘丘乇丶丶么丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X1-X2-X3-CS12-CS12-CK21-CS12-CK21-CK21-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CK31-CS13-CK31-CK31-X1-X2-X3 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘乇丶丶么丘丘丷么丶丶丘丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽业业业乔业业业业乔业乌乔业乔业丽丽丽乔业丽丽丽丽丽丽丘丘乇丶丶么丘") (ℓ "丘乇丶丶么丘丘丷么丶丶丘丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乌丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽丽业业业乔业丽丽丽丽丽丽丽丽丽业业业乔业业业业乔业乌乔业乔业丽丽丽乔业丽丽丽丽丽丽丘丘乇丶丶么丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 0 q1 ∷
   rw 6 q2 ∷
   rw 12 q3 ∷
   rw 88 q1 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = sE 451 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK30-CS03-CS03-CKd30-X3
  q5 : Eqn
  q5 = sE 1297 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X3

-- Bar(SSKSKK;3,2->0) passes factors of X0 X3 CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10 X0 X3: 3 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X0-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X0-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乑中中乒丞丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞丞乑中中乒丞") ⟫ʷ ≈ ⟪ (ℓ "丞乑中中乒丞丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞丞乑中中乒丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X0-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X0-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乑中中乒丞丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞丞乑中中乒丞") (ℓ "丞乑中中乒丞丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞丞乑中中乒丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 0 q4 ∷
   rw 6 q5 ∷
   rw 37 q4 ∷ []) Eq.refl

private
  q6 : Eqn
  q6 = wE 1 W
  q7 : Eqn
  q7 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q8 : Eqn
  q8 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q9 : Eqn
  q9 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q10 : Eqn
  q10 = wE 3 W
  q11 : Eqn
  q11 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q12 : Eqn
  q12 = wE 1790 W
  q13 : Eqn
  q13 = sE 1295 lem-pass-CK30-CS03-CS03-CKd30-vs-X3-TOFF213-X3
  q14 : Eqn
  q14 = sE 1234 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF213-X3
  q15 : Eqn
  q15 = wE 1791 W

-- pass [X0 CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10 X0] [X3 TOFF213 X3]: 193 steps
lem-pass-X0-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X0-vs-X3-TOFF213-X3 : ⟪ (ℓ "丌中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丌丞乥丞") ⟫ʷ ≈ ⟪ (ℓ "丞乥丞丌中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丌") ⟫ʷ
lem-pass-X0-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X0-vs-X3-TOFF213-X3 = derive (ℓ "丌中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丌丞乥丞") (ℓ "丞乥丞丌中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丌")
  (rw 31 q6 ∷
   rw 30 q7 ∷
   rw 29 q8 ∷
   rw 28 q8 ∷
   rw 27 q9 ∷
   rw 26 q8 ∷
   rw 25 q9 ∷
   rw 24 q9 ∷
   re 23 1 (ℓ "乏乆乏") ∷
   rw 25 q10 ∷
   rw 22 q9 ∷
   rw 21 q9 ∷
   rw 20 q9 ∷
   rw 19 q9 ∷
   rw 18 q9 ∷
   rw 17 q9 ∷
   rw 16 q11 ∷
   rw 15 q8 ∷
   rw 14 q9 ∷
   rw 13 q9 ∷
   rw 12 q9 ∷
   rw 11 q11 ∷
   rw 10 q8 ∷
   rw 9 q11 ∷
   rw 8 q8 ∷
   re 7 1 (ℓ "乏乆乏") ∷
   rw 9 q10 ∷
   re 6 1 (ℓ "乏乄乏") ∷
   rw 8 q10 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw 7 q10 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q10 ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw 5 q10 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q10 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q10 ∷
   rw 0 q7 ∷
   rw 1 q12 ∷
   rw 2 q6 ∷
   re 0 3 (ℓ "乑") ∷
   rw 3 q6 ∷
   re 1 3 (ℓ "中") ∷
   rw 4 q6 ∷
   re 2 3 (ℓ "中") ∷
   rw 5 q6 ∷
   re 3 3 (ℓ "乒") ∷
   rw 6 q6 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q6 ∷
   re 5 3 (ℓ "中") ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "乑") ∷
   rw 9 q6 ∷
   re 7 3 (ℓ "中") ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "乑") ∷
   rw 11 q6 ∷
   re 9 3 (ℓ "乑") ∷
   rw 12 q6 ∷
   re 10 3 (ℓ "乓") ∷
   rw⁻ 11 q8 ∷
   rw⁻ 12 q11 ∷
   rw⁻ 13 q8 ∷
   rw⁻ 14 q11 ∷
   rw⁻ 15 q9 ∷
   rw⁻ 16 q9 ∷
   rw⁻ 17 q9 ∷
   rw⁻ 18 q8 ∷
   rw⁻ 19 q11 ∷
   rw⁻ 20 q9 ∷
   rw⁻ 21 q9 ∷
   rw⁻ 22 q9 ∷
   rw⁻ 23 q9 ∷
   rw⁻ 24 q9 ∷
   rw⁻ 25 q9 ∷
   rw 28 q6 ∷
   re 26 3 (ℓ "乓") ∷
   rw⁻ 27 q9 ∷
   rw⁻ 28 q9 ∷
   rw⁻ 29 q8 ∷
   rw⁻ 30 q9 ∷
   rw⁻ 31 q8 ∷
   rw⁻ 32 q8 ∷
   rw 35 q6 ∷
   re 33 3 (ℓ "乑") ∷
   rw 36 q6 ∷
   re 34 3 (ℓ "中") ∷
   rw 37 q6 ∷
   re 35 3 (ℓ "中") ∷
   rw 38 q6 ∷
   re 36 3 (ℓ "乒") ∷
   rw 37 q10 ∷
   rw 33 q13 ∷
   rw 4 q14 ∷
   rw 0 q13 ∷
   rw 40 q6 ∷
   re 39 1 (ℓ "乏久乏") ∷
   rw 41 q10 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 40 q10 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q10 ∷
   re 36 1 (ℓ "乏乄乏") ∷
   rw 38 q10 ∷
   rw 35 q8 ∷
   rw 34 q8 ∷
   rw 33 q9 ∷
   rw 32 q8 ∷
   rw 31 q9 ∷
   rw 30 q9 ∷
   re 29 1 (ℓ "乏乆乏") ∷
   rw 31 q10 ∷
   rw 28 q9 ∷
   rw 27 q9 ∷
   rw 26 q9 ∷
   rw 25 q9 ∷
   rw 24 q9 ∷
   rw 23 q9 ∷
   rw 22 q11 ∷
   rw 21 q8 ∷
   rw 20 q9 ∷
   rw 19 q9 ∷
   rw 18 q9 ∷
   rw 17 q11 ∷
   rw 16 q8 ∷
   rw 15 q11 ∷
   rw 14 q8 ∷
   re 13 1 (ℓ "乏乆乏") ∷
   rw 15 q10 ∷
   re 12 1 (ℓ "乏乄乏") ∷
   rw 14 q10 ∷
   re 11 1 (ℓ "乏乄乏") ∷
   rw 13 q10 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q10 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw 11 q10 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q10 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q10 ∷
   re 6 1 (ℓ "乏久乏") ∷
   rw 8 q10 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q10 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q10 ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw 5 q10 ∷
   rw 4 q15 ∷
   rw⁻ 3 q7 ∷
   rw 6 q6 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q6 ∷
   re 5 3 (ℓ "中") ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "乑") ∷
   rw 9 q6 ∷
   re 7 3 (ℓ "中") ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "乑") ∷
   rw 11 q6 ∷
   re 9 3 (ℓ "乑") ∷
   rw 12 q6 ∷
   re 10 3 (ℓ "乓") ∷
   rw⁻ 11 q8 ∷
   rw⁻ 12 q11 ∷
   rw⁻ 13 q8 ∷
   rw⁻ 14 q11 ∷
   rw⁻ 15 q9 ∷
   rw⁻ 16 q9 ∷
   rw⁻ 17 q9 ∷
   rw⁻ 18 q8 ∷
   rw⁻ 19 q11 ∷
   rw⁻ 20 q9 ∷
   rw⁻ 21 q9 ∷
   rw⁻ 22 q9 ∷
   rw⁻ 23 q9 ∷
   rw⁻ 24 q9 ∷
   rw⁻ 25 q9 ∷
   rw 28 q6 ∷
   re 26 3 (ℓ "乓") ∷
   rw⁻ 27 q9 ∷
   rw⁻ 28 q9 ∷
   rw⁻ 29 q8 ∷
   rw⁻ 30 q9 ∷
   rw⁻ 31 q8 ∷
   rw⁻ 32 q8 ∷
   rw⁻ 33 q7 ∷
   rw 34 q10 ∷ []) Eq.refl
