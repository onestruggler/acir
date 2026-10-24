{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD667 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D667 (W : Ws) (Sᴰ : SD667) where

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
  lem-Xᵖ3 : St 1769
  lem-Xᵖ3 = pickᴰ 0 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20 : St 1053
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20 = pickᴰ 1 Sᴰ
  lem-X-P1--⟶-P1-X : St 1770
  lem-X-P1--⟶-P1-X = pickᴰ 2 Sᴰ
  lem-X-P3--⟶-P3-X : St 1771
  lem-X-P3--⟶-P3-X = pickᴰ 3 Sᴰ
  lem-pass-CCZ023-vs-TOFF013-CS02-TOFF013-CSd02 : St 1772
  lem-pass-CCZ023-vs-TOFF013-CS02-TOFF013-CSd02 = pickᴰ 4 Sᴰ
  lem-pass-CZ23-CCZ123-vs-TOFF012-CS03-TOFF012-CSd03 : St 1773
  lem-pass-CZ23-CCZ123-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 5 Sᴰ

private
  q1 : Eqn
  q1 = eqn (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") (trans (by-assoc Eq.refl) (trans (ax lf) (by-assoc Eq.refl)))
  q2 : Eqn
  q2 = sE 1053 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20
  q3 : Eqn
  q3 = sE 1770 lem-X-P1--⟶-P1-X
  q4 : Eqn
  q4 = sE 1771 lem-X-P3--⟶-P3-X
  q5 : Eqn
  q5 = wE 2007 W
  q6 : Eqn
  q6 = sE 1769 lem-Xᵖ3
  q7 : Eqn
  q7 = wE 1 W
  q8 : Eqn
  q8 = wE 3 W
  q9 : Eqn
  q9 = wE 464 W
  q10 : Eqn
  q10 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q11 : Eqn
  q11 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q12 : Eqn
  q12 = wE 2008 W

-- top HD^3: 167 steps
lem-top-HDᵖ3 : ⟪ (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-top-HDᵖ3 = derive (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") []
  (rw 0 q1 ∷
   rw 91 q1 ∷
   rw 182 q1 ∷
   rw 62 q2 ∷
   rw 29 q3 ∷
   rw⁻ 91 q4 ∷
   rw 153 q2 ∷
   rw 124 q2 ∷
   rw 91 q3 ∷
   rw 58 q3 ∷
   rw⁻ 182 q4 ∷
   rw⁻ 153 q4 ∷
   rw 0 q5 ∷
   rw 1 q6 ∷
   rw 90 q7 ∷
   re 89 1 (ℓ "乏乄乏") ∷
   rw 91 q8 ∷
   re 88 1 (ℓ "乏乄乏") ∷
   rw 90 q8 ∷
   re 87 1 (ℓ "乏丧乏") ∷
   rw 89 q8 ∷
   re 86 1 (ℓ "乏乄乏") ∷
   rw 88 q8 ∷
   re 85 1 (ℓ "乏丧乏") ∷
   rw 87 q8 ∷
   re 84 1 (ℓ "乏丧乏") ∷
   rw 86 q8 ∷
   re 83 1 (ℓ "乏丹乏") ∷
   rw 85 q8 ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw 84 q8 ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw 83 q8 ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw 82 q8 ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw 81 q8 ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw 80 q8 ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 79 q8 ∷
   rw 76 q9 ∷
   re 75 1 (ℓ "乏乄乏") ∷
   rw 77 q8 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 76 q8 ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw 75 q8 ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw 74 q8 ∷
   rw 71 q9 ∷
   re 70 1 (ℓ "乏乄乏") ∷
   rw 72 q8 ∷
   rw 69 q9 ∷
   re 68 1 (ℓ "乏乄乏") ∷
   rw 70 q8 ∷
   re 67 1 (ℓ "乏丹乏") ∷
   rw 69 q8 ∷
   rw 66 q10 ∷
   rw 65 q10 ∷
   rw 64 q11 ∷
   rw 63 q10 ∷
   rw 62 q11 ∷
   rw 61 q11 ∷
   re 60 1 (ℓ "乏乄乏") ∷
   rw 62 q8 ∷
   re 59 1 (ℓ "乏乄乏") ∷
   rw 61 q8 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 60 q8 ∷
   re 57 1 (ℓ "乏乄乏") ∷
   rw 59 q8 ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw 58 q8 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q8 ∷
   re 54 1 (ℓ "乏丹乏") ∷
   rw 56 q8 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q8 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q8 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q8 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q8 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q8 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 50 q8 ∷
   rw 47 q9 ∷
   re 46 1 (ℓ "乏乄乏") ∷
   rw 48 q8 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q8 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q8 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q8 ∷
   rw 42 q9 ∷
   re 41 1 (ℓ "乏乄乏") ∷
   rw 43 q8 ∷
   rw 40 q9 ∷
   re 39 1 (ℓ "乏乄乏") ∷
   rw 41 q8 ∷
   re 38 1 (ℓ "乏丹乏") ∷
   rw 40 q8 ∷
   rw 37 q10 ∷
   rw 36 q10 ∷
   rw 35 q11 ∷
   rw 34 q10 ∷
   rw 33 q11 ∷
   rw 32 q11 ∷
   re 31 1 (ℓ "乏乄乏") ∷
   rw 33 q8 ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw 32 q8 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q8 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q8 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q8 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q8 ∷
   re 25 1 (ℓ "乏丹乏") ∷
   rw 27 q8 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q8 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q8 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q8 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q8 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q8 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q8 ∷
   rw 18 q9 ∷
   re 17 1 (ℓ "乏乄乏") ∷
   rw 19 q8 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q8 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q8 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q8 ∷
   rw 13 q9 ∷
   re 12 1 (ℓ "乏乄乏") ∷
   rw 14 q8 ∷
   rw 11 q9 ∷
   re 10 1 (ℓ "乏乄乏") ∷
   rw 12 q8 ∷
   re 9 1 (ℓ "乏丹乏") ∷
   rw 11 q8 ∷
   rw 8 q10 ∷
   rw 7 q10 ∷
   rw 6 q11 ∷
   rw 5 q10 ∷
   rw 4 q11 ∷
   rw 3 q11 ∷
   rw 4 q5 ∷
   rw 5 q7 ∷
   re 3 3 (ℓ "丿") ∷
   rw 4 q8 ∷
   rw 0 q12 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = sE 1772 lem-pass-CCZ023-vs-TOFF013-CS02-TOFF013-CSd02

-- pass [TOFF013 CS02 TOFF013 CSd02] [CCZ023]: 1 steps
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-CCZ023 : ⟪ (ℓ "乞丧乞丨乛") ⟫ʷ ≈ ⟪ (ℓ "乛乞丧乞丨") ⟫ʷ
lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-CCZ023 = derive (ℓ "乞丧乞丨乛") (ℓ "乛乞丧乞丨")
  (rw⁻ 0 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = sE 1773 lem-pass-CZ23-CCZ123-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [TOFF012 CS03 TOFF012 CSd03] [CZ23 CCZ123]: 1 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CZ23-CCZ123 : ⟪ (ℓ "九中九丮之乜") ⟫ʷ ≈ ⟪ (ℓ "之乜九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CZ23-CCZ123 = derive (ℓ "九中九丮之乜") (ℓ "之乜九中九丮")
  (rw⁻ 0 q14 ∷ []) Eq.refl
