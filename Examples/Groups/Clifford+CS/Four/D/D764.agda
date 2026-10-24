{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD764 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D764 (W : Ws) (Sᴰ : SD764) where

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
  lem-S2 : St 1778
  lem-S2 = pickᴰ 0 Sᴰ
  lem-S2-at0213 : St 1917
  lem-S2-at0213 = pickᴰ 1 Sᴰ
  lem-S2-at1023 : St 1918
  lem-S2-at1023 = pickᴰ 2 Sᴰ
  lem-pass-TOFF312-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : St 3059
  lem-pass-TOFF312-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = pickᴰ 3 Sᴰ
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : St 3060
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = pickᴰ 4 Sᴰ
  lem-merge3-at1023 : St 2909
  lem-merge3-at1023 = pickᴰ 5 Sᴰ
  lem-merge3-at1032 : St 2917
  lem-merge3-at1032 = pickᴰ 6 Sᴰ
  lem-merge3-at0321 : St 3058
  lem-merge3-at0321 = pickᴰ 7 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : St 3061
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = pickᴰ 8 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : St 3062
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = pickᴰ 9 Sᴰ
  lem-merge3-at0132 : St 3063
  lem-merge3-at0132 = pickᴰ 10 Sᴰ
  lem-merge3-at2013 : St 3064
  lem-merge3-at2013 = pickᴰ 11 Sᴰ

private
  q1 : Eqn
  q1 = eqn (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") (trans (by-assoc Eq.refl) (trans (ax lf) (by-assoc Eq.refl)))
  q2 : Eqn
  q2 = sE 3062 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1
  q3 : Eqn
  q3 = sE 3059 lem-pass-TOFF312-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1
  q4 : Eqn
  q4 = sE 3060 lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1
  q5 : Eqn
  q5 = sE 3061 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1

-- pass [CS01 CS01 CK10 CS01 CX12 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK30 CS02 CS02 CS02 S2 CK20 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 S2 S2 S2 S2 CK20 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS01 CS01 CS01 S1 CK10 CS01 CS01 CS01 CS01 CS01 CS01 S3 CK30] [X1 TOFF012 CS03 TOFF012 CSd03 X1]: 7 steps
lem-pass-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK30-CS02-CS02-CS02-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S3-CK30-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : ⟪ (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丒九中九丮丒") ⟫ʷ ≈ ⟪ (ℓ "丒九中九丮丒丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK30-CS02-CS02-CS02-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S3-CK30-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = derive (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丒九中九丮丒") (ℓ "丒九中九丮丒丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑")
  (rw 0 q1 ∷
   rw 62 q2 ∷
   rw 61 q3 ∷
   rw 30 q4 ∷
   rw 29 q3 ∷
   rw 0 q5 ∷
   rw⁻ 6 q1 ∷ []) Eq.refl

private
  q6 : Eqn
  q6 = sE 2909 lem-merge3-at1023

-- L87 merge-p 1023 3: 1 steps
lem-L87-merge-p-1023-3 : ⟪ (ℓ "习丽习举丞习丽习举丞") ⟫ʷ ≈ ⟪ (ℓ "丧乙") ⟫ʷ
lem-L87-merge-p-1023-3 = derive (ℓ "习丽习举丞习丽习举丞") (ℓ "丧乙")
  (rw 0 q6 ∷ []) Eq.refl

private
  q7 : Eqn
  q7 = sE 3064 lem-merge3-at2013

-- L87 merge-p 2013 3: 1 steps
lem-L87-merge-p-2013-3 : ⟪ (ℓ "乣义乣乊丞乣义乣乊丞") ⟫ʷ ≈ ⟪ (ℓ "丠乙") ⟫ʷ
lem-L87-merge-p-2013-3 = derive (ℓ "乣义乣乊丞乣义乣乊丞") (ℓ "丠乙")
  (rw 0 q7 ∷ []) Eq.refl

private
  q8 : Eqn
  q8 = sE 1778 lem-S2
  q9 : Eqn
  q9 = sE 3063 lem-merge3-at0132

-- L87 merge-p 0123 2: 3 steps
lem-L87-merge-p-0123-2 : ⟪ (ℓ "九中九丮丘九中九丮丘") ⟫ʷ ≈ ⟪ (ℓ "丽乚") ⟫ʷ
lem-L87-merge-p-0123-2 = derive (ℓ "九中九丮丘九中九丮丘") (ℓ "丽乚")
  (rw 0 q8 ∷
   rw 5 q8 ∷
   rw 0 q9 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = sE 1918 lem-S2-at1023
  q11 : Eqn
  q11 = sE 2917 lem-merge3-at1032

-- L87 merge-p 1023 2: 3 steps
lem-L87-merge-p-1023-2 : ⟪ (ℓ "习丽习举丘习丽习举丘") ⟫ʷ ≈ ⟪ (ℓ "中乚") ⟫ʷ
lem-L87-merge-p-1023-2 = derive (ℓ "习丽习举丘习丽习举丘") (ℓ "中乚")
  (rw 0 q10 ∷
   rw 5 q10 ∷
   rw 0 q11 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = sE 1917 lem-S2-at0213
  q13 : Eqn
  q13 = sE 3058 lem-merge3-at0321

-- L87 merge-p 0123 1: 3 steps
lem-L87-merge-p-0123-1 : ⟪ (ℓ "九中九丮丒九中九丮丒") ⟫ʷ ≈ ⟪ (ℓ "义乛") ⟫ʷ
lem-L87-merge-p-0123-1 = derive (ℓ "九中九丮丒九中九丮丒") (ℓ "义乛")
  (rw 0 q12 ∷
   rw 5 q12 ∷
   rw 0 q13 ∷ []) Eq.refl
