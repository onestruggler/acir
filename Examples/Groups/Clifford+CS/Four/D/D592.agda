{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD592 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D592 (W : Ws) (Sᴰ : SD592) where

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
  lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 841
  lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 0 Sᴰ
  lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : St 879
  lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 1 Sᴰ
  lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03 : St 851
  lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 2 Sᴰ
  lem-pass-X2-CSd20-X2-vs-TOFF012-CS03-TOFF012-CSd03 : St 870
  lem-pass-X2-CSd20-X2-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 3 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30 : St 1059
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30 = pickᴰ 4 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03 : St 1060
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03 = pickᴰ 5 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-TOFF312 : St 1061
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-TOFF312 = pickᴰ 6 Sᴰ
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02 : St 1062
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02 = pickᴰ 7 Sᴰ
  lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩ : St 1063
  lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩ = pickᴰ 8 Sᴰ
  lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩ : St 1064
  lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩ = pickᴰ 9 Sᴰ
  lem-pass-CK30-vs-CCZ123 : St 1065
  lem-pass-CK30-vs-CCZ123 = pickᴰ 10 Sᴰ
  lem-pass-CK30-vs-CSd23 : St 1066
  lem-pass-CK30-vs-CSd23 = pickᴰ 11 Sᴰ
  lem-pass-CKd30-vs-CCZ123 : St 1067
  lem-pass-CKd30-vs-CCZ123 = pickᴰ 12 Sᴰ
  lem-pass-CKd30-vs-CSd23 : St 1068
  lem-pass-CKd30-vs-CSd23 = pickᴰ 13 Sᴰ
  lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-X0-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-X0 : St 1069
  lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-X0-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-X0 = pickᴰ 14 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-vs-CCZ123 : St 1070
  lem-pass-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-vs-CCZ123 = pickᴰ 15 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-vs-CSd23 : St 1071
  lem-pass-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-vs-CSd23 = pickᴰ 16 Sᴰ
  lem-pass-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-vs-CCZ123 : St 1072
  lem-pass-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-vs-CCZ123 = pickᴰ 17 Sᴰ
  lem-pass-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-vs-CSd23 : St 1073
  lem-pass-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-vs-CSd23 = pickᴰ 18 Sᴰ
  lem-pass-X3-CK30-X3-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : St 1074
  lem-pass-X3-CK30-X3-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = pickᴰ 19 Sᴰ

private
  q1 : Eqn
  q1 = eqn (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") (trans (by-assoc Eq.refl) (trans (ax lf) (by-assoc Eq.refl)))
  q2 : Eqn
  q2 = wE 1700 W
  q3 : Eqn
  q3 = sE 1061 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-TOFF312
  q4 : Eqn
  q4 = sE 1060 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03
  q5 : Eqn
  q5 = sE 1059 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20] [CS01 CS01 CK10 CS01 CX12 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK30 CS02 CS02 CS02 S2 CK20 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 S2 S2 S2 S2 CK20 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS01 CS01 CS01 S1 CK10 CS01 CS01 CS01 CS01 CS01 CS01 S3 CK30]: 7 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK30-CS02-CS02-CS02-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S3-CK30 : ⟪ (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") ⟫ʷ ≈ ⟪ (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK30-CS02-CS02-CS02-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-S2-CK20-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S3-CK30 = derive (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄")
  (rw 29 q1 ∷
   rw 0 q2 ∷
   rw 29 q3 ∷
   rw 30 q4 ∷
   rw 61 q3 ∷
   rw 62 q5 ∷
   rw⁻ 0 q1 ∷ []) Eq.refl

private
  q6 : Eqn
  q6 = wE 231 W
  q7 : Eqn
  q7 = wE 1692 W
  q8 : Eqn
  q8 = wE 1705 W
  q9 : Eqn
  q9 = wE 1706 W
  q10 : Eqn
  q10 = wE 1694 W
  q11 : Eqn
  q11 = wE 1695 W
  q12 : Eqn
  q12 = sE 1062 lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02
  q13 : Eqn
  q13 = wE 1342 W
  q14 : Eqn
  q14 = wE 1696 W
  q15 : Eqn
  q15 = wE 1707 W
  q16 : Eqn
  q16 = wE 1708 W
  q17 : Eqn
  q17 = wE 1698 W
  q18 : Eqn
  q18 = wE 1699 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03] [CS01 CS01 CK10 CS01 CX12 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02] ^inv: 43 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-ᵖinv : ⟪ (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丨久丨丨丹丨丨丨丨丨丨丕久丨丨丨丹両丵両両") ⟫ʷ ≈ ⟪ (ℓ "丨久丨丨丹丨丨丨丨丨丨丕久丨丨丨丹両丵両両丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-ᵖinv = derive (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丨久丨丨丹丨丨丨丨丨丨丕久丨丨丨丹両丵両両") (ℓ "丨久丨丨丹丨丨丨丨丨丨丕久丨丨丨丹両丵両両丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中")
  (rw 0 q6 ∷
   rw 1 q7 ∷
   rw 2 q6 ∷
   rw 3 q6 ∷
   rw 4 q8 ∷
   rw 5 q6 ∷
   rw 6 q6 ∷
   rw 7 q6 ∷
   rw 8 q6 ∷
   rw 9 q6 ∷
   rw 10 q6 ∷
   rw 11 q9 ∷
   rw 12 q7 ∷
   rw 13 q6 ∷
   rw 14 q6 ∷
   rw 15 q6 ∷
   rw 16 q8 ∷
   rw 17 q10 ∷
   rw 18 q11 ∷
   rw 19 q10 ∷
   rw 20 q10 ∷
   rw⁻ 21 q12 ∷
   rw 72 q13 ∷
   rw 71 q14 ∷
   rw 70 q13 ∷
   rw 69 q13 ∷
   rw 68 q15 ∷
   rw 67 q13 ∷
   rw 66 q13 ∷
   rw 65 q13 ∷
   rw 64 q13 ∷
   rw 63 q13 ∷
   rw 62 q13 ∷
   rw 61 q16 ∷
   rw 60 q14 ∷
   rw 59 q13 ∷
   rw 58 q13 ∷
   rw 57 q13 ∷
   rw 56 q15 ∷
   rw 55 q17 ∷
   rw 54 q18 ∷
   rw 53 q17 ∷
   rw 52 q17 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = wE 1 W
  q20 : Eqn
  q20 = wE 3 W
  q21 : Eqn
  q21 = wE 1709 W
  q22 : Eqn
  q22 = eqn (ℓ "下乏") (ℓ "乏下") (low₁-comm ((K • iI)) ((Swap ↑)))
  q23 : Eqn
  q23 = wE 175 W
  q24 : Eqn
  q24 = sE 1074 lem-pass-X3-CK30-X3-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1
  q25 : Eqn
  q25 = eqn (ℓ "下丒") (ℓ "丒下") (low₁-comm ((K • iI)) (X))
  q26 : Eqn
  q26 = wE 1710 W
  q27 : Eqn
  q27 = wE 116 W
  q28 : Eqn
  q28 = wE 173 W
  q29 : Eqn
  q29 = wE 1711 W

-- CA CKd30 Gad(t=0, W=(1,), d=1, e=1): 25 steps
lem-CA-CKd30-Gad⟨t≡0-W≡⟨1⟩-d≡1-e≡1⟩ : ⟪ (ℓ "乒丒九中九丮丒") ⟫ʷ ≈ ⟪ (ℓ "丒下九中九丮上丒乒") ⟫ʷ
lem-CA-CKd30-Gad⟨t≡0-W≡⟨1⟩-d≡1-e≡1⟩ = derive (ℓ "乒丒九中九丮丒") (ℓ "丒下九中九丮上丒乒")
  (rw 1 q19 ∷
   re 0 1 (ℓ "乏久乏") ∷
   rw 2 q20 ∷
   rw 1 q21 ∷
   rw⁻ 0 q22 ∷
   rw 1 q23 ∷
   rw 4 q19 ∷
   re 2 3 (ℓ "乑") ∷
   rw 3 q23 ∷
   rw 4 q20 ∷
   rw 1 q24 ∷
   rw 0 q25 ∷
   rw 1 q26 ∷
   rw 6 q27 ∷
   rw 7 q25 ∷
   rw 12 q19 ∷
   rw 11 q28 ∷
   re 10 1 (ℓ "乏乄乏") ∷
   rw 12 q20 ∷
   rw 9 q28 ∷
   rw 8 q22 ∷
   rw 9 q29 ∷
   rw 10 q19 ∷
   re 8 3 (ℓ "乒") ∷
   rw 9 q20 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q31 : Eqn
  q31 = wE 1676 W
  q32 : Eqn
  q32 = wE 1712 W
  q33 : Eqn
  q33 = sE 841 lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q34 : Eqn
  q34 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q35 : Eqn
  q35 = wE 1713 W

-- pass [X3 CKd30 X3] [X1 Kd0 TOFF012 CS03 TOFF012 CSd03 K0 X1]: 53 steps
lem-pass-X3-CKd30-X3-vs-X1-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-X1 : ⟪ (ℓ "丞乒丞丒下九中九丮上丒") ⟫ʷ ≈ ⟪ (ℓ "丒下九中九丮上丒丞乒丞") ⟫ʷ
lem-pass-X3-CKd30-X3-vs-X1-Kd0-TOFF012-CS03-TOFF012-CSd03-K0-X1 = derive (ℓ "丞乒丞丒下九中九丮上丒") (ℓ "丒下九中九丮上丒丞乒丞")
  (rw 4 q19 ∷
   rw 3 q30 ∷
   rw 2 q28 ∷
   re 1 1 (ℓ "乏久乏") ∷
   rw 3 q20 ∷
   rw 0 q28 ∷
   rw 1 q31 ∷
   rw⁻ 0 q30 ∷
   rw 1 q23 ∷
   rw 4 q19 ∷
   re 2 3 (ℓ "乒") ∷
   rw 3 q23 ∷
   rw 4 q20 ∷
   rw 5 q19 ∷
   rw 4 q22 ∷
   rw 3 q28 ∷
   re 2 1 (ℓ "乏久乏") ∷
   rw 4 q20 ∷
   rw 1 q28 ∷
   rw 2 q32 ∷
   rw⁻ 1 q22 ∷
   rw 2 q23 ∷
   rw 5 q19 ∷
   re 3 3 (ℓ "乒") ∷
   rw 4 q23 ∷
   rw 5 q20 ∷
   rw 2 q33 ∷
   rw 10 q19 ∷
   rw 9 q34 ∷
   rw 8 q28 ∷
   re 7 1 (ℓ "乏久乏") ∷
   rw 9 q20 ∷
   rw 6 q28 ∷
   rw 7 q35 ∷
   rw⁻ 6 q34 ∷
   rw 7 q23 ∷
   rw 10 q19 ∷
   re 8 3 (ℓ "乒") ∷
   rw 9 q23 ∷
   rw 10 q20 ∷
   rw 11 q19 ∷
   rw 10 q30 ∷
   rw 9 q28 ∷
   re 8 1 (ℓ "乏久乏") ∷
   rw 10 q20 ∷
   rw 7 q28 ∷
   rw 8 q31 ∷
   rw⁻ 7 q30 ∷
   rw 8 q23 ∷
   rw 11 q19 ∷
   re 9 3 (ℓ "乒") ∷
   rw 10 q23 ∷
   rw 11 q20 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = wE 1714 W
  q37 : Eqn
  q37 = sE 879 lem-pass-X1-CS10-X1-vs-TOFF012-CS03-TOFF012-CSd03
  q38 : Eqn
  q38 = wE 1715 W

-- pass [CS10] [X1 TOFF012 CS03 TOFF012 CSd03 X1]: 3 steps
lem-pass-CS10-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : ⟪ (ℓ "丠丒九中九丮丒") ⟫ʷ ≈ ⟪ (ℓ "丒九中九丮丒丠") ⟫ʷ
lem-pass-CS10-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = derive (ℓ "丠丒九中九丮丒") (ℓ "丒九中九丮丒丠")
  (rw 0 q36 ∷
   rw 1 q37 ∷
   rw 5 q38 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = wE 1682 W
  q40 : Eqn
  q40 = wE 1490 W
  q41 : Eqn
  q41 = sE 851 lem-pass-X2-CS20-X2-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [X2 CS20 X2] [X1 TOFF012 CS03 TOFF012 CSd03 X1]: 5 steps
lem-pass-X2-CS20-X2-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 : ⟪ (ℓ "丘丧丘丒九中九丮丒") ⟫ʷ ≈ ⟪ (ℓ "丒九中九丮丒丘丧丘") ⟫ʷ
lem-pass-X2-CS20-X2-vs-X1-TOFF012-CS03-TOFF012-CSd03-X1 = derive (ℓ "丘丧丘丒九中九丮丒") (ℓ "丒九中九丮丒丘丧丘")
  (rw 0 q39 ∷
   rw 1 q40 ∷
   rw 1 q41 ∷
   rw 5 q40 ∷
   rw 5 q39 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = wE 1681 W
  q43 : Eqn
  q43 = wE 1667 W
  q44 : Eqn
  q44 = sE 870 lem-pass-X2-CSd20-X2-vs-TOFF012-CS03-TOFF012-CSd03
  q45 : Eqn
  q45 = wE 1668 W

-- pass [X2 CSd20 X2] [X1 Sd0 TOFF012 CS03 TOFF012 CSd03 S0 X1]: 5 steps
lem-pass-X2-CSd20-X2-vs-X1-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X1 : ⟪ (ℓ "丘丨丘丒三九中九丮丈丒") ⟫ʷ ≈ ⟪ (ℓ "丒三九中九丮丈丒丘丨丘") ⟫ʷ
lem-pass-X2-CSd20-X2-vs-X1-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-X1 = derive (ℓ "丘丨丘丒三九中九丮丈丒") (ℓ "丒三九中九丮丈丒丘丨丘")
  (rw 0 q42 ∷
   rw 1 q43 ∷
   rw 2 q44 ∷
   rw 6 q45 ∷
   rw 7 q42 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = wE 1716 W
  q47 : Eqn
  q47 = wE 464 W
  q48 : Eqn
  q48 = wE 1163 W
  q49 : Eqn
  q49 = sE 1067 lem-pass-CKd30-vs-CCZ123
  q50 : Eqn
  q50 = sE 1068 lem-pass-CKd30-vs-CSd23
  q51 : Eqn
  q51 = sE 1072 lem-pass-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-vs-CCZ123
  q52 : Eqn
  q52 = sE 1073 lem-pass-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-vs-CSd23
  q53 : Eqn
  q53 = sE 1065 lem-pass-CK30-vs-CCZ123
  q54 : Eqn
  q54 = sE 1066 lem-pass-CK30-vs-CSd23
  q55 : Eqn
  q55 = sE 1070 lem-pass-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-vs-CCZ123
  q56 : Eqn
  q56 = sE 1071 lem-pass-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-vs-CSd23
  q57 : Eqn
  q57 = wE 1717 W
  q58 : Eqn
  q58 = wE 1718 W
  q59 : Eqn
  q59 = wE 151 W

-- HD passes D: 26 steps
lem-HD-passes-D : ⟪ (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑乜乊") ⟫ʷ ≈ ⟪ (ℓ "乜乊丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") ⟫ʷ
lem-HD-passes-D = derive (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑乜乊") (ℓ "乜乊丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑")
  (rw 22 q46 ∷
   rw 80 q19 ∷
   re 79 1 (ℓ "乏乄乏") ∷
   rw 81 q20 ∷
   rw 78 q47 ∷
   rw 79 q48 ∷
   rw 80 q19 ∷
   re 78 3 (ℓ "乒") ∷
   rw 79 q20 ∷
   rw 78 q49 ∷
   rw 79 q50 ∷
   rw 22 q51 ∷
   rw 23 q52 ∷
   rw 21 q53 ∷
   rw 22 q54 ∷
   rw 0 q55 ∷
   rw 1 q56 ∷
   rw 24 q57 ∷
   rw 81 q19 ∷
   re 80 1 (ℓ "乏久乏") ∷
   rw 82 q20 ∷
   rw 81 q58 ∷
   rw 80 q59 ∷
   rw 83 q19 ∷
   re 81 3 (ℓ "乑") ∷
   rw 82 q20 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = wE 1719 W
  q61 : Eqn
  q61 = sE 1063 lem-Bar⟨SSKSKK13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩
  q62 : Eqn
  q62 = wE 1720 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [X1 CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20 X1]: 3 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X1 : ⟪ (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒") ⟫ʷ ≈ ⟪ (ℓ "丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X1 = derive (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒") (ℓ "丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑")
  (rw 29 q60 ∷
   rw 0 q61 ∷
   rw 0 q62 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = sE 1064 lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03] [X1 CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20 X1]: 3 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X1 : ⟪ (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒") ⟫ʷ ≈ ⟪ (ℓ "丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-X1 = derive (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒") (ℓ "丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中")
  (rw 31 q60 ∷
   rw 0 q63 ∷
   rw 0 q62 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = sE 1069 lem-pass-CS01-CS01-CK01-CS01-CK01-CK01-CX03-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX03-CS13-CS13-CK31-CS13-CK31-CK31-vs-X0-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-X0

-- Bar(SSKSKK;0,3->1) passes factors of X0 CS01 CS01 CK01 CS01 CK01 CK01 CX02 CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX02 CS12 CS12 CK21 CS12 CK21 CK21 X0: 1 steps
lem-Bar⟨SSKSKK03-⟶1⟩-passes-factors-of-X0-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-X0 : ⟪ (ℓ "丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔丌丠丠两丠两两个乇且乇且丶丶丶乇且丶丶丶丶丶丶个丶丶乇丶乇乇丌") ⟫ʷ ≈ ⟪ (ℓ "丌丠丠两丠两两个乇且乇且丶丶丶乇且丶丶丶丶丶丶个丶丶乇丶乇乇丌丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔") ⟫ʷ
lem-Bar⟨SSKSKK03-⟶1⟩-passes-factors-of-X0-CS01-CS01-CK01-CS01-CK01-CK01-CX02-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK21-CK21-X0 = derive (ℓ "丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔丌丠丠两丠两两个乇且乇且丶丶丶乇且丶丶丶丶丶丶个丶丶乇丶乇乇丌") (ℓ "丌丠丠两丠两两个乇且乇且丶丶丶乇且丶丶丶丶丶丶个丶丶乇丶乇乇丌丠丠两丠两两丰乔业乔业丽丽丽乔业丽丽丽丽丽丽丰丽丽乔丽乔乔")
  (rw 0 q64 ∷ []) Eq.refl
