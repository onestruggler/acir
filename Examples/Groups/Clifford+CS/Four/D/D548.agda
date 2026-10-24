{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD548 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D548 (W : Ws) (Sᴰ : SD548) where

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
  lem-pass-CCZ123-vs-CCZ023 : St 922
  lem-pass-CCZ123-vs-CCZ023 = pickᴰ 0 Sᴰ
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-white-iX-via-V2-conjugates-2 : St 923
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-white-iX-via-V2-conjugates-2 = pickᴰ 1 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-comm-WBar⟨SSKSKK~32-⟶1⟩ : St 924
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-comm-WBar⟨SSKSKK~32-⟶1⟩ = pickᴰ 2 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-comm-WBar⟨SSSKSS~32-⟶1⟩ : St 925
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-comm-WBar⟨SSSKSS~32-⟶1⟩ = pickᴰ 3 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩ : St 926
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩ = pickᴰ 4 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 173 W
  q3 : Eqn
  q3 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q4 : Eqn
  q4 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q7 : Eqn
  q7 = wE 1569 W
  q8 : Eqn
  q8 = wE 175 W
  q9 : Eqn
  q9 = sE 926 lem-Bar⟨SSKSKK32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩
  q10 : Eqn
  q10 = wE 1570 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10 X3]: 171 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞") ⟫ʷ ≈ ⟪ (ℓ "丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞") (ℓ "丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 60 q1 ∷
   rw 59 q2 ∷
   rw 58 q3 ∷
   rw 57 q3 ∷
   rw 56 q4 ∷
   rw 55 q3 ∷
   rw 54 q4 ∷
   rw 53 q4 ∷
   re 52 1 (ℓ "乏乆乏") ∷
   rw 54 q5 ∷
   rw 51 q4 ∷
   rw 50 q4 ∷
   rw 49 q4 ∷
   rw 48 q4 ∷
   rw 47 q4 ∷
   rw 46 q4 ∷
   rw 45 q6 ∷
   rw 44 q3 ∷
   rw 43 q4 ∷
   rw 42 q4 ∷
   rw 41 q4 ∷
   rw 40 q6 ∷
   rw 39 q3 ∷
   rw 38 q6 ∷
   rw 37 q3 ∷
   re 36 1 (ℓ "乏乆乏") ∷
   rw 38 q5 ∷
   re 35 1 (ℓ "乏乄乏") ∷
   rw 37 q5 ∷
   re 34 1 (ℓ "乏乄乏") ∷
   rw 36 q5 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q5 ∷
   re 32 1 (ℓ "乏乄乏") ∷
   rw 34 q5 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q5 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q5 ∷
   rw 29 q2 ∷
   rw 30 q7 ∷
   rw 29 q8 ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "中") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "中") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "乑") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "中") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "乑") ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "乑") ∷
   rw 36 q8 ∷
   rw 37 q8 ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "乓") ∷
   rw 39 q8 ∷
   rw⁻ 40 q3 ∷
   rw⁻ 41 q6 ∷
   rw⁻ 42 q3 ∷
   rw⁻ 43 q6 ∷
   rw⁻ 44 q4 ∷
   rw⁻ 45 q4 ∷
   rw⁻ 46 q4 ∷
   rw⁻ 47 q3 ∷
   rw⁻ 48 q6 ∷
   rw⁻ 49 q4 ∷
   rw⁻ 50 q4 ∷
   rw⁻ 51 q4 ∷
   rw⁻ 52 q4 ∷
   rw⁻ 53 q4 ∷
   rw⁻ 54 q4 ∷
   rw 55 q8 ∷
   rw 58 q1 ∷
   re 56 3 (ℓ "乓") ∷
   rw 57 q8 ∷
   rw⁻ 58 q4 ∷
   rw⁻ 59 q4 ∷
   rw⁻ 60 q3 ∷
   rw⁻ 61 q4 ∷
   rw⁻ 62 q3 ∷
   rw⁻ 63 q3 ∷
   rw 64 q5 ∷
   rw 0 q9 ∷
   rw 35 q1 ∷
   rw 34 q3 ∷
   rw 33 q3 ∷
   rw 32 q4 ∷
   rw 31 q3 ∷
   rw 30 q4 ∷
   rw 29 q4 ∷
   rw 28 q2 ∷
   re 27 1 (ℓ "乏乆乏") ∷
   rw 29 q5 ∷
   rw 26 q2 ∷
   rw 25 q4 ∷
   rw 24 q4 ∷
   rw 23 q4 ∷
   rw 22 q4 ∷
   rw 21 q4 ∷
   rw 20 q4 ∷
   rw 19 q6 ∷
   rw 18 q3 ∷
   rw 17 q4 ∷
   rw 16 q4 ∷
   rw 15 q4 ∷
   rw 14 q6 ∷
   rw 13 q3 ∷
   rw 12 q6 ∷
   rw 11 q3 ∷
   rw 10 q2 ∷
   re 9 1 (ℓ "乏乆乏") ∷
   rw 11 q5 ∷
   rw 8 q2 ∷
   rw 7 q2 ∷
   re 6 1 (ℓ "乏乄乏") ∷
   rw 8 q5 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw 7 q5 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw 5 q5 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q5 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q5 ∷
   rw 0 q2 ∷
   rw 1 q10 ∷
   rw 0 q8 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "中") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "中") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "乑") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "乑") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乑") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "乓") ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q6 ∷
   rw⁻ 10 q3 ∷
   rw⁻ 11 q6 ∷
   rw⁻ 12 q4 ∷
   rw⁻ 13 q4 ∷
   rw⁻ 14 q4 ∷
   rw⁻ 15 q3 ∷
   rw⁻ 16 q6 ∷
   rw⁻ 17 q4 ∷
   rw⁻ 18 q4 ∷
   rw⁻ 19 q4 ∷
   rw⁻ 20 q4 ∷
   rw⁻ 21 q4 ∷
   rw⁻ 22 q4 ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "乓") ∷
   rw⁻ 24 q4 ∷
   rw⁻ 25 q4 ∷
   rw⁻ 26 q3 ∷
   rw⁻ 27 q4 ∷
   rw⁻ 28 q3 ∷
   rw⁻ 29 q3 ∷
   rw 30 q8 ∷
   rw 31 q5 ∷ []) Eq.refl

private
  q11 : Eqn
  q11 = wE 1571 W
  q12 : Eqn
  q12 = sE 925 lem-Bar⟨SSKSKK32-⟶0⟩-passes-comm-WBar⟨SSSKSS~32-⟶1⟩
  q13 : Eqn
  q13 = wE 1572 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 CS13 CS13 CS13 CK31 CS13 CS13 CX32 CS12 CS12 CS12 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CX32 CS12 CS12 CS12 CK21 CS12 CS12 X3]: 3 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-CS13-CS13-CK31-CS13-CS13-CX32-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CS12-CK21-CS12-CS12-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丽丽丽乔丽丽乖丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乖丶丶丶乇丶丶丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽丽丽乔丽丽乖丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乖丶丶丶乇丶丶丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-CS13-CS13-CK31-CS13-CS13-CX32-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CS12-CK21-CS12-CS12-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丽丽丽乔丽丽乖丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乖丶丶丶乇丶丶丞") (ℓ "丞丽丽丽乔丽丽乖丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乖丶丶丶乇丶丶丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 29 q11 ∷
   rw 0 q12 ∷
   rw 0 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = wE 1573 W
  q15 : Eqn
  q15 = sE 924 lem-Bar⟨SSKSKK32-⟶0⟩-passes-comm-WBar⟨SSKSKK~32-⟶1⟩
  q16 : Eqn
  q16 = wE 1574 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 CS13 CS13 CK31 CS13 CK31 CK31 CX32 CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX32 CS12 CS12 CK21 CS12 CK21 CK21 X3]: 3 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX32-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CK21-CS12-CK21-CK21-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丽丽乔丽乔乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽丽乔丽乔乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX32-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CK21-CS12-CK21-CK21-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞丽丽乔丽乔乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇丞") (ℓ "丞丽丽乔丽乔乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 29 q14 ∷
   rw 0 q15 ∷
   rw 0 q16 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = wE 1575 W
  q18 : Eqn
  q18 = sE 923 lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-white-iX-via-V2-conjugates-2
  q19 : Eqn
  q19 = wE 1576 W

-- pass [CS13 CS13 CK31 CS13 CK31 CK31 CX30 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX30 CS01 CS01 CK01 CS01 CK01 CK01] [X3 TOFF123 X3]: 3 steps
lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-TOFF123-X3 : ⟪ (ℓ "丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两丞乢丞") ⟫ʷ ≈ ⟪ (ℓ "丞乢丞丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两") ⟫ʷ
lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-TOFF123-X3 = derive (ℓ "丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两丞乢丞") (ℓ "丞乢丞丽丽乔丽乔乔乐两丈两丈丠丠丠两丈丠丠丠丠丠丠乐丠丠两丠两两")
  (rw 29 q17 ∷
   rw 0 q18 ∷
   rw 0 q19 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = sE 922 lem-pass-CCZ123-vs-CCZ023

-- pass [CCZ023] [CCZ123]: 1 steps
lem-pass-CCZ023-vs-CCZ123 : ⟪ (ℓ "乛乜") ⟫ʷ ≈ ⟪ (ℓ "乜乛") ⟫ʷ
lem-pass-CCZ023-vs-CCZ123 = derive (ℓ "乛乜") (ℓ "乜乛")
  (rw⁻ 0 q20 ∷ []) Eq.refl
