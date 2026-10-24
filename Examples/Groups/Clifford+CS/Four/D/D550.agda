{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD550 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D550 (W : Ws) (Sᴰ : SD550) where

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
  lem-Bar⟨SSSKSS32-⟶0⟩-passes-comm-WBar⟨SSKSKK~32-⟶1⟩ : St 928
  lem-Bar⟨SSSKSS32-⟶0⟩-passes-comm-WBar⟨SSKSKK~32-⟶1⟩ = pickᴰ 0 Sᴰ
  lem-Bar⟨SSSKSS32-⟶0⟩-passes-comm-WBar⟨SSSKSS~32-⟶1⟩ : St 929
  lem-Bar⟨SSSKSS32-⟶0⟩-passes-comm-WBar⟨SSSKSS~32-⟶1⟩ = pickᴰ 1 Sᴰ
  lem-Bar⟨SSSKSS32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩ : St 930
  lem-Bar⟨SSSKSS32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩ = pickᴰ 2 Sᴰ

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
  q9 = sE 930 lem-Bar⟨SSSKSS32-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~31-⟶0⟩
  q10 : Eqn
  q10 = wE 1570 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X3 CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10 X3]: 171 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X3 : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞") ⟫ʷ ≈ ⟪ (ℓ "丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X3 = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞") (ℓ "丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 62 q1 ∷
   rw 61 q2 ∷
   rw 60 q3 ∷
   rw 59 q3 ∷
   rw 58 q4 ∷
   rw 57 q3 ∷
   rw 56 q4 ∷
   rw 55 q4 ∷
   re 54 1 (ℓ "乏乆乏") ∷
   rw 56 q5 ∷
   rw 53 q4 ∷
   rw 52 q4 ∷
   rw 51 q4 ∷
   rw 50 q4 ∷
   rw 49 q4 ∷
   rw 48 q4 ∷
   rw 47 q6 ∷
   rw 46 q3 ∷
   rw 45 q4 ∷
   rw 44 q4 ∷
   rw 43 q4 ∷
   rw 42 q6 ∷
   rw 41 q3 ∷
   rw 40 q6 ∷
   rw 39 q3 ∷
   re 38 1 (ℓ "乏乆乏") ∷
   rw 40 q5 ∷
   re 37 1 (ℓ "乏乄乏") ∷
   rw 39 q5 ∷
   re 36 1 (ℓ "乏乄乏") ∷
   rw 38 q5 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q5 ∷
   re 34 1 (ℓ "乏乄乏") ∷
   rw 36 q5 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q5 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q5 ∷
   rw 31 q2 ∷
   rw 32 q7 ∷
   rw 31 q8 ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "中") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "乑") ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "中") ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "乑") ∷
   rw 39 q1 ∷
   re 37 3 (ℓ "乑") ∷
   rw 38 q8 ∷
   rw 39 q8 ∷
   rw 42 q1 ∷
   re 40 3 (ℓ "乓") ∷
   rw 41 q8 ∷
   rw⁻ 42 q3 ∷
   rw⁻ 43 q6 ∷
   rw⁻ 44 q3 ∷
   rw⁻ 45 q6 ∷
   rw⁻ 46 q4 ∷
   rw⁻ 47 q4 ∷
   rw⁻ 48 q4 ∷
   rw⁻ 49 q3 ∷
   rw⁻ 50 q6 ∷
   rw⁻ 51 q4 ∷
   rw⁻ 52 q4 ∷
   rw⁻ 53 q4 ∷
   rw⁻ 54 q4 ∷
   rw⁻ 55 q4 ∷
   rw⁻ 56 q4 ∷
   rw 57 q8 ∷
   rw 60 q1 ∷
   re 58 3 (ℓ "乓") ∷
   rw 59 q8 ∷
   rw⁻ 60 q4 ∷
   rw⁻ 61 q4 ∷
   rw⁻ 62 q3 ∷
   rw⁻ 63 q4 ∷
   rw⁻ 64 q3 ∷
   rw⁻ 65 q3 ∷
   rw 66 q5 ∷
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
  q12 = sE 929 lem-Bar⟨SSSKSS32-⟶0⟩-passes-comm-WBar⟨SSSKSS~32-⟶1⟩
  q13 : Eqn
  q13 = wE 1572 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X3 CS13 CS13 CS13 CK31 CS13 CS13 CX32 CS12 CS12 CS12 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CX32 CS12 CS12 CS12 CK21 CS12 CS12 X3]: 3 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS13-CS13-CS13-CK31-CS13-CS13-CX32-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CS12-CK21-CS12-CS12-X3 : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞丽丽丽乔丽丽乖丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乖丶丶丶乇丶丶丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽丽丽乔丽丽乖丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乖丶丶丶乇丶丶丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS13-CS13-CS13-CK31-CS13-CS13-CX32-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CS12-CK21-CS12-CS12-X3 = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞丽丽丽乔丽丽乖丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乖丶丶丶乇丶丶丞") (ℓ "丞丽丽丽乔丽丽乖丶丶丶丶丶丶乇且丶丶丶丶丶丶丶丶丶乖丶丶丶乇丶丶丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 31 q11 ∷
   rw 0 q12 ∷
   rw 0 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = wE 1573 W
  q15 : Eqn
  q15 = sE 928 lem-Bar⟨SSSKSS32-⟶0⟩-passes-comm-WBar⟨SSKSKK~32-⟶1⟩
  q16 : Eqn
  q16 = wE 1574 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X3 CS13 CS13 CK31 CS13 CK31 CK31 CX32 CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX32 CS12 CS12 CK21 CS12 CK21 CK21 X3]: 3 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX32-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CK21-CS12-CK21-CK21-X3 : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞丽丽乔丽乔乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽丽乔丽乔乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX32-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CK21-CS12-CK21-CK21-X3 = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞丽丽乔丽乔乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇丞") (ℓ "丞丽丽乔丽乔乔乖乇且乇且丶丶丶乇且丶丶丶丶丶丶乖丶丶乇丶乇乇丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 31 q14 ∷
   rw 0 q15 ∷
   rw 0 q16 ∷ []) Eq.refl
