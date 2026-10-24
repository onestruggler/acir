{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)

module Examples.Groups.Clifford+CS.Five.D.D003 where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

private
  q1 : Ws → Eqn
  q1 c4 = wpE 1068 c4
  q2 : Ws → Eqn
  q2 c4 = wlE 1379 (lit c4)

-- sym-ab @0310213442: 18 steps
lem-sym-ab-at0310213442 : Ws → ⟪ (ℓ "佥") ⟫ʷ ≈ ⟪ (ℓ "佫") ⟫ʷ
lem-sym-ab-at0310213442 c4 = derive (ℓ "佥") (ℓ "佫")
  (re 0 1 (ℓ "亐亓仴亓亐仴") ∷
   re 2 1 (ℓ "亠亡仠亡亠仠") ∷
   re 4 1 (ℓ "丱") ∷
   re 7 1 (ℓ "丱") ∷
   rw 2 (q1 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   re 4 1 (ℓ "伙") ∷
   re 7 1 (ℓ "伙") ∷
   re 2 6 (ℓ "伡") ∷
   re 5 1 (ℓ "亠亡仠亡亠仠") ∷
   re 7 1 (ℓ "丱") ∷
   re 10 1 (ℓ "丱") ∷
   rw 5 (q1 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   re 7 1 (ℓ "伙") ∷
   re 10 1 (ℓ "伙") ∷
   re 5 6 (ℓ "伡") ∷
   re 0 6 (ℓ "佫") ∷ []) Eq.refl

private
  q3 : Ws → Eqn
  q3 c4 = wlE 477 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = wlE 433 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (ℓ "乄亰") (ℓ "亰乄") (c₂ (CX₁₀) (CCZ))
  q6 : Ws → Eqn
  q6 c4 = wpE 363 c4
  q7 : Ws → Eqn
  q7 c4 = wpE 294 c4

-- cQ @03203442: 7 steps
lem-cQ-at03203442 : Ws → ⟪ (ℓ "亐亰") ⟫ʷ ≈ ⟪ (ℓ "亰亐") ⟫ʷ
lem-cQ-at03203442 c4 = derive (ℓ "亐亰") (ℓ "亰亐")
  (rw 0 (q3 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw 3 (q5 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw 1 (q5 c4) ∷
   rw⁻ 0 (q7 c4) ∷
   rw⁻ 1 (q3 c4) ∷ []) Eq.refl

-- sym-ab @03203442: 18 steps
lem-sym-ab-at03203442 : Ws → ⟪ (ℓ "佫") ⟫ʷ ≈ ⟪ (ℓ "佥") ⟫ʷ
lem-sym-ab-at03203442 c4 = derive (ℓ "佫") (ℓ "佥")
  (re 0 1 (ℓ "亐亓伡亓亐伡") ∷
   re 2 1 (ℓ "京亭伙亭京伙") ∷
   re 4 1 (ℓ "义") ∷
   re 7 1 (ℓ "义") ∷
   rw 2 (q2 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   re 4 1 (ℓ "仠") ∷
   re 7 1 (ℓ "仠") ∷
   re 2 6 (ℓ "仴") ∷
   re 5 1 (ℓ "京亭伙亭京伙") ∷
   re 7 1 (ℓ "义") ∷
   re 10 1 (ℓ "义") ∷
   rw 5 (q2 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   re 7 1 (ℓ "仠") ∷
   re 10 1 (ℓ "仠") ∷
   re 5 6 (ℓ "仴") ∷
   re 0 6 (ℓ "佥") ∷ []) Eq.refl

private
  q8 : Ws → Eqn
  q8 c4 = wpE 131 c4
  q9 : Ws → Eqn
  q9 c4 = wpE 130 c4

-- sym-ab @02132130: 18 steps
lem-sym-ab-at02132130 : Ws → ⟪ (ℓ "佅") ⟫ʷ ≈ ⟪ (ℓ "伴") ⟫ʷ
lem-sym-ab-at02132130 c4 = derive (ℓ "佅") (ℓ "伴")
  (re 0 1 (ℓ "交亦佄亦交佄") ∷
   re 2 1 (ℓ "亘些伺些亘伺") ∷
   re 4 1 (ℓ "乻") ∷
   re 7 1 (ℓ "乻") ∷
   rw 2 (q8 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 4 1 (ℓ "休") ∷
   re 7 1 (ℓ "休") ∷
   re 2 6 (ℓ "伒") ∷
   re 5 1 (ℓ "亘些伺些亘伺") ∷
   re 7 1 (ℓ "乻") ∷
   re 10 1 (ℓ "乻") ∷
   rw 5 (q8 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   re 7 1 (ℓ "休") ∷
   re 10 1 (ℓ "休") ∷
   re 5 6 (ℓ "伒") ∷
   re 0 6 (ℓ "伴") ∷ []) Eq.refl

private
  q10 : Ws → Eqn
  q10 c4 = wpE 262 c4
  q11 : Ws → Eqn
  q11 c4 = wlE 1303 (lit c4)

-- sym-ab @031031: 18 steps
lem-sym-ab-at031031 : Ws → ⟪ (ℓ "佦") ⟫ʷ ≈ ⟪ (ℓ "佰") ⟫ʷ
lem-sym-ab-at031031 c4 = derive (ℓ "佦") (ℓ "佰")
  (re 0 1 (ℓ "亘些仦些亘仦") ∷
   re 2 1 (ℓ "亐云以云亐以") ∷
   re 4 1 (ℓ "丿") ∷
   re 7 1 (ℓ "丿") ∷
   rw 2 (q10 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   re 4 1 (ℓ "伽") ∷
   re 7 1 (ℓ "伽") ∷
   re 2 6 (ℓ "但") ∷
   re 5 1 (ℓ "亐云以云亐以") ∷
   re 7 1 (ℓ "丿") ∷
   re 10 1 (ℓ "丿") ∷
   rw 5 (q10 c4) ∷
   rw⁻ 5 (q11 c4) ∷
   re 7 1 (ℓ "伽") ∷
   re 10 1 (ℓ "伽") ∷
   re 5 6 (ℓ "但") ∷
   re 0 6 (ℓ "佰") ∷ []) Eq.refl

private
  q12 : Ws → Eqn
  q12 c4 = wlE 344 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = wpE 661 c4

-- sym-ab @03243042: 18 steps
lem-sym-ab-at03243042 : Ws → ⟪ (ℓ "佮") ⟫ʷ ≈ ⟪ (ℓ "侂") ⟫ʷ
lem-sym-ab-at03243042 c4 = derive (ℓ "佮") (ℓ "侂")
  (re 0 1 (ℓ "京亮会亮京会") ∷
   re 2 1 (ℓ "亐互伙互亐伙") ∷
   re 4 1 (ℓ "义") ∷
   re 7 1 (ℓ "义") ∷
   rw 2 (q12 c4) ∷
   rw 2 (q13 c4) ∷
   re 4 1 (ℓ "佷") ∷
   re 7 1 (ℓ "佷") ∷
   re 2 6 (ℓ "侁") ∷
   re 5 1 (ℓ "亐互伙互亐伙") ∷
   re 7 1 (ℓ "义") ∷
   re 10 1 (ℓ "义") ∷
   rw 5 (q12 c4) ∷
   rw 5 (q13 c4) ∷
   re 7 1 (ℓ "佷") ∷
   re 10 1 (ℓ "佷") ∷
   re 5 6 (ℓ "侁") ∷
   re 0 6 (ℓ "侂") ∷ []) Eq.refl

-- sym-ab @0314213042: 18 steps
lem-sym-ab-at0314213042 : Ws → ⟪ (ℓ "侂") ⟫ʷ ≈ ⟪ (ℓ "佮") ⟫ʷ
lem-sym-ab-at0314213042 c4 = derive (ℓ "侂") (ℓ "佮")
  (re 0 1 (ℓ "京亮侁亮京侁") ∷
   re 2 1 (ℓ "亠亣佷亣亠佷") ∷
   re 4 1 (ℓ "乫") ∷
   re 7 1 (ℓ "乫") ∷
   rw⁻ 2 (q13 c4) ∷
   rw⁻ 2 (q12 c4) ∷
   re 4 1 (ℓ "伙") ∷
   re 7 1 (ℓ "伙") ∷
   re 2 6 (ℓ "会") ∷
   re 5 1 (ℓ "亠亣佷亣亠佷") ∷
   re 7 1 (ℓ "乫") ∷
   re 10 1 (ℓ "乫") ∷
   rw⁻ 5 (q13 c4) ∷
   rw⁻ 5 (q12 c4) ∷
   re 7 1 (ℓ "伙") ∷
   re 10 1 (ℓ "伙") ∷
   re 5 6 (ℓ "会") ∷
   re 0 6 (ℓ "佮") ∷ []) Eq.refl

-- sym-ab @142142: 18 steps
lem-sym-ab-at142142 : Ws → ⟪ (ℓ "企") ⟫ʷ ≈ ⟪ (ℓ "仆") ⟫ʷ
lem-sym-ab-at142142 c4 = derive (ℓ "企") (ℓ "仆")
  (re 0 1 (ℓ "五井伀井五伀") ∷
   re 2 1 (ℓ "亠亣仿亣亠仿") ∷
   re 4 1 (ℓ "乫") ∷
   re 7 1 (ℓ "乫") ∷
   rw⁻ 2 (q13 c4) ∷
   rw⁻ 2 (q12 c4) ∷
   re 4 1 (ℓ "亴") ∷
   re 7 1 (ℓ "亴") ∷
   re 2 6 (ℓ "仅") ∷
   re 5 1 (ℓ "亠亣仿亣亠仿") ∷
   re 7 1 (ℓ "乫") ∷
   re 10 1 (ℓ "乫") ∷
   rw⁻ 5 (q13 c4) ∷
   rw⁻ 5 (q12 c4) ∷
   re 7 1 (ℓ "亴") ∷
   re 10 1 (ℓ "亴") ∷
   re 5 6 (ℓ "仅") ∷
   re 0 6 (ℓ "仆") ∷ []) Eq.refl

-- sym-ab @2442: 18 steps
lem-sym-ab-at2442 : Ws → ⟪ (ℓ "仆") ⟫ʷ ≈ ⟪ (ℓ "企") ⟫ʷ
lem-sym-ab-at2442 c4 = derive (ℓ "仆") (ℓ "企")
  (re 0 1 (ℓ "五井仅井五仅") ∷
   re 2 1 (ℓ "亐互亴互亐亴") ∷
   re 4 1 (ℓ "义") ∷
   re 7 1 (ℓ "义") ∷
   rw 2 (q12 c4) ∷
   rw 2 (q13 c4) ∷
   re 4 1 (ℓ "仿") ∷
   re 7 1 (ℓ "仿") ∷
   re 2 6 (ℓ "伀") ∷
   re 5 1 (ℓ "亐互亴互亐亴") ∷
   re 7 1 (ℓ "义") ∷
   re 10 1 (ℓ "义") ∷
   rw 5 (q12 c4) ∷
   rw 5 (q13 c4) ∷
   re 7 1 (ℓ "仿") ∷
   re 10 1 (ℓ "仿") ∷
   re 5 6 (ℓ "伀") ∷
   re 0 6 (ℓ "企") ∷ []) Eq.refl

private
  q14 : Ws → Eqn
  q14 c4 = wpE 1232 c4
  q15 : Ws → Eqn
  q15 c4 = wlE 1341 (lit c4)

-- sym-ab @02102331: 18 steps
lem-sym-ab-at02102331 : Ws → ⟪ (ℓ "伯") ⟫ʷ ≈ ⟪ (ℓ "似") ⟫ʷ
lem-sym-ab-at02102331 c4 = derive (ℓ "伯") (ℓ "似")
  (re 0 1 (ℓ "亘亚从亚亘从") ∷
   re 2 1 (ℓ "二亍仍亍二仍") ∷
   re 4 1 (ℓ "丿") ∷
   re 7 1 (ℓ "丿") ∷
   rw 2 (q14 c4) ∷
   rw⁻ 2 (q15 c4) ∷
   re 4 1 (ℓ "伺") ∷
   re 7 1 (ℓ "伺") ∷
   re 2 6 (ℓ "伻") ∷
   re 5 1 (ℓ "二亍仍亍二仍") ∷
   re 7 1 (ℓ "丿") ∷
   re 10 1 (ℓ "丿") ∷
   rw 5 (q14 c4) ∷
   rw⁻ 5 (q15 c4) ∷
   re 7 1 (ℓ "伺") ∷
   re 10 1 (ℓ "伺") ∷
   re 5 6 (ℓ "伻") ∷
   re 0 6 (ℓ "似") ∷ []) Eq.refl

-- sym-ab @02132031: 18 steps
lem-sym-ab-at02132031 : Ws → ⟪ (ℓ "似") ⟫ʷ ≈ ⟪ (ℓ "伯") ⟫ʷ
lem-sym-ab-at02132031 c4 = derive (ℓ "似") (ℓ "伯")
  (re 0 1 (ℓ "亘亚伻亚亘伻") ∷
   re 2 1 (ℓ "交产伺产交伺") ∷
   re 4 1 (ℓ "乻") ∷
   re 7 1 (ℓ "乻") ∷
   rw 2 (q15 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   re 4 1 (ℓ "仍") ∷
   re 7 1 (ℓ "仍") ∷
   re 2 6 (ℓ "从") ∷
   re 5 1 (ℓ "交产伺产交伺") ∷
   re 7 1 (ℓ "乻") ∷
   re 10 1 (ℓ "乻") ∷
   rw 5 (q15 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   re 7 1 (ℓ "仍") ∷
   re 10 1 (ℓ "仍") ∷
   re 5 6 (ℓ "从") ∷
   re 0 6 (ℓ "伯") ∷ []) Eq.refl

private
  q16 : Ws → Eqn
  q16 c4 = wpE 404 c4

-- F4-I-K2 @02132031: 1 steps
lem-F4-I-K2-at02132031 : Ws → ⟪ (ℓ "並丢並亁") ⟫ʷ ≈ ⟪ (ℓ "亁並丢並") ⟫ʷ
lem-F4-I-K2-at02132031 c4 = derive (ℓ "並丢並亁") (ℓ "亁並丢並")
  (rw⁻ 0 (q16 c4) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = wpE 441 c4

-- F4-S3-K2 @02132031: 1 steps
lem-F4-S3-K2-at02132031 : Ws → ⟪ (ℓ "並乕並亁") ⟫ʷ ≈ ⟪ (ℓ "亁並乕並") ⟫ʷ
lem-F4-S3-K2-at02132031 c4 = derive (ℓ "並乕並亁") (ℓ "亁並乕並")
  (rw⁻ 0 (q17 c4) ∷ []) Eq.refl

private
  q18 : Ws → Eqn
  q18 c4 = wpE 474 c4

-- F4-K2-K2 @02132031: 1 steps
lem-F4-K2-K2-at02132031 : Ws → ⟪ (ℓ "並亁並亁") ⟫ʷ ≈ ⟪ (ℓ "亁並亁並") ⟫ʷ
lem-F4-K2-K2-at02132031 c4 = derive (ℓ "並亁並亁") (ℓ "亁並亁並")
  (rw⁻ 0 (q18 c4) ∷ []) Eq.refl

private
  q19 : Ws → Eqn
  q19 c4 = wlE 550 (lit c4)

-- F4-I-S3 @02132031: 1 steps
lem-F4-I-S3-at02132031 : Ws → ⟪ (ℓ "並丢並乕") ⟫ʷ ≈ ⟪ (ℓ "乕並丢並") ⟫ʷ
lem-F4-I-S3-at02132031 c4 = derive (ℓ "並丢並乕") (ℓ "乕並丢並")
  (rw⁻ 0 (q19 c4) ∷ []) Eq.refl

private
  q20 : Ws → Eqn
  q20 c4 = wlE 564 (lit c4)

-- F4-S3-S3 @02132031: 1 steps
lem-F4-S3-S3-at02132031 : Ws → ⟪ (ℓ "並乕並乕") ⟫ʷ ≈ ⟪ (ℓ "乕並乕並") ⟫ʷ
lem-F4-S3-S3-at02132031 c4 = derive (ℓ "並乕並乕") (ℓ "乕並乕並")
  (rw⁻ 0 (q20 c4) ∷ []) Eq.refl

private
  q21 : Ws → Eqn
  q21 c4 = wpE 471 c4

-- F4-K2-S3 @02132031: 1 steps
lem-F4-K2-S3-at02132031 : Ws → ⟪ (ℓ "並亁並乕") ⟫ʷ ≈ ⟪ (ℓ "乕並亁並") ⟫ʷ
lem-F4-K2-S3-at02132031 c4 = derive (ℓ "並亁並乕") (ℓ "乕並亁並")
  (rw⁻ 0 (q21 c4) ∷ []) Eq.refl

private
  q22 : Ws → Eqn
  q22 c4 = wlE 549 (lit c4)

-- F4-I-I @02132031: 1 steps
lem-F4-I-I-at02132031 : Ws → ⟪ (ℓ "並丢並丢") ⟫ʷ ≈ ⟪ (ℓ "丢並丢並") ⟫ʷ
lem-F4-I-I-at02132031 c4 = derive (ℓ "並丢並丢") (ℓ "丢並丢並")
  (rw⁻ 0 (q22 c4) ∷ []) Eq.refl

private
  q23 : Ws → Eqn
  q23 c4 = wlE 563 (lit c4)

-- F4-S3-I @02132031: 1 steps
lem-F4-S3-I-at02132031 : Ws → ⟪ (ℓ "並乕並丢") ⟫ʷ ≈ ⟪ (ℓ "丢並乕並") ⟫ʷ
lem-F4-S3-I-at02132031 c4 = derive (ℓ "並乕並丢") (ℓ "丢並乕並")
  (rw⁻ 0 (q23 c4) ∷ []) Eq.refl

private
  q24 : Ws → Eqn
  q24 c4 = wpE 469 c4

-- F4-K2-I @02132031: 1 steps
lem-F4-K2-I-at02132031 : Ws → ⟪ (ℓ "並亁並丢") ⟫ʷ ≈ ⟪ (ℓ "丢並亁並") ⟫ʷ
lem-F4-K2-I-at02132031 c4 = derive (ℓ "並亁並丢") (ℓ "丢並亁並")
  (rw⁻ 0 (q24 c4) ∷ []) Eq.refl

private
  q25 : Ws → Eqn
  q25 c4 = wpE 403 c4

-- F4-I-S2 @02132031: 1 steps
lem-F4-I-S2-at02132031 : Ws → ⟪ (ℓ "並丢並丽") ⟫ʷ ≈ ⟪ (ℓ "丽並丢並") ⟫ʷ
lem-F4-I-S2-at02132031 c4 = derive (ℓ "並丢並丽") (ℓ "丽並丢並")
  (rw⁻ 0 (q25 c4) ∷ []) Eq.refl

private
  q26 : Ws → Eqn
  q26 c4 = wpE 440 c4

-- F4-S3-S2 @02132031: 1 steps
lem-F4-S3-S2-at02132031 : Ws → ⟪ (ℓ "並乕並丽") ⟫ʷ ≈ ⟪ (ℓ "丽並乕並") ⟫ʷ
lem-F4-S3-S2-at02132031 c4 = derive (ℓ "並乕並丽") (ℓ "丽並乕並")
  (rw⁻ 0 (q26 c4) ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = wpE 470 c4

-- F4-K2-S2 @02132031: 1 steps
lem-F4-K2-S2-at02132031 : Ws → ⟪ (ℓ "並亁並丽") ⟫ʷ ≈ ⟪ (ℓ "丽並亁並") ⟫ʷ
lem-F4-K2-S2-at02132031 c4 = derive (ℓ "並亁並丽") (ℓ "丽並亁並")
  (rw⁻ 0 (q27 c4) ∷ []) Eq.refl

private
  q28 : Ws → Eqn
  q28 c4 = wlE 553 (lit c4)

-- F4-I-K2 @132132: 1 steps
lem-F4-I-K2-at132132 : Ws → ⟪ (ℓ "並丢並亄") ⟫ʷ ≈ ⟪ (ℓ "亄並丢並") ⟫ʷ
lem-F4-I-K2-at132132 c4 = derive (ℓ "並丢並亄") (ℓ "亄並丢並")
  (rw⁻ 0 (q28 c4) ∷ []) Eq.refl

private
  q29 : Ws → Eqn
  q29 c4 = wlE 579 (lit c4)

-- F4-S3-K2 @132132: 1 steps
lem-F4-S3-K2-at132132 : Ws → ⟪ (ℓ "並乩並亄") ⟫ʷ ≈ ⟪ (ℓ "亄並乩並") ⟫ʷ
lem-F4-S3-K2-at132132 c4 = derive (ℓ "並乩並亄") (ℓ "亄並乩並")
  (rw⁻ 0 (q29 c4) ∷ []) Eq.refl

private
  q30 : Ws → Eqn
  q30 c4 = wlE 607 (lit c4)

-- F4-K2-K2 @132132: 1 steps
lem-F4-K2-K2-at132132 : Ws → ⟪ (ℓ "並亄並亄") ⟫ʷ ≈ ⟪ (ℓ "亄並亄並") ⟫ʷ
lem-F4-K2-K2-at132132 c4 = derive (ℓ "並亄並亄") (ℓ "亄並亄並")
  (rw⁻ 0 (q30 c4) ∷ []) Eq.refl

private
  q31 : Ws → Eqn
  q31 c4 = wlE 551 (lit c4)

-- F4-I-S3 @132132: 1 steps
lem-F4-I-S3-at132132 : Ws → ⟪ (ℓ "並丢並乩") ⟫ʷ ≈ ⟪ (ℓ "乩並丢並") ⟫ʷ
lem-F4-I-S3-at132132 c4 = derive (ℓ "並丢並乩") (ℓ "乩並丢並")
  (rw⁻ 0 (q31 c4) ∷ []) Eq.refl

private
  q32 : Ws → Eqn
  q32 c4 = wlE 577 (lit c4)

-- F4-S3-S3 @132132: 1 steps
lem-F4-S3-S3-at132132 : Ws → ⟪ (ℓ "並乩並乩") ⟫ʷ ≈ ⟪ (ℓ "乩並乩並") ⟫ʷ
lem-F4-S3-S3-at132132 c4 = derive (ℓ "並乩並乩") (ℓ "乩並乩並")
  (rw⁻ 0 (q32 c4) ∷ []) Eq.refl

private
  q33 : Ws → Eqn
  q33 c4 = wlE 605 (lit c4)

-- F4-K2-S3 @132132: 1 steps
lem-F4-K2-S3-at132132 : Ws → ⟪ (ℓ "並亄並乩") ⟫ʷ ≈ ⟪ (ℓ "乩並亄並") ⟫ʷ
lem-F4-K2-S3-at132132 c4 = derive (ℓ "並亄並乩") (ℓ "乩並亄並")
  (rw⁻ 0 (q33 c4) ∷ []) Eq.refl

-- F4-I-I @132132: 1 steps
lem-F4-I-I-at132132 : Ws → ⟪ (ℓ "並丢並丢") ⟫ʷ ≈ ⟪ (ℓ "丢並丢並") ⟫ʷ
lem-F4-I-I-at132132 c4 = derive (ℓ "並丢並丢") (ℓ "丢並丢並")
  (rw⁻ 0 (q22 c4) ∷ []) Eq.refl

private
  q34 : Ws → Eqn
  q34 c4 = wlE 575 (lit c4)

-- F4-S3-I @132132: 1 steps
lem-F4-S3-I-at132132 : Ws → ⟪ (ℓ "並乩並丢") ⟫ʷ ≈ ⟪ (ℓ "丢並乩並") ⟫ʷ
lem-F4-S3-I-at132132 c4 = derive (ℓ "並乩並丢") (ℓ "丢並乩並")
  (rw⁻ 0 (q34 c4) ∷ []) Eq.refl

private
  q35 : Ws → Eqn
  q35 c4 = wlE 603 (lit c4)

-- F4-K2-I @132132: 1 steps
lem-F4-K2-I-at132132 : Ws → ⟪ (ℓ "並亄並丢") ⟫ʷ ≈ ⟪ (ℓ "丢並亄並") ⟫ʷ
lem-F4-K2-I-at132132 c4 = derive (ℓ "並亄並丢") (ℓ "丢並亄並")
  (rw⁻ 0 (q35 c4) ∷ []) Eq.refl

-- F4-I-S2 @132132: 1 steps
lem-F4-I-S2-at132132 : Ws → ⟪ (ℓ "並丢並乕") ⟫ʷ ≈ ⟪ (ℓ "乕並丢並") ⟫ʷ
lem-F4-I-S2-at132132 c4 = derive (ℓ "並丢並乕") (ℓ "乕並丢並")
  (rw⁻ 0 (q19 c4) ∷ []) Eq.refl

private
  q36 : Ws → Eqn
  q36 c4 = wlE 576 (lit c4)

-- F4-S3-S2 @132132: 1 steps
lem-F4-S3-S2-at132132 : Ws → ⟪ (ℓ "並乩並乕") ⟫ʷ ≈ ⟪ (ℓ "乕並乩並") ⟫ʷ
lem-F4-S3-S2-at132132 c4 = derive (ℓ "並乩並乕") (ℓ "乕並乩並")
  (rw⁻ 0 (q36 c4) ∷ []) Eq.refl

private
  q37 : Ws → Eqn
  q37 c4 = wlE 604 (lit c4)

-- F4-K2-S2 @132132: 1 steps
lem-F4-K2-S2-at132132 : Ws → ⟪ (ℓ "並亄並乕") ⟫ʷ ≈ ⟪ (ℓ "乕並亄並") ⟫ʷ
lem-F4-K2-S2-at132132 c4 = derive (ℓ "並亄並乕") (ℓ "乕並亄並")
  (rw⁻ 0 (q37 c4) ∷ []) Eq.refl

-- F4-I-K3 @02132031: 1 steps
lem-F4-I-K3-at02132031 : Ws → ⟪ (ℓ "並丢並亄") ⟫ʷ ≈ ⟪ (ℓ "亄並丢並") ⟫ʷ
lem-F4-I-K3-at02132031 c4 = derive (ℓ "並丢並亄") (ℓ "亄並丢並")
  (rw⁻ 0 (q28 c4) ∷ []) Eq.refl

private
  q38 : Ws → Eqn
  q38 c4 = wpE 416 c4

-- F4-S2-K3 @02132031: 1 steps
lem-F4-S2-K3-at02132031 : Ws → ⟪ (ℓ "並丽並亄") ⟫ʷ ≈ ⟪ (ℓ "亄並丽並") ⟫ʷ
lem-F4-S2-K3-at02132031 c4 = derive (ℓ "並丽並亄") (ℓ "亄並丽並")
  (rw⁻ 0 (q38 c4) ∷ []) Eq.refl

-- F4-K3-K3 @02132031: 1 steps
lem-F4-K3-K3-at02132031 : Ws → ⟪ (ℓ "並亄並亄") ⟫ʷ ≈ ⟪ (ℓ "亄並亄並") ⟫ʷ
lem-F4-K3-K3-at02132031 c4 = derive (ℓ "並亄並亄") (ℓ "亄並亄並")
  (rw⁻ 0 (q30 c4) ∷ []) Eq.refl

private
  q39 : Ws → Eqn
  q39 c4 = wpE 411 c4

-- F4-S2-S2 @02132031: 1 steps
lem-F4-S2-S2-at02132031 : Ws → ⟪ (ℓ "並丽並丽") ⟫ʷ ≈ ⟪ (ℓ "丽並丽並") ⟫ʷ
lem-F4-S2-S2-at02132031 c4 = derive (ℓ "並丽並丽") (ℓ "丽並丽並")
  (rw⁻ 0 (q39 c4) ∷ []) Eq.refl

private
  q40 : Ws → Eqn
  q40 c4 = wpE 494 c4

-- F4-K3-S2 @02132031: 1 steps
lem-F4-K3-S2-at02132031 : Ws → ⟪ (ℓ "並亄並丽") ⟫ʷ ≈ ⟪ (ℓ "丽並亄並") ⟫ʷ
lem-F4-K3-S2-at02132031 c4 = derive (ℓ "並亄並丽") (ℓ "丽並亄並")
  (rw⁻ 0 (q40 c4) ∷ []) Eq.refl

private
  q41 : Ws → Eqn
  q41 c4 = wpE 410 c4

-- F4-S2-I @02132031: 1 steps
lem-F4-S2-I-at02132031 : Ws → ⟪ (ℓ "並丽並丢") ⟫ʷ ≈ ⟪ (ℓ "丢並丽並") ⟫ʷ
lem-F4-S2-I-at02132031 c4 = derive (ℓ "並丽並丢") (ℓ "丢並丽並")
  (rw⁻ 0 (q41 c4) ∷ []) Eq.refl

-- F4-K3-I @02132031: 1 steps
lem-F4-K3-I-at02132031 : Ws → ⟪ (ℓ "並亄並丢") ⟫ʷ ≈ ⟪ (ℓ "丢並亄並") ⟫ʷ
lem-F4-K3-I-at02132031 c4 = derive (ℓ "並亄並丢") (ℓ "丢並亄並")
  (rw⁻ 0 (q35 c4) ∷ []) Eq.refl

private
  q42 : Ws → Eqn
  q42 c4 = wpE 412 c4

-- F4-S2-S3 @02132031: 1 steps
lem-F4-S2-S3-at02132031 : Ws → ⟪ (ℓ "並丽並乕") ⟫ʷ ≈ ⟪ (ℓ "乕並丽並") ⟫ʷ
lem-F4-S2-S3-at02132031 c4 = derive (ℓ "並丽並乕") (ℓ "乕並丽並")
  (rw⁻ 0 (q42 c4) ∷ []) Eq.refl

-- F4-K3-S3 @02132031: 1 steps
lem-F4-K3-S3-at02132031 : Ws → ⟪ (ℓ "並亄並乕") ⟫ʷ ≈ ⟪ (ℓ "乕並亄並") ⟫ʷ
lem-F4-K3-S3-at02132031 c4 = derive (ℓ "並亄並乕") (ℓ "乕並亄並")
  (rw⁻ 0 (q37 c4) ∷ []) Eq.refl

private
  q43 : Ws → Eqn
  q43 c4 = wlE 554 (lit c4)

-- F4-I-K3 @132132: 1 steps
lem-F4-I-K3-at132132 : Ws → ⟪ (ℓ "並丢並亇") ⟫ʷ ≈ ⟪ (ℓ "亇並丢並") ⟫ʷ
lem-F4-I-K3-at132132 c4 = derive (ℓ "並丢並亇") (ℓ "亇並丢並")
  (rw⁻ 0 (q43 c4) ∷ []) Eq.refl

private
  q44 : Ws → Eqn
  q44 c4 = wlE 568 (lit c4)

-- F4-S2-K3 @132132: 1 steps
lem-F4-S2-K3-at132132 : Ws → ⟪ (ℓ "並乕並亇") ⟫ʷ ≈ ⟪ (ℓ "亇並乕並") ⟫ʷ
lem-F4-S2-K3-at132132 c4 = derive (ℓ "並乕並亇") (ℓ "亇並乕並")
  (rw⁻ 0 (q44 c4) ∷ []) Eq.refl

private
  q45 : Ws → Eqn
  q45 c4 = wlE 660 (lit c4)

-- F4-K3-K3 @132132: 1 steps
lem-F4-K3-K3-at132132 : Ws → ⟪ (ℓ "並亇並亇") ⟫ʷ ≈ ⟪ (ℓ "亇並亇並") ⟫ʷ
lem-F4-K3-K3-at132132 c4 = derive (ℓ "並亇並亇") (ℓ "亇並亇並")
  (rw⁻ 0 (q45 c4) ∷ []) Eq.refl

-- F4-S2-S2 @132132: 1 steps
lem-F4-S2-S2-at132132 : Ws → ⟪ (ℓ "並乕並乕") ⟫ʷ ≈ ⟪ (ℓ "乕並乕並") ⟫ʷ
lem-F4-S2-S2-at132132 c4 = derive (ℓ "並乕並乕") (ℓ "乕並乕並")
  (rw⁻ 0 (q20 c4) ∷ []) Eq.refl

private
  q46 : Ws → Eqn
  q46 c4 = wlE 656 (lit c4)

-- F4-K3-S2 @132132: 1 steps
lem-F4-K3-S2-at132132 : Ws → ⟪ (ℓ "並亇並乕") ⟫ʷ ≈ ⟪ (ℓ "乕並亇並") ⟫ʷ
lem-F4-K3-S2-at132132 c4 = derive (ℓ "並亇並乕") (ℓ "乕並亇並")
  (rw⁻ 0 (q46 c4) ∷ []) Eq.refl

-- F4-S2-I @132132: 1 steps
lem-F4-S2-I-at132132 : Ws → ⟪ (ℓ "並乕並丢") ⟫ʷ ≈ ⟪ (ℓ "丢並乕並") ⟫ʷ
lem-F4-S2-I-at132132 c4 = derive (ℓ "並乕並丢") (ℓ "丢並乕並")
  (rw⁻ 0 (q23 c4) ∷ []) Eq.refl

private
  q47 : Ws → Eqn
  q47 c4 = wlE 655 (lit c4)

-- F4-K3-I @132132: 1 steps
lem-F4-K3-I-at132132 : Ws → ⟪ (ℓ "並亇並丢") ⟫ʷ ≈ ⟪ (ℓ "丢並亇並") ⟫ʷ
lem-F4-K3-I-at132132 c4 = derive (ℓ "並亇並丢") (ℓ "丢並亇並")
  (rw⁻ 0 (q47 c4) ∷ []) Eq.refl

private
  q48 : Ws → Eqn
  q48 c4 = wlE 565 (lit c4)

-- F4-S2-S3 @132132: 1 steps
lem-F4-S2-S3-at132132 : Ws → ⟪ (ℓ "並乕並乩") ⟫ʷ ≈ ⟪ (ℓ "乩並乕並") ⟫ʷ
lem-F4-S2-S3-at132132 c4 = derive (ℓ "並乕並乩") (ℓ "乩並乕並")
  (rw⁻ 0 (q48 c4) ∷ []) Eq.refl

private
  q49 : Ws → Eqn
  q49 c4 = wlE 657 (lit c4)

-- F4-K3-S3 @132132: 1 steps
lem-F4-K3-S3-at132132 : Ws → ⟪ (ℓ "並亇並乩") ⟫ʷ ≈ ⟪ (ℓ "乩並亇並") ⟫ʷ
lem-F4-K3-S3-at132132 c4 = derive (ℓ "並亇並乩") (ℓ "乩並亇並")
  (rw⁻ 0 (q49 c4) ∷ []) Eq.refl

private
  q50 : Ws → Eqn
  q50 c4 = wlE 1440 (lit c4)

-- F4-I-K3 @0213243140: 1 steps
lem-F4-I-K3-at0213243140 : Ws → ⟪ (ℓ "与上与中") ⟫ʷ ≈ ⟪ (ℓ "中与上与") ⟫ʷ
lem-F4-I-K3-at0213243140 c4 = derive (ℓ "与上与中") (ℓ "中与上与")
  (rw⁻ 0 (q50 c4) ∷ []) Eq.refl

private
  q51 : Ws → Eqn
  q51 c4 = wpE 1293 c4

-- F4-S2-K3 @0213243140: 1 steps
lem-F4-S2-K3-at0213243140 : Ws → ⟪ (ℓ "与丽与中") ⟫ʷ ≈ ⟪ (ℓ "中与丽与") ⟫ʷ
lem-F4-S2-K3-at0213243140 c4 = derive (ℓ "与丽与中") (ℓ "中与丽与")
  (rw⁻ 0 (q51 c4) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = wlE 1444 (lit c4)

-- F4-K3-K3 @0213243140: 1 steps
lem-F4-K3-K3-at0213243140 : Ws → ⟪ (ℓ "与中与中") ⟫ʷ ≈ ⟪ (ℓ "中与中与") ⟫ʷ
lem-F4-K3-K3-at0213243140 c4 = derive (ℓ "与中与中") (ℓ "中与中与")
  (rw⁻ 0 (q52 c4) ∷ []) Eq.refl

private
  q53 : Ws → Eqn
  q53 c4 = wpE 1295 c4

-- F4-I-S2 @0213243140: 1 steps
lem-F4-I-S2-at0213243140 : Ws → ⟪ (ℓ "与上与丽") ⟫ʷ ≈ ⟪ (ℓ "丽与上与") ⟫ʷ
lem-F4-I-S2-at0213243140 c4 = derive (ℓ "与上与丽") (ℓ "丽与上与")
  (rw⁻ 0 (q53 c4) ∷ []) Eq.refl

private
  q54 : Ws → Eqn
  q54 c4 = wpE 1296 c4

-- F4-S2-S2 @0213243140: 1 steps
lem-F4-S2-S2-at0213243140 : Ws → ⟪ (ℓ "与丽与丽") ⟫ʷ ≈ ⟪ (ℓ "丽与丽与") ⟫ʷ
lem-F4-S2-S2-at0213243140 c4 = derive (ℓ "与丽与丽") (ℓ "丽与丽与")
  (rw⁻ 0 (q54 c4) ∷ []) Eq.refl

private
  q55 : Ws → Eqn
  q55 c4 = wpE 1299 c4

-- F4-K3-S2 @0213243140: 1 steps
lem-F4-K3-S2-at0213243140 : Ws → ⟪ (ℓ "与中与丽") ⟫ʷ ≈ ⟪ (ℓ "丽与中与") ⟫ʷ
lem-F4-K3-S2-at0213243140 c4 = derive (ℓ "与中与丽") (ℓ "丽与中与")
  (rw⁻ 0 (q55 c4) ∷ []) Eq.refl

private
  q56 : Ws → Eqn
  q56 c4 = wlE 1445 (lit c4)

-- F4-I-I @0213243140: 1 steps
lem-F4-I-I-at0213243140 : Ws → ⟪ (ℓ "与上与上") ⟫ʷ ≈ ⟪ (ℓ "上与上与") ⟫ʷ
lem-F4-I-I-at0213243140 c4 = derive (ℓ "与上与上") (ℓ "上与上与")
  (rw⁻ 0 (q56 c4) ∷ []) Eq.refl

private
  q57 : Ws → Eqn
  q57 c4 = wpE 1300 c4

-- F4-S2-I @0213243140: 1 steps
lem-F4-S2-I-at0213243140 : Ws → ⟪ (ℓ "与丽与上") ⟫ʷ ≈ ⟪ (ℓ "上与丽与") ⟫ʷ
lem-F4-S2-I-at0213243140 c4 = derive (ℓ "与丽与上") (ℓ "上与丽与")
  (rw⁻ 0 (q57 c4) ∷ []) Eq.refl

private
  q58 : Ws → Eqn
  q58 c4 = wlE 1449 (lit c4)

-- F4-K3-I @0213243140: 1 steps
lem-F4-K3-I-at0213243140 : Ws → ⟪ (ℓ "与中与上") ⟫ʷ ≈ ⟪ (ℓ "上与中与") ⟫ʷ
lem-F4-K3-I-at0213243140 c4 = derive (ℓ "与中与上") (ℓ "上与中与")
  (rw⁻ 0 (q58 c4) ∷ []) Eq.refl

private
  q59 : Ws → Eqn
  q59 c4 = wlE 1450 (lit c4)

-- F4-I-S3 @0213243140: 1 steps
lem-F4-I-S3-at0213243140 : Ws → ⟪ (ℓ "与上与丨") ⟫ʷ ≈ ⟪ (ℓ "丨与上与") ⟫ʷ
lem-F4-I-S3-at0213243140 c4 = derive (ℓ "与上与丨") (ℓ "丨与上与")
  (rw⁻ 0 (q59 c4) ∷ []) Eq.refl

private
  q60 : Ws → Eqn
  q60 c4 = wpE 1303 c4

-- F4-S2-S3 @0213243140: 1 steps
lem-F4-S2-S3-at0213243140 : Ws → ⟪ (ℓ "与丽与丨") ⟫ʷ ≈ ⟪ (ℓ "丨与丽与") ⟫ʷ
lem-F4-S2-S3-at0213243140 c4 = derive (ℓ "与丽与丨") (ℓ "丨与丽与")
  (rw⁻ 0 (q60 c4) ∷ []) Eq.refl

private
  q61 : Ws → Eqn
  q61 c4 = wlE 1454 (lit c4)

-- F4-K3-S3 @0213243140: 1 steps
lem-F4-K3-S3-at0213243140 : Ws → ⟪ (ℓ "与中与丨") ⟫ʷ ≈ ⟪ (ℓ "丨与中与") ⟫ʷ
lem-F4-K3-S3-at0213243140 c4 = derive (ℓ "与中与丨") (ℓ "丨与中与")
  (rw⁻ 0 (q61 c4) ∷ []) Eq.refl

private
  q62 : Ws → Eqn
  q62 c4 = wlE 1476 (lit c4)

-- F4-K2-K1 @0440: 1 steps
lem-F4-K2-K1-at0440 : Ws → ⟪ (ℓ "与临与中") ⟫ʷ ≈ ⟪ (ℓ "中与临与") ⟫ʷ
lem-F4-K2-K1-at0440 c4 = derive (ℓ "与临与中") (ℓ "中与临与")
  (rw⁻ 0 (q62 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = wlE 1531 (lit c4)

-- F4-K2-K2 @0440: 1 steps
lem-F4-K2-K2-at0440 : Ws → ⟪ (ℓ "与临与临") ⟫ʷ ≈ ⟪ (ℓ "临与临与") ⟫ʷ
lem-F4-K2-K2-at0440 c4 = derive (ℓ "与临与临") (ℓ "临与临与")
  (rw⁻ 0 (q63 c4) ∷ []) Eq.refl

private
  q64 : Ws → Eqn
  q64 c4 = wlE 1532 (lit c4)

-- F4-I-K2 @0440: 1 steps
lem-F4-I-K2-at0440 : Ws → ⟪ (ℓ "与上与临") ⟫ʷ ≈ ⟪ (ℓ "临与上与") ⟫ʷ
lem-F4-I-K2-at0440 c4 = derive (ℓ "与上与临") (ℓ "临与上与")
  (rw⁻ 0 (q64 c4) ∷ []) Eq.refl

-- F4-I-K1 @0440: 1 steps
lem-F4-I-K1-at0440 : Ws → ⟪ (ℓ "与上与中") ⟫ʷ ≈ ⟪ (ℓ "中与上与") ⟫ʷ
lem-F4-I-K1-at0440 c4 = derive (ℓ "与上与中") (ℓ "中与上与")
  (rw⁻ 0 (q50 c4) ∷ []) Eq.refl

private
  q65 : Ws → Eqn
  q65 c4 = wlE 1556 (lit c4)

-- F4-K2-I @0440: 1 steps
lem-F4-K2-I-at0440 : Ws → ⟪ (ℓ "与临与上") ⟫ʷ ≈ ⟪ (ℓ "上与临与") ⟫ʷ
lem-F4-K2-I-at0440 c4 = derive (ℓ "与临与上") (ℓ "上与临与")
  (rw⁻ 0 (q65 c4) ∷ []) Eq.refl

-- F4-I-I @0440: 1 steps
lem-F4-I-I-at0440 : Ws → ⟪ (ℓ "与上与上") ⟫ʷ ≈ ⟪ (ℓ "上与上与") ⟫ʷ
lem-F4-I-I-at0440 c4 = derive (ℓ "与上与上") (ℓ "上与上与")
  (rw⁻ 0 (q56 c4) ∷ []) Eq.refl

private
  q66 : Ws → Eqn
  q66 c4 = wlE 1559 (lit c4)

-- F4-K3-I @0440: 1 steps
lem-F4-K3-I-at0440 : Ws → ⟪ (ℓ "与主与上") ⟫ʷ ≈ ⟪ (ℓ "上与主与") ⟫ʷ
lem-F4-K3-I-at0440 c4 = derive (ℓ "与主与上") (ℓ "上与主与")
  (rw⁻ 0 (q66 c4) ∷ []) Eq.refl

private
  q67 : Ws → Eqn
  q67 c4 = wlE 1560 (lit c4)

-- F4-K3-K2 @0440: 1 steps
lem-F4-K3-K2-at0440 : Ws → ⟪ (ℓ "与主与临") ⟫ʷ ≈ ⟪ (ℓ "临与主与") ⟫ʷ
lem-F4-K3-K2-at0440 c4 = derive (ℓ "与主与临") (ℓ "临与主与")
  (rw⁻ 0 (q67 c4) ∷ []) Eq.refl

private
  q68 : Ws → Eqn
  q68 c4 = wlE 1271 (lit c4)
  q69 : Ws → Eqn
  q69 c4 = wpE 1048 c4

-- sym-ab @04122041: 18 steps
lem-sym-ab-at04122041 : Ws → ⟪ (ℓ "侗") ⟫ʷ ≈ ⟪ (ℓ "侏") ⟫ʷ
lem-sym-ab-at04122041 c4 = derive (ℓ "侗") (ℓ "侏")
  (re 0 1 (ℓ "亜亟佣亟亜佣") ∷
   re 2 1 (ℓ "亰亱佐亱亰佐") ∷
   re 4 1 (ℓ "义") ∷
   re 7 1 (ℓ "义") ∷
   rw⁻ 2 (q68 c4) ∷
   rw⁻ 2 (q69 c4) ∷
   re 4 1 (ℓ "伂") ∷
   re 7 1 (ℓ "伂") ∷
   re 2 6 (ℓ "伉") ∷
   re 5 1 (ℓ "亰亱佐亱亰佐") ∷
   re 7 1 (ℓ "义") ∷
   re 10 1 (ℓ "义") ∷
   rw⁻ 5 (q68 c4) ∷
   rw⁻ 5 (q69 c4) ∷
   re 7 1 (ℓ "伂") ∷
   re 10 1 (ℓ "伂") ∷
   re 5 6 (ℓ "伉") ∷
   re 0 6 (ℓ "侏") ∷ []) Eq.refl

private
  q70 : Ws → Eqn
  q70 c4 = wpE 594 c4
  q71 : Ws → Eqn
  q71 c4 = wpE 987 c4
  q72 : Ws → Eqn
  q72 c4 = wpE 596 c4
  q73 : Ws → Eqn
  q73 c4 = wpE 986 c4
  q74 : Ws → Eqn
  q74 c4 = eqn (ℓ "伂乥") (ℓ "乥伂") (c₂ (CZ) (Swap))
  q75 : Ws → Eqn
  q75 c4 = wlE 3 (lit c4)

-- nat-SWbc @041041: 23 steps
lem-nat-SWbc-at041041 : Ws → ⟪ (ℓ "乥侏乥") ⟫ʷ ≈ ⟪ (ℓ "侑") ⟫ʷ
lem-nat-SWbc-at041041 c4 = derive (ℓ "乥侏乥") (ℓ "侑")
  (re 1 1 (ℓ "亜亟伉亟亜伉") ∷
   rw⁻ 0 (q70 c4) ∷
   rw 1 (q71 c4) ∷
   re 3 1 (ℓ "亠亡伂亡亠伂") ∷
   rw⁻ 2 (q72 c4) ∷
   rw 3 (q73 c4) ∷
   rw⁻ 4 (q74 c4) ∷
   rw 5 (q73 c4) ∷
   rw⁻ 6 (q72 c4) ∷
   rw⁻ 7 (q74 c4) ∷
   rw 8 (q71 c4) ∷
   rw⁻ 9 (q70 c4) ∷
   re 11 1 (ℓ "亠亡伂亡亠伂") ∷
   rw⁻ 10 (q72 c4) ∷
   rw 11 (q73 c4) ∷
   rw⁻ 12 (q74 c4) ∷
   rw 13 (q73 c4) ∷
   rw⁻ 14 (q72 c4) ∷
   rw⁻ 15 (q74 c4) ∷
   rw 16 (q75 c4) ∷
   re 2 6 (ℓ "伃") ∷
   re 5 6 (ℓ "伃") ∷
   re 0 6 (ℓ "侑") ∷ []) Eq.refl

private
  q76 : Ws → Eqn
  q76 c4 = wlE 1573 (lit c4)

-- F4-K3-K1 @0440: 1 steps
lem-F4-K3-K1-at0440 : Ws → ⟪ (ℓ "与主与中") ⟫ʷ ≈ ⟪ (ℓ "中与主与") ⟫ʷ
lem-F4-K3-K1-at0440 c4 = derive (ℓ "与主与中") (ℓ "中与主与")
  (rw⁻ 0 (q76 c4) ∷ []) Eq.refl

private
  q77 : Ws → Eqn
  q77 c4 = wlE 1578 (lit c4)

-- F4-K3-K3 @0440: 1 steps
lem-F4-K3-K3-at0440 : Ws → ⟪ (ℓ "与主与主") ⟫ʷ ≈ ⟪ (ℓ "主与主与") ⟫ʷ
lem-F4-K3-K3-at0440 c4 = derive (ℓ "与主与主") (ℓ "主与主与")
  (rw⁻ 0 (q77 c4) ∷ []) Eq.refl

private
  q78 : Ws → Eqn
  q78 c4 = wlE 1579 (lit c4)

-- F4-I-K3 @0440: 1 steps
lem-F4-I-K3-at0440 : Ws → ⟪ (ℓ "与上与主") ⟫ʷ ≈ ⟪ (ℓ "主与上与") ⟫ʷ
lem-F4-I-K3-at0440 c4 = derive (ℓ "与上与主") (ℓ "主与上与")
  (rw⁻ 0 (q78 c4) ∷ []) Eq.refl

private
  q79 : Ws → Eqn
  q79 c4 = wlE 1580 (lit c4)

-- F4-K2-K3 @0440: 1 steps
lem-F4-K2-K3-at0440 : Ws → ⟪ (ℓ "与临与主") ⟫ʷ ≈ ⟪ (ℓ "主与临与") ⟫ʷ
lem-F4-K2-K3-at0440 c4 = derive (ℓ "与临与主") (ℓ "主与临与")
  (rw⁻ 0 (q79 c4) ∷ []) Eq.refl

-- F4-K1-I @0440: 1 steps
lem-F4-K1-I-at0440 : Ws → ⟪ (ℓ "与中与上") ⟫ʷ ≈ ⟪ (ℓ "上与中与") ⟫ʷ
lem-F4-K1-I-at0440 c4 = derive (ℓ "与中与上") (ℓ "上与中与")
  (rw⁻ 0 (q58 c4) ∷ []) Eq.refl

private
  q80 : Ws → Eqn
  q80 c4 = wlE 1582 (lit c4)

-- F4-K1-K3 @0440: 1 steps
lem-F4-K1-K3-at0440 : Ws → ⟪ (ℓ "与中与主") ⟫ʷ ≈ ⟪ (ℓ "主与中与") ⟫ʷ
lem-F4-K1-K3-at0440 c4 = derive (ℓ "与中与主") (ℓ "主与中与")
  (rw⁻ 0 (q80 c4) ∷ []) Eq.refl

private
  q81 : Ws → Eqn
  q81 c4 = wlE 1584 (lit c4)

-- F4-K1-K2 @0440: 1 steps
lem-F4-K1-K2-at0440 : Ws → ⟪ (ℓ "与中与临") ⟫ʷ ≈ ⟪ (ℓ "临与中与") ⟫ʷ
lem-F4-K1-K2-at0440 c4 = derive (ℓ "与中与临") (ℓ "临与中与")
  (rw⁻ 0 (q81 c4) ∷ []) Eq.refl

-- F4-K1-K1 @0440: 1 steps
lem-F4-K1-K1-at0440 : Ws → ⟪ (ℓ "与中与中") ⟫ʷ ≈ ⟪ (ℓ "中与中与") ⟫ʷ
lem-F4-K1-K1-at0440 c4 = derive (ℓ "与中与中") (ℓ "中与中与")
  (rw⁻ 0 (q52 c4) ∷ []) Eq.refl

private
  q82 : Ws → Eqn
  q82 c4 = wpE 766 c4
  q83 : Ws → Eqn
  q83 c4 = wpE 767 c4

-- sym-ab @0413213240: 18 steps
lem-sym-ab-at0413213240 : Ws → ⟪ (ℓ "侟") ⟫ʷ ≈ ⟪ (ℓ "侖") ⟫ʷ
lem-sym-ab-at0413213240 c4 = derive (ℓ "侟") (ℓ "侖")
  (re 0 1 (ℓ "京亯來亯京來") ∷
   re 2 1 (ℓ "亰亲使亲亰使") ∷
   re 4 1 (ℓ "丸") ∷
   re 7 1 (ℓ "丸") ∷
   rw⁻ 2 (q82 c4) ∷
   rw 2 (q83 c4) ∷
   re 4 1 (ℓ "伦") ∷
   re 7 1 (ℓ "伦") ∷
   re 2 6 (ℓ "伧") ∷
   re 5 1 (ℓ "亰亲使亲亰使") ∷
   re 7 1 (ℓ "丸") ∷
   re 10 1 (ℓ "丸") ∷
   rw⁻ 5 (q82 c4) ∷
   rw 5 (q83 c4) ∷
   re 7 1 (ℓ "伦") ∷
   re 10 1 (ℓ "伦") ∷
   re 5 6 (ℓ "伧") ∷
   re 0 6 (ℓ "侖") ∷ []) Eq.refl

private
  q84 : Ws → Eqn
  q84 c4 = wlE 1592 (lit c4)
  q85 : Ws → Eqn
  q85 c4 = wlE 1593 (lit c4)
  q86 : Ws → Eqn
  q86 c4 = wlE 1594 (lit c4)
  q87 : Ws → Eqn
  q87 c4 = wlE 1595 (lit c4)
  q88 : Ws → Eqn
  q88 c4 = eqn (ℓ "伦乥") (ℓ "乥伦") (c₂ (CZ) (Swap))

-- nat-SWbc @04233240: 23 steps
lem-nat-SWbc-at04233240 : Ws → ⟪ (ℓ "乥侖乥") ⟫ʷ ≈ ⟪ (ℓ "侔") ⟫ʷ
lem-nat-SWbc-at04233240 c4 = derive (ℓ "乥侖乥") (ℓ "侔")
  (re 1 1 (ℓ "京亯伧亯京伧") ∷
   rw⁻ 0 (q84 c4) ∷
   rw 1 (q85 c4) ∷
   re 3 1 (ℓ "亨亩伦亩亨伦") ∷
   rw⁻ 2 (q86 c4) ∷
   rw 3 (q87 c4) ∷
   rw⁻ 4 (q88 c4) ∷
   rw 5 (q87 c4) ∷
   rw⁻ 6 (q86 c4) ∷
   rw⁻ 7 (q88 c4) ∷
   rw 8 (q85 c4) ∷
   rw⁻ 9 (q84 c4) ∷
   re 11 1 (ℓ "亨亩伦亩亨伦") ∷
   rw⁻ 10 (q86 c4) ∷
   rw 11 (q87 c4) ∷
   rw⁻ 12 (q88 c4) ∷
   rw 13 (q87 c4) ∷
   rw⁻ 14 (q86 c4) ∷
   rw⁻ 15 (q88 c4) ∷
   rw 16 (q75 c4) ∷
   re 2 6 (ℓ "伬") ∷
   re 5 6 (ℓ "伬") ∷
   re 0 6 (ℓ "侔") ∷ []) Eq.refl

private
  q89 : Ws → Eqn
  q89 c4 = wlE 1126 (lit c4)
  q90 : Ws → Eqn
  q90 c4 = wpE 992 c4

-- sym-ab @022440: 18 steps
lem-sym-ab-at022440 : Ws → ⟪ (ℓ "伶") ⟫ʷ ≈ ⟪ (ℓ "佟") ⟫ʷ
lem-sym-ab-at022440 c4 = derive (ℓ "伶") (ℓ "佟")
  (re 0 1 (ℓ "亨亪伔亪亨伔") ∷
   re 2 1 (ℓ "交亥伓亥交伓") ∷
   re 4 1 (ℓ "个") ∷
   re 7 1 (ℓ "个") ∷
   rw⁻ 2 (q89 c4) ∷
   rw 2 (q90 c4) ∷
   re 4 1 (ℓ "住") ∷
   re 7 1 (ℓ "住") ∷
   re 2 6 (ℓ "佞") ∷
   re 5 1 (ℓ "交亥伓亥交伓") ∷
   re 7 1 (ℓ "个") ∷
   re 10 1 (ℓ "个") ∷
   rw⁻ 5 (q89 c4) ∷
   rw 5 (q90 c4) ∷
   re 7 1 (ℓ "住") ∷
   re 10 1 (ℓ "住") ∷
   re 5 6 (ℓ "佞") ∷
   re 0 6 (ℓ "佟") ∷ []) Eq.refl

private
  q91 : Ws → Eqn
  q91 c4 = wpE 677 c4
  q92 : Ws → Eqn
  q92 c4 = wpE 678 c4
  q93 : Ws → Eqn
  q93 c4 = wpE 675 c4
  q94 : Ws → Eqn
  q94 c4 = wpE 676 c4
  q95 : Ws → Eqn
  q95 c4 = eqn (ℓ "丫佺") (ℓ "佺丫") (c₂ (Swap) (CZ))
  q96 : Ws → Eqn
  q96 c4 = wlE 18 (lit c4)

-- nat-SWbc @0413203142: 23 steps
lem-nat-SWbc-at0413203142 : Ws → ⟪ (ℓ "丫侜丫") ⟫ʷ ≈ ⟪ (ℓ "侞") ⟫ʷ
lem-nat-SWbc-at0413203142 c4 = derive (ℓ "丫侜丫") (ℓ "侞")
  (re 1 1 (ℓ "亠亣侃亣亠侃") ∷
   rw⁻ 0 (q91 c4) ∷
   rw 1 (q92 c4) ∷
   re 3 1 (ℓ "京亮佺亮京佺") ∷
   rw⁻ 2 (q93 c4) ∷
   rw 3 (q94 c4) ∷
   rw 4 (q95 c4) ∷
   rw 5 (q94 c4) ∷
   rw⁻ 6 (q93 c4) ∷
   rw 7 (q95 c4) ∷
   rw 8 (q92 c4) ∷
   rw⁻ 9 (q91 c4) ∷
   re 11 1 (ℓ "京亮佺亮京佺") ∷
   rw⁻ 10 (q93 c4) ∷
   rw 11 (q94 c4) ∷
   rw 12 (q95 c4) ∷
   rw 13 (q94 c4) ∷
   rw⁻ 14 (q93 c4) ∷
   rw 15 (q95 c4) ∷
   rw 16 (q96 c4) ∷
   re 2 6 (ℓ "佻") ∷
   re 5 6 (ℓ "佻") ∷
   re 0 6 (ℓ "侞") ∷ []) Eq.refl

private
  q97 : Ws → Eqn
  q97 c4 = wpE 211 c4
  q98 : Ws → Eqn
  q98 c4 = wpE 212 c4

-- sym-ab @0413213042: 18 steps
lem-sym-ab-at0413213042 : Ws → ⟪ (ℓ "侞") ⟫ʷ ≈ ⟪ (ℓ "侕") ⟫ʷ
lem-sym-ab-at0413213042 c4 = derive (ℓ "侞") (ℓ "侕")
  (re 0 1 (ℓ "京亯佻亯京佻") ∷
   re 2 1 (ℓ "亠亢佺亢亠佺") ∷
   re 4 1 (ℓ "乤") ∷
   re 7 1 (ℓ "乤") ∷
   rw⁻ 2 (q97 c4) ∷
   rw⁻ 2 (q98 c4) ∷
   re 4 1 (ℓ "伢") ∷
   re 7 1 (ℓ "伢") ∷
   re 2 6 (ℓ "伣") ∷
   re 5 1 (ℓ "亠亢佺亢亠佺") ∷
   re 7 1 (ℓ "乤") ∷
   re 10 1 (ℓ "乤") ∷
   rw⁻ 5 (q97 c4) ∷
   rw⁻ 5 (q98 c4) ∷
   re 7 1 (ℓ "伢") ∷
   re 10 1 (ℓ "伢") ∷
   re 5 6 (ℓ "伣") ∷
   re 0 6 (ℓ "侕") ∷ []) Eq.refl

-- sym-ab @04233042: 18 steps
lem-sym-ab-at04233042 : Ws → ⟪ (ℓ "侕") ⟫ʷ ≈ ⟪ (ℓ "侞") ⟫ʷ
lem-sym-ab-at04233042 c4 = derive (ℓ "侕") (ℓ "侞")
  (re 0 1 (ℓ "京亯伣亯京伣") ∷
   re 2 1 (ℓ "五亖伢亖五伢") ∷
   re 4 1 (ℓ "义") ∷
   re 7 1 (ℓ "义") ∷
   rw 2 (q98 c4) ∷
   rw 2 (q97 c4) ∷
   re 4 1 (ℓ "佺") ∷
   re 7 1 (ℓ "佺") ∷
   re 2 6 (ℓ "佻") ∷
   re 5 1 (ℓ "五亖伢亖五伢") ∷
   re 7 1 (ℓ "义") ∷
   re 10 1 (ℓ "义") ∷
   rw 5 (q98 c4) ∷
   rw 5 (q97 c4) ∷
   re 7 1 (ℓ "佺") ∷
   re 10 1 (ℓ "佺") ∷
   re 5 6 (ℓ "佻") ∷
   re 0 6 (ℓ "侞") ∷ []) Eq.refl

private
  q99 : Ws → Eqn
  q99 c4 = wpE 696 c4
  q100 : Ws → Eqn
  q100 c4 = wpE 695 c4

-- nat-SWbc @0413213042: 23 steps
lem-nat-SWbc-at0413213042 : Ws → ⟪ (ℓ "丫侞丫") ⟫ʷ ≈ ⟪ (ℓ "侜") ⟫ʷ
lem-nat-SWbc-at0413213042 c4 = derive (ℓ "丫侞丫") (ℓ "侜")
  (re 1 1 (ℓ "京亯佻亯京佻") ∷
   rw⁻ 0 (q93 c4) ∷
   rw 1 (q99 c4) ∷
   re 3 1 (ℓ "亠亢佺亢亠佺") ∷
   rw⁻ 2 (q91 c4) ∷
   rw 3 (q100 c4) ∷
   rw 4 (q95 c4) ∷
   rw 5 (q100 c4) ∷
   rw⁻ 6 (q91 c4) ∷
   rw 7 (q95 c4) ∷
   rw 8 (q99 c4) ∷
   rw⁻ 9 (q93 c4) ∷
   re 11 1 (ℓ "亠亢佺亢亠佺") ∷
   rw⁻ 10 (q91 c4) ∷
   rw 11 (q100 c4) ∷
   rw 12 (q95 c4) ∷
   rw 13 (q100 c4) ∷
   rw⁻ 14 (q91 c4) ∷
   rw 15 (q95 c4) ∷
   rw 16 (q96 c4) ∷
   re 2 6 (ℓ "侃") ∷
   re 5 6 (ℓ "侃") ∷
   re 0 6 (ℓ "侜") ∷ []) Eq.refl

-- sym-ab @02142140: 18 steps
lem-sym-ab-at02142140 : Ws → ⟪ (ℓ "佟") ⟫ʷ ≈ ⟪ (ℓ "伶") ⟫ʷ
lem-sym-ab-at02142140 c4 = derive (ℓ "佟") (ℓ "伶")
  (re 0 1 (ℓ "亨亪佞亪亨佞") ∷
   re 2 1 (ℓ "亰亳住亳亰住") ∷
   re 4 1 (ℓ "丿") ∷
   re 7 1 (ℓ "丿") ∷
   rw⁻ 2 (q90 c4) ∷
   rw 2 (q89 c4) ∷
   re 4 1 (ℓ "伓") ∷
   re 7 1 (ℓ "伓") ∷
   re 2 6 (ℓ "伔") ∷
   re 5 1 (ℓ "亰亳住亳亰住") ∷
   re 7 1 (ℓ "丿") ∷
   re 10 1 (ℓ "丿") ∷
   rw⁻ 5 (q90 c4) ∷
   rw 5 (q89 c4) ∷
   re 7 1 (ℓ "伓") ∷
   re 10 1 (ℓ "伓") ∷
   re 5 6 (ℓ "伔") ∷
   re 0 6 (ℓ "伶") ∷ []) Eq.refl

private
  q101 : Ws → Eqn
  q101 c4 = wlE 1613 (lit c4)
  q102 : Ws → Eqn
  q102 c4 = wlE 1614 (lit c4)

-- nat-SWbc @0440: 23 steps
lem-nat-SWbc-at0440 : Ws → ⟪ (ℓ "乥侔乥") ⟫ʷ ≈ ⟪ (ℓ "侖") ⟫ʷ
lem-nat-SWbc-at0440 c4 = derive (ℓ "乥侔乥") (ℓ "侖")
  (re 1 1 (ℓ "亨享伬享亨伬") ∷
   rw⁻ 0 (q86 c4) ∷
   rw 1 (q101 c4) ∷
   re 3 1 (ℓ "京亭伦亭京伦") ∷
   rw⁻ 2 (q84 c4) ∷
   rw 3 (q102 c4) ∷
   rw⁻ 4 (q88 c4) ∷
   rw 5 (q102 c4) ∷
   rw⁻ 6 (q84 c4) ∷
   rw⁻ 7 (q88 c4) ∷
   rw 8 (q101 c4) ∷
   rw⁻ 9 (q86 c4) ∷
   re 11 1 (ℓ "京亭伦亭京伦") ∷
   rw⁻ 10 (q84 c4) ∷
   rw 11 (q102 c4) ∷
   rw⁻ 12 (q88 c4) ∷
   rw 13 (q102 c4) ∷
   rw⁻ 14 (q84 c4) ∷
   rw⁻ 15 (q88 c4) ∷
   rw 16 (q75 c4) ∷
   re 2 6 (ℓ "伧") ∷
   re 5 6 (ℓ "伧") ∷
   re 0 6 (ℓ "侖") ∷ []) Eq.refl

-- sym-ab @04233240: 18 steps
lem-sym-ab-at04233240 : Ws → ⟪ (ℓ "侖") ⟫ʷ ≈ ⟪ (ℓ "侟") ⟫ʷ
lem-sym-ab-at04233240 c4 = derive (ℓ "侖") (ℓ "侟")
  (re 0 1 (ℓ "京亯伧亯京伧") ∷
   re 2 1 (ℓ "亨亩伦亩亨伦") ∷
   re 4 1 (ℓ "个") ∷
   re 7 1 (ℓ "个") ∷
   rw⁻ 2 (q83 c4) ∷
   rw 2 (q82 c4) ∷
   re 4 1 (ℓ "使") ∷
   re 7 1 (ℓ "使") ∷
   re 2 6 (ℓ "來") ∷
   re 5 1 (ℓ "亨亩伦亩亨伦") ∷
   re 7 1 (ℓ "个") ∷
   re 10 1 (ℓ "个") ∷
   rw⁻ 5 (q83 c4) ∷
   rw 5 (q82 c4) ∷
   re 7 1 (ℓ "使") ∷
   re 10 1 (ℓ "使") ∷
   re 5 6 (ℓ "來") ∷
   re 0 6 (ℓ "侟") ∷ []) Eq.refl

private
  q103 : Ws → Eqn
  q103 c4 = wpE 719 c4
  q104 : Ws → Eqn
  q104 c4 = wlE 1659 (lit c4)
  q105 : Ws → Eqn
  q105 c4 = wlE 1660 (lit c4)
  q106 : Ws → Eqn
  q106 c4 = wlE 11 (lit c4)
  q107 : Ws → Eqn
  q107 c4 = wlE 12 (lit c4)

-- nat-S @0410213243: 31 steps
lem-nat-S-at0410213243 : Ws → ⟪ (ℓ "乥俊乥") ⟫ʷ ≈ ⟪ (ℓ "俟") ⟫ʷ
lem-nat-S-at0410213243 c4 = derive (ℓ "乥俊乥") (ℓ "俟")
  (re 1 1 (ℓ "佔亓俈亓俉") ∷
   re 3 1 (ℓ "乹") ∷
   re 5 1 (ℓ "乺") ∷
   re 1 1 (ℓ "亜亞体亞亜体") ∷
   rw⁻ 0 (q70 c4) ∷
   rw 1 (q103 c4) ∷
   re 3 1 (ℓ "亨享佒享亨佒") ∷
   re 5 1 (ℓ "乻") ∷
   re 8 1 (ℓ "乻") ∷
   rw⁻ 2 (q104 c4) ∷
   re 4 1 (ℓ "佷") ∷
   re 7 1 (ℓ "佷") ∷
   re 2 6 (ℓ "佸") ∷
   rw 3 (q103 c4) ∷
   rw⁻ 4 (q70 c4) ∷
   re 6 1 (ℓ "亨享佒享亨佒") ∷
   re 8 1 (ℓ "乻") ∷
   re 11 1 (ℓ "乻") ∷
   rw⁻ 5 (q104 c4) ∷
   re 7 1 (ℓ "佷") ∷
   re 10 1 (ℓ "佷") ∷
   re 5 6 (ℓ "佸") ∷
   rw 6 (q105 c4) ∷
   rw⁻ 7 (q106 c4) ∷
   rw 8 (q105 c4) ∷
   rw⁻ 9 (q107 c4) ∷
   rw 10 (q75 c4) ∷
   re 0 6 (ℓ "佹") ∷
   re 2 1 (ℓ "保") ∷
   re 4 1 (ℓ "俞") ∷
   re 0 5 (ℓ "俟") ∷ []) Eq.refl

private
  q108 : Ws → Eqn
  q108 c4 = wpE 732 c4
  q109 : Ws → Eqn
  q109 c4 = wpE 733 c4

-- sym-ab @04122140: 18 steps
lem-sym-ab-at04122140 : Ws → ⟪ (ℓ "侙") ⟫ʷ ≈ ⟪ (ℓ "侔") ⟫ʷ
lem-sym-ab-at04122140 c4 = derive (ℓ "侙") (ℓ "侔")
  (re 0 1 (ℓ "亨享你享亨你") ∷
   re 2 1 (ℓ "亰亱佚亱亰佚") ∷
   re 4 1 (ℓ "丱") ∷
   re 7 1 (ℓ "丱") ∷
   rw⁻ 2 (q108 c4) ∷
   rw 2 (q109 c4) ∷
   re 4 1 (ℓ "伦") ∷
   re 7 1 (ℓ "伦") ∷
   re 2 6 (ℓ "伬") ∷
   re 5 1 (ℓ "亰亱佚亱亰佚") ∷
   re 7 1 (ℓ "丱") ∷
   re 10 1 (ℓ "丱") ∷
   rw⁻ 5 (q108 c4) ∷
   rw 5 (q109 c4) ∷
   re 7 1 (ℓ "伦") ∷
   re 10 1 (ℓ "伦") ∷
   re 5 6 (ℓ "伬") ∷
   re 0 6 (ℓ "侔") ∷ []) Eq.refl

private
  q110 : Ws → Eqn
  q110 c4 = wlE 1596 (lit c4)
  q111 : Ws → Eqn
  q111 c4 = wpE 1437 c4

-- sym-ab @0413203142: 18 steps
lem-sym-ab-at0413203142 : Ws → ⟪ (ℓ "侜") ⟫ʷ ≈ ⟪ (ℓ "侐") ⟫ʷ
lem-sym-ab-at0413203142 c4 = derive (ℓ "侜") (ℓ "侐")
  (re 0 1 (ℓ "亠亣侃亣亠侃") ∷
   re 2 1 (ℓ "京亮佺亮京佺") ∷
   re 4 1 (ℓ "乤") ∷
   re 7 1 (ℓ "乤") ∷
   rw⁻ 2 (q110 c4) ∷
   rw⁻ 2 (q111 c4) ∷
   re 4 1 (ℓ "仸") ∷
   re 7 1 (ℓ "仸") ∷
   re 2 6 (ℓ "仹") ∷
   re 5 1 (ℓ "京亮佺亮京佺") ∷
   re 7 1 (ℓ "乤") ∷
   re 10 1 (ℓ "乤") ∷
   rw⁻ 5 (q110 c4) ∷
   rw⁻ 5 (q111 c4) ∷
   re 7 1 (ℓ "仸") ∷
   re 10 1 (ℓ "仸") ∷
   re 5 6 (ℓ "仹") ∷
   re 0 6 (ℓ "侐") ∷ []) Eq.refl

-- sym-ab @0410233142: 18 steps
lem-sym-ab-at0410233142 : Ws → ⟪ (ℓ "侐") ⟫ʷ ≈ ⟪ (ℓ "侜") ⟫ʷ
lem-sym-ab-at0410233142 c4 = derive (ℓ "侐") (ℓ "侜")
  (re 0 1 (ℓ "亠亣仹亣亠仹") ∷
   re 2 1 (ℓ "五井仸井五仸") ∷
   re 4 1 (ℓ "丱") ∷
   re 7 1 (ℓ "丱") ∷
   rw 2 (q111 c4) ∷
   rw 2 (q110 c4) ∷
   re 4 1 (ℓ "佺") ∷
   re 7 1 (ℓ "佺") ∷
   re 2 6 (ℓ "侃") ∷
   re 5 1 (ℓ "五井仸井五仸") ∷
   re 7 1 (ℓ "丱") ∷
   re 10 1 (ℓ "丱") ∷
   rw 5 (q111 c4) ∷
   rw 5 (q110 c4) ∷
   re 7 1 (ℓ "佺") ∷
   re 10 1 (ℓ "佺") ∷
   re 5 6 (ℓ "侃") ∷
   re 0 6 (ℓ "侜") ∷ []) Eq.refl

-- sym-ab @0440: 18 steps
lem-sym-ab-at0440 : Ws → ⟪ (ℓ "侔") ⟫ʷ ≈ ⟪ (ℓ "侙") ⟫ʷ
lem-sym-ab-at0440 c4 = derive (ℓ "侔") (ℓ "侙")
  (re 0 1 (ℓ "亨享伬享亨伬") ∷
   re 2 1 (ℓ "京亭伦亭京伦") ∷
   re 4 1 (ℓ "个") ∷
   re 7 1 (ℓ "个") ∷
   rw⁻ 2 (q109 c4) ∷
   rw 2 (q108 c4) ∷
   re 4 1 (ℓ "佚") ∷
   re 7 1 (ℓ "佚") ∷
   re 2 6 (ℓ "你") ∷
   re 5 1 (ℓ "京亭伦亭京伦") ∷
   re 7 1 (ℓ "个") ∷
   re 10 1 (ℓ "个") ∷
   rw⁻ 5 (q109 c4) ∷
   rw 5 (q108 c4) ∷
   re 7 1 (ℓ "佚") ∷
   re 10 1 (ℓ "佚") ∷
   re 5 6 (ℓ "你") ∷
   re 0 6 (ℓ "侙") ∷ []) Eq.refl

-- F4-S0-K1 @0440: 1 steps
lem-F4-S0-K1-at0440 : Ws → ⟪ (ℓ "与丽与中") ⟫ʷ ≈ ⟪ (ℓ "中与丽与") ⟫ʷ
lem-F4-S0-K1-at0440 c4 = derive (ℓ "与丽与中") (ℓ "中与丽与")
  (rw⁻ 0 (q51 c4) ∷ []) Eq.refl

private
  q112 : Ws → Eqn
  q112 c4 = wpE 516 c4
  q113 : Ws → Eqn
  q113 c4 = wlE 756 (lit c4)

-- sym-ab @0410233241: 18 steps
lem-sym-ab-at0410233241 : Ws → ⟪ (ℓ "侑") ⟫ʷ ≈ ⟪ (ℓ "依") ⟫ʷ
lem-sym-ab-at0410233241 c4 = derive (ℓ "侑") (ℓ "依")
  (re 0 1 (ℓ "亠亣伃亣亠伃") ∷
   re 2 1 (ℓ "亜亝伂亝亜伂") ∷
   re 4 1 (ℓ "个") ∷
   re 7 1 (ℓ "个") ∷
   rw 2 (q112 c4) ∷
   rw 2 (q113 c4) ∷
   re 4 1 (ℓ "侉") ∷
   re 7 1 (ℓ "侉") ∷
   re 2 6 (ℓ "侊") ∷
   re 5 1 (ℓ "亜亝伂亝亜伂") ∷
   re 7 1 (ℓ "个") ∷
   re 10 1 (ℓ "个") ∷
   rw 5 (q112 c4) ∷
   rw 5 (q113 c4) ∷
   re 7 1 (ℓ "侉") ∷
   re 10 1 (ℓ "侉") ∷
   re 5 6 (ℓ "侊") ∷
   re 0 6 (ℓ "依") ∷ []) Eq.refl

private
  q114 : Ws → Eqn
  q114 c4 = wpE 1488 c4

-- F4-S0-K2 @0440: 1 steps
lem-F4-S0-K2-at0440 : Ws → ⟪ (ℓ "与丽与临") ⟫ʷ ≈ ⟪ (ℓ "临与丽与") ⟫ʷ
lem-F4-S0-K2-at0440 c4 = derive (ℓ "与丽与临") (ℓ "临与丽与")
  (rw⁻ 0 (q114 c4) ∷ []) Eq.refl

private
  q115 : Ws → Eqn
  q115 c4 = wpE 1436 c4
  q116 : Ws → Eqn
  q116 c4 = wpE 1503 c4

-- sym-ab @0412233140: 18 steps
lem-sym-ab-at0412233140 : Ws → ⟪ (ℓ "供") ⟫ʷ ≈ ⟪ (ℓ "侠") ⟫ʷ
lem-sym-ab-at0412233140 c4 = derive (ℓ "供") (ℓ "侠")
  (re 0 1 (ℓ "亰亳佛亳亰佛") ∷
   re 2 1 (ℓ "亨亪佚亪亨佚") ∷
   re 4 1 (ℓ "丱") ∷
   re 7 1 (ℓ "丱") ∷
   rw⁻ 2 (q115 c4) ∷
   rw 2 (q116 c4) ∷
   re 4 1 (ℓ "使") ∷
   re 7 1 (ℓ "使") ∷
   re 2 6 (ℓ "侀") ∷
   re 5 1 (ℓ "亨亪佚亪亨佚") ∷
   re 7 1 (ℓ "丱") ∷
   re 10 1 (ℓ "丱") ∷
   rw⁻ 5 (q115 c4) ∷
   rw 5 (q116 c4) ∷
   re 7 1 (ℓ "使") ∷
   re 10 1 (ℓ "使") ∷
   re 5 6 (ℓ "侀") ∷
   re 0 6 (ℓ "侠") ∷ []) Eq.refl

-- sym-ab @04133140: 18 steps
lem-sym-ab-at04133140 : Ws → ⟪ (ℓ "侠") ⟫ʷ ≈ ⟪ (ℓ "供") ⟫ʷ
lem-sym-ab-at04133140 c4 = derive (ℓ "侠") (ℓ "供")
  (re 0 1 (ℓ "亰亳侀亳亰侀") ∷
   re 2 1 (ℓ "京亮使亮京使") ∷
   re 4 1 (ℓ "丸") ∷
   re 7 1 (ℓ "丸") ∷
   rw⁻ 2 (q116 c4) ∷
   rw 2 (q115 c4) ∷
   re 4 1 (ℓ "佚") ∷
   re 7 1 (ℓ "佚") ∷
   re 2 6 (ℓ "佛") ∷
   re 5 1 (ℓ "京亮使亮京使") ∷
   re 7 1 (ℓ "丸") ∷
   re 10 1 (ℓ "丸") ∷
   rw⁻ 5 (q116 c4) ∷
   rw 5 (q115 c4) ∷
   re 7 1 (ℓ "佚") ∷
   re 10 1 (ℓ "佚") ∷
   re 5 6 (ℓ "佛") ∷
   re 0 6 (ℓ "供") ∷ []) Eq.refl

-- F4-S0-I @0440: 1 steps
lem-F4-S0-I-at0440 : Ws → ⟪ (ℓ "与丽与上") ⟫ʷ ≈ ⟪ (ℓ "上与丽与") ⟫ʷ
lem-F4-S0-I-at0440 c4 = derive (ℓ "与丽与上") (ℓ "上与丽与")
  (rw⁻ 0 (q57 c4) ∷ []) Eq.refl

private
  q117 : Ws → Eqn
  q117 c4 = wpE 1518 c4

-- F4-S0-K3 @0440: 1 steps
lem-F4-S0-K3-at0440 : Ws → ⟪ (ℓ "与丽与主") ⟫ʷ ≈ ⟪ (ℓ "主与丽与") ⟫ʷ
lem-F4-S0-K3-at0440 c4 = derive (ℓ "与丽与主") (ℓ "主与丽与")
  (rw⁻ 0 (q117 c4) ∷ []) Eq.refl
