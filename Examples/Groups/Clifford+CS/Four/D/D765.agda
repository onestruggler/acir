{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD765 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D765 (W : Ws) (Sᴰ : SD765) where

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
  lem-ROT-form : St 2018
  lem-ROT-form = pickᴰ 0 Sᴰ
  lem-pass-CS02-CCZ012-vs-TOFF012-CS03-TOFF012-CSd03 : St 3065
  lem-pass-CS02-CCZ012-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 1 Sᴰ
  lem-ROT≡cF : St 1425
  lem-ROT≡cF = pickᴰ 2 Sᴰ
  lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡S-e≡1⟩ : St 3066
  lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡S-e≡1⟩ = pickᴰ 3 Sᴰ
  lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡Sd-e≡1⟩ : St 3067
  lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡Sd-e≡1⟩ = pickᴰ 4 Sᴰ
  lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SKSS-e≡1⟩ : St 3068
  lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SKSS-e≡1⟩ = pickᴰ 5 Sᴰ
  lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SKdSd-e≡1⟩ : St 3069
  lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SKdSd-e≡1⟩ = pickᴰ 6 Sᴰ
  lem-pass-X3-CK31-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 3070
  lem-pass-X3-CK31-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 7 Sᴰ
  lem-pass-X3-CKd31-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 3071
  lem-pass-X3-CKd31-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 8 Sᴰ
  lem-pass-X3-CS31-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 3072
  lem-pass-X3-CS31-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 9 Sᴰ
  lem-pass-X3-CSd31-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 3073
  lem-pass-X3-CSd31-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 10 Sᴰ
  lem-pass-X3-CK32-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 2135
  lem-pass-X3-CK32-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 11 Sᴰ
  lem-pass-X3-CKd32-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 2136
  lem-pass-X3-CKd32-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 12 Sᴰ
  lem-pass-X3-CS32-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 3074
  lem-pass-X3-CS32-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 13 Sᴰ
  lem-pass-X3-CSd32-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 3075
  lem-pass-X3-CSd32-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 14 Sᴰ
  lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-3 : St 2689
  lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-3 = pickᴰ 15 Sᴰ
  lem-pass-CK31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : St 3076
  lem-pass-CK31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = pickᴰ 16 Sᴰ
  lem-pass-CKd31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : St 3077
  lem-pass-CKd31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = pickᴰ 17 Sᴰ
  lem-pass-CS31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : St 3078
  lem-pass-CS31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = pickᴰ 18 Sᴰ
  lem-pass-CSd31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : St 3079
  lem-pass-CSd31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = pickᴰ 19 Sᴰ
  lem-ca-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3 : St 2732
  lem-ca-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3 = pickᴰ 20 Sᴰ
  lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡KSSK-e≡1⟩ : St 3080
  lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡KSSK-e≡1⟩ = pickᴰ 21 Sᴰ
  lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SdKSS-e≡1⟩ : St 3081
  lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SdKSS-e≡1⟩ = pickᴰ 22 Sᴰ
  lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩ : St 3082
  lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩ = pickᴰ 23 Sᴰ
  lem-CAw1-SS-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ : St 3083
  lem-CAw1-SS-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ = pickᴰ 24 Sᴰ
  lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SSKSSK-e≡1⟩ : St 3084
  lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SSKSSK-e≡1⟩ = pickᴰ 25 Sᴰ
  lem-ca-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩-3 : St 2971
  lem-ca-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩-3 = pickᴰ 26 Sᴰ
  lem-PP0-sep-inv : St 3085
  lem-PP0-sep-inv = pickᴰ 27 Sᴰ
  lem-PP1-split : St 3086
  lem-PP1-split = pickᴰ 28 Sᴰ
  lem-REL-S : St 3087
  lem-REL-S = pickᴰ 29 Sᴰ
  lem-REL-SKSS : St 3088
  lem-REL-SKSS = pickᴰ 30 Sᴰ
  lem-REL-Sd : St 3089
  lem-REL-Sd = pickᴰ 31 Sᴰ
  lem-REL-SdKSS : St 3090
  lem-REL-SdKSS = pickᴰ 32 Sᴰ
  lem-S3i : St 3091
  lem-S3i = pickᴰ 33 Sᴰ
  lem-h-gad : St 3092
  lem-h-gad = pickᴰ 34 Sᴰ
  lem-merge-R0 : St 3093
  lem-merge-R0 = pickᴰ 35 Sᴰ
  lem-merge-a1 : St 3094
  lem-merge-a1 = pickᴰ 36 Sᴰ
  lem-merge-all-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ : St 3095
  lem-merge-all-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ = pickᴰ 37 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : St 3096
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = pickᴰ 38 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 : St 3097
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 = pickᴰ 39 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : St 3098
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = pickᴰ 40 Sᴰ
  lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 3099
  lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 41 Sᴰ
  lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩-at1023 : St 3100
  lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩-at1023 = pickᴰ 42 Sᴰ

private
  q1 : Eqn
  q1 = sE 1425 lem-ROT≡cF
  q2 : Eqn
  q2 = sE 2018 lem-ROT-form
  q3 : Eqn
  q3 = eqn (ℓ "上丼") (ℓ "丼上") (low₁-comm (K) (Swap))
  q4 : Eqn
  q4 = wE 2560 W
  q5 : Eqn
  q5 = eqn (ℓ "下乏") (ℓ "乏下") (low₁-comm ((K • iI)) ((Swap ↑)))
  q6 : Eqn
  q6 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q7 : Eqn
  q7 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q8 : Eqn
  q8 = wE 1 W
  q9 : Eqn
  q9 = sE 3091 lem-S3i
  q10 : Eqn
  q10 = eqn (ℓ "三乏") (ℓ "乏三") (low₁-comm ((S • S • S)) ((Swap ↑)))
  q11 : Eqn
  q11 = eqn (ℓ "下丼") (ℓ "丼下") (low₁-comm ((K • iI)) (Swap))
  q12 : Eqn
  q12 = wE 14 W
  q13 : Eqn
  q13 = wE 23 W
  q14 : Eqn
  q14 = sE 2018 lem-ROT-form
  q15 : Eqn
  q15 = sE 1425 lem-ROT≡cF

-- SW12-ROT: 17 steps
lem-SW12-ROT : ⟪ (ℓ "丼临乙习丿习乙丿与临乙习丿习乙丿丼") ⟫ʷ ≈ ⟪ (ℓ "临乙习丿习乙丿与临乙习丿习乙丿") ⟫ʷ
lem-SW12-ROT = derive (ℓ "丼临乙习丿习乙丿与临乙习丿习乙丿丼") (ℓ "临乙习丿习乙丿与临乙习丿习乙丿")
  (rw 1 q1 ∷
   rw 1 q2 ∷
   rw⁻ 0 q3 ∷
   rw 1 q4 ∷
   rw⁻ 4 q5 ∷
   rw⁻ 5 q6 ∷
   rw⁻ 6 q7 ∷
   rw 12 q8 ∷
   rw 7 q9 ∷
   rw⁻ 11 q5 ∷
   rw⁻ 12 q10 ∷
   rw⁻ 13 q7 ∷
   rw 18 q11 ∷
   rw 17 q12 ∷
   rw 14 q13 ∷
   rw⁻ 0 q14 ∷
   rw⁻ 0 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = sE 3086 lem-PP1-split
  q17 : Eqn
  q17 = sE 3065 lem-pass-CS02-CCZ012-vs-TOFF012-CS03-TOFF012-CSd03
  q18 : Eqn
  q18 = sE 3085 lem-PP0-sep-inv
  q19 : Eqn
  q19 = sE 3086 lem-PP1-split

-- adj01: 4 steps
lem-adj01 : ⟪ (ℓ "九中九丮习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举九中九丮") ⟫ʷ
lem-adj01 = derive (ℓ "九中九丮习丽习举") (ℓ "习丽习举九中九丮")
  (rw 4 q16 ∷
   rw⁻ 0 q17 ∷
   rw 2 q18 ∷
   rw⁻ 0 q19 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = sE 3067 lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡Sd-e≡1⟩
  q21 : Eqn
  q21 = sE 3082 lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩
  q22 : Eqn
  q22 = sE 3089 lem-REL-Sd

-- prod Gad(t=0, W=(), d=1, e=1) Gad(t=0, W=(), d=SK, e=-1): 3 steps
lem-prod-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "九中九丮丈上中九丮九下三") ⟫ʷ ≈ ⟪ (ℓ "丈丈下三九中九丮丈上三三") ⟫ʷ
lem-prod-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ = derive (ℓ "九中九丮丈上中九丮九下三") (ℓ "丈丈下三九中九丮丈上三三")
  (rw 0 q20 ∷
   rw 6 q21 ∷
   rw 0 q22 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = sE 3081 lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SdKSS-e≡1⟩
  q24 : Eqn
  q24 = sE 3080 lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡KSSK-e≡1⟩
  q25 : Eqn
  q25 = sE 3090 lem-REL-SdKSS

-- prod Gad(t=0, W=(), d=SK, e=-1) Gad(t=0, W=(), d=1, e=-1): 3 steps
lem-prod-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡-1⟩ : ⟪ (ℓ "丈上中九丮九下三中九丮九") ⟫ʷ ≈ ⟪ (ℓ "丈丈下丈丈九中九丮三三上三三") ⟫ʷ
lem-prod-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡-1⟩ = derive (ℓ "丈上中九丮九下三中九丮九") (ℓ "丈丈下丈丈九中九丮三三上三三")
  (rw 0 q23 ∷
   rw 12 q24 ∷
   rw 0 q25 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = wE 1357 W
  q27 : Eqn
  q27 = wE 3 W
  q28 : Eqn
  q28 = wE 4 W
  q29 : Eqn
  q29 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q30 : Eqn
  q30 = wE 43 W
  q31 : Eqn
  q31 = sE 3094 lem-merge-a1
  q32 : Eqn
  q32 = wE 1380 W
  q33 : Eqn
  q33 = wE 1379 W
  q34 : Eqn
  q34 = wE 1381 W
  q35 : Eqn
  q35 = wE 389 W

-- merge a1 ^-1: 63 steps
lem-merge-a1-ᵖ-1 : ⟪ (ℓ "丘丽习举习丘丽习举习") ⟫ʷ ≈ ⟪ (ℓ "乚丮") ⟫ʷ
lem-merge-a1-ᵖ-1 = derive (ℓ "丘丽习举习丘丽习举习") (ℓ "乚丮")
  (rw 10 q8 ∷
   rw 11 q26 ∷
   rw 12 q8 ∷
   re 10 3 (ℓ "中") ∷
   rw 13 q8 ∷
   re 11 3 (ℓ "丮") ∷
   rw 12 q27 ∷
   rw 11 q8 ∷
   rw 12 q28 ∷
   re 12 1 (ℓ "丶丣丷丣丧") ∷
   rw 13 q8 ∷
   re 11 3 (ℓ "丽") ∷
   rw⁻ 12 q29 ∷
   rw 15 q8 ∷
   re 13 3 (ℓ "举") ∷
   rw⁻ 14 q29 ∷
   rw 17 q8 ∷
   re 15 3 (ℓ "中") ∷
   rw 11 q8 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q27 ∷
   rw⁻ 13 q29 ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 14 q27 ∷
   rw⁻ 15 q29 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 16 q27 ∷
   rw 12 q30 ∷
   re 12 5 (ℓ "乙") ∷
   re 11 3 (ℓ "乚") ∷
   re 13 1 (ℓ "丶丣丷丣丧") ∷
   rw 14 q8 ∷
   re 12 3 (ℓ "丽") ∷
   rw⁻ 13 q29 ∷
   rw 16 q8 ∷
   re 14 3 (ℓ "举") ∷
   rw⁻ 15 q29 ∷
   rw 18 q8 ∷
   re 16 3 (ℓ "中") ∷
   rw 12 q8 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q27 ∷
   rw⁻ 14 q29 ∷
   re 16 1 (ℓ "乏丷乏") ∷
   rw 15 q27 ∷
   rw⁻ 16 q29 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 17 q27 ∷
   rw 13 q30 ∷
   re 13 5 (ℓ "乙") ∷
   re 12 3 (ℓ "乚") ∷
   rw 13 q27 ∷
   rw⁻ 10 q31 ∷
   rw 9 q32 ∷
   rw 8 q33 ∷
   rw 7 q32 ∷
   rw 6 q34 ∷
   rw 5 q35 ∷
   rw 4 q32 ∷
   rw 3 q33 ∷
   rw 2 q32 ∷
   rw 1 q34 ∷
   rw 0 q35 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = wE 225 W
  q37 : Eqn
  q37 = wE 1732 W
  q38 : Eqn
  q38 = wE 116 W
  q39 : Eqn
  q39 = wE 45 W
  q40 : Eqn
  q40 = wE 231 W
  q41 : Eqn
  q41 = wE 54 W
  q42 : Eqn
  q42 = wE 1726 W
  q43 : Eqn
  q43 = sE 3093 lem-merge-R0

-- split R: 23 steps
lem-split-R : ⟪ (ℓ "丈上中九丮九下三") ⟫ʷ ≈ ⟪ (ℓ "丷丈九三丞丈上九中九丮下三丞") ⟫ʷ
lem-split-R = derive (ℓ "丈上中九丮九下三") (ℓ "丷丈九三丞丈上九中九丮下三丞")
  (rw 8 q36 ∷
   rw 9 q37 ∷
   rw 10 q38 ∷
   rw 11 q8 ∷
   rw 12 q26 ∷
   rw 13 q8 ∷
   re 11 3 (ℓ "中") ∷
   rw 14 q8 ∷
   re 12 3 (ℓ "丮") ∷
   rw 13 q27 ∷
   rw 12 q39 ∷
   rw 13 q8 ∷
   rw 14 q40 ∷
   rw 15 q8 ∷
   re 13 3 (ℓ "丮") ∷
   rw 16 q8 ∷
   re 14 3 (ℓ "中") ∷
   rw 15 q27 ∷
   rw 14 q39 ∷
   rw 15 q41 ∷
   rw 16 q42 ∷
   rw 17 q36 ∷
   rw 0 q43 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = sE 3066 lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡S-e≡1⟩
  q45 : Eqn
  q45 = sE 3069 lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SKdSd-e≡1⟩
  q46 : Eqn
  q46 = sE 3087 lem-REL-S

-- prod Gad(t=0, W=(), d=1, e=1) Gad(t=0, W=(), d=SK, e=1): 3 steps
lem-prod-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ : ⟪ (ℓ "九中九丮丈上九中九丮下三") ⟫ʷ ≈ ⟪ (ℓ "下三九中九丮丈上") ⟫ʷ
lem-prod-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩ = derive (ℓ "九中九丮丈上九中九丮下三") (ℓ "下三九中九丮丈上")
  (rw 0 q44 ∷
   rw 6 q45 ∷
   rw 0 q46 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = sE 3068 lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SKSS-e≡1⟩
  q48 : Eqn
  q48 = sE 3084 lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SSKSSK-e≡1⟩
  q49 : Eqn
  q49 = sE 3088 lem-REL-SKSS

-- prod Gad(t=0, W=(), d=SK, e=1) Gad(t=0, W=(), d=1, e=-1): 3 steps
lem-prod-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡-1⟩ : ⟪ (ℓ "丈上九中九丮下三中九丮九") ⟫ʷ ≈ ⟪ (ℓ "下丈丈九中九丮三三上") ⟫ʷ
lem-prod-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡-1⟩ = derive (ℓ "丈上九中九丮下三中九丮九") (ℓ "下丈丈九中九丮三三上")
  (rw 0 q47 ∷
   rw 12 q48 ∷
   rw 0 q49 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = wE 5 W
  q51 : Eqn
  q51 = wE 217 W
  q52 : Eqn
  q52 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q53 : Eqn
  q53 = wE 189 W
  q54 : Eqn
  q54 = wE 7 W
  q55 : Eqn
  q55 = wE 8 W
  q56 : Eqn
  q56 = wE 9 W
  q57 : Eqn
  q57 = wE 10 W
  q58 : Eqn
  q58 = wE 11 W
  q59 : Eqn
  q59 = wE 127 W
  q60 : Eqn
  q60 = wE 118 W
  q61 : Eqn
  q61 = wE 274 W
  q62 : Eqn
  q62 = wE 480 W
  q63 : Eqn
  q63 = wE 481 W
  q64 : Eqn
  q64 = sE 3092 lem-h-gad
  q65 : Eqn
  q65 = wE 311 W
  q66 : Eqn
  q66 = wE 123 W
  q67 : Eqn
  q67 = wE 27 W
  q68 : Eqn
  q68 = wE 28 W
  q69 : Eqn
  q69 = wE 29 W
  q70 : Eqn
  q70 = wE 25 W
  q71 : Eqn
  q71 = wE 124 W
  q72 : Eqn
  q72 = wE 322 W
  q73 : Eqn
  q73 = wE 313 W
  q74 : Eqn
  q74 = wE 312 W
  q75 : Eqn
  q75 = wE 31 W

-- h-gad @1023: 140 steps
lem-h-gad-at1023 : ⟪ (ℓ "丒两乙九丯九乙丯丈两乙九丯九乙丯丒") ⟫ʷ ≈ ⟪ (ℓ "与丐习丽习举丑丏") ⟫ʷ
lem-h-gad-at1023 = derive (ℓ "丒两乙九丯九乙丯丈两乙九丯九乙丯丒") (ℓ "与丐习丽习举丑丏")
  (rw 17 q50 ∷
   rw 16 q51 ∷
   re 15 1 (ℓ "乏丩乏") ∷
   rw⁻ 17 q52 ∷
   rw 16 q53 ∷
   rw⁻ 15 q52 ∷
   re 16 3 (ℓ "丿") ∷
   re 14 1 (ℓ "丶丣丷丣丧") ∷
   rw 18 q54 ∷
   rw 17 q55 ∷
   rw 16 q56 ∷
   rw 15 q55 ∷
   rw 14 q57 ∷
   rw 15 q58 ∷
   re 15 5 (ℓ "乙") ∷
   re 13 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 20 q59 ∷
   rw 19 q60 ∷
   rw 18 q54 ∷
   rw 17 q55 ∷
   rw 16 q56 ∷
   rw 15 q55 ∷
   rw 14 q57 ∷
   rw 13 q60 ∷
   rw 14 q61 ∷
   re 14 8 (ℓ "习") ∷
   re 12 1 (ℓ "乏丩乏") ∷
   rw⁻ 14 q52 ∷
   rw 13 q53 ∷
   rw⁻ 12 q52 ∷
   re 13 3 (ℓ "丿") ∷
   re 11 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 18 q59 ∷
   rw 17 q60 ∷
   rw 16 q54 ∷
   rw 15 q55 ∷
   rw 14 q56 ∷
   rw 13 q55 ∷
   rw 12 q57 ∷
   rw 11 q60 ∷
   rw 12 q61 ∷
   re 12 8 (ℓ "习") ∷
   re 10 1 (ℓ "丶丣丷丣丧") ∷
   rw 14 q54 ∷
   rw 13 q55 ∷
   rw 12 q56 ∷
   rw 11 q55 ∷
   rw 10 q57 ∷
   rw 11 q58 ∷
   re 11 5 (ℓ "乙") ∷
   rw 9 q62 ∷
   rw 8 q63 ∷
   re 7 1 (ℓ "乏丩乏") ∷
   rw⁻ 9 q52 ∷
   rw 8 q53 ∷
   rw⁻ 7 q52 ∷
   re 8 3 (ℓ "丿") ∷
   re 6 1 (ℓ "丶丣丷丣丧") ∷
   rw 10 q54 ∷
   rw 9 q55 ∷
   rw 8 q56 ∷
   rw 7 q55 ∷
   rw 6 q57 ∷
   rw 7 q58 ∷
   re 7 5 (ℓ "乙") ∷
   re 5 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 12 q59 ∷
   rw 11 q60 ∷
   rw 10 q54 ∷
   rw 9 q55 ∷
   rw 8 q56 ∷
   rw 7 q55 ∷
   rw 6 q57 ∷
   rw 5 q60 ∷
   rw 6 q61 ∷
   re 6 8 (ℓ "习") ∷
   re 4 1 (ℓ "乏丩乏") ∷
   rw⁻ 6 q52 ∷
   rw 5 q53 ∷
   rw⁻ 4 q52 ∷
   re 5 3 (ℓ "丿") ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 10 q59 ∷
   rw 9 q60 ∷
   rw 8 q54 ∷
   rw 7 q55 ∷
   rw 6 q56 ∷
   rw 5 q55 ∷
   rw 4 q57 ∷
   rw 3 q60 ∷
   rw 4 q61 ∷
   re 4 8 (ℓ "习") ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q54 ∷
   rw 5 q55 ∷
   rw 4 q56 ∷
   rw 3 q55 ∷
   rw 2 q57 ∷
   rw 3 q58 ∷
   re 3 5 (ℓ "乙") ∷
   rw 1 q62 ∷
   rw 0 q51 ∷
   rw 1 q64 ∷
   rw 0 q65 ∷
   rw 1 q66 ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 2 q66 ∷
   rw 3 q67 ∷
   rw 4 q68 ∷
   rw 5 q69 ∷
   rw 6 q68 ∷
   rw 7 q70 ∷
   rw 8 q66 ∷
   rw 9 q71 ∷
   rw 2 q61 ∷
   re 2 8 (ℓ "习") ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 3 q52 ∷
   rw 4 q70 ∷
   rw 5 q52 ∷
   re 3 3 (ℓ "丽") ∷
   re 5 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 4 q66 ∷
   rw 5 q67 ∷
   rw 6 q68 ∷
   rw 7 q69 ∷
   rw 8 q68 ∷
   rw 9 q70 ∷
   rw 10 q66 ∷
   rw 11 q71 ∷
   rw 4 q61 ∷
   re 4 8 (ℓ "习") ∷
   re 6 1 (ℓ "乏丨乏") ∷
   rw 5 q52 ∷
   rw 6 q72 ∷
   rw 7 q52 ∷
   re 5 3 (ℓ "举") ∷
   rw 6 q73 ∷
   rw 7 q74 ∷
   rw 8 q75 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = sE 3099 lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q77 : Eqn
  q77 = wE 1358 W
  q78 : Eqn
  q78 = wE 227 W
  q79 : Eqn
  q79 = wE 1342 W

-- pass [X3 TOFF102 CS13 TOFF102 CSd13 X3] [CS03 TOFF012 CSd03 TOFF012]: 33 steps
lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丞习丽习举丞中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丞习丽习举丞") ⟫ʷ
lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丞习丽习举丞中九丮九") (ℓ "中九丮九丞习丽习举丞")
  (rw 0 q8 ∷
   rw 1 q26 ∷
   rw 2 q8 ∷
   re 0 3 (ℓ "中") ∷
   rw 3 q8 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q27 ∷
   rw 1 q39 ∷
   rw 2 q8 ∷
   rw 3 q40 ∷
   rw 4 q8 ∷
   re 2 3 (ℓ "丮") ∷
   rw 5 q8 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q27 ∷
   rw 3 q39 ∷
   rw⁻ 4 q76 ∷
   rw 15 q8 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q27 ∷
   re 13 1 (ℓ "乏丨乏") ∷
   rw 15 q27 ∷
   rw 14 q77 ∷
   rw 13 q27 ∷
   rw 12 q78 ∷
   rw 13 q8 ∷
   re 12 1 (ℓ "乏丨乏") ∷
   rw 14 q27 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q27 ∷
   rw 12 q79 ∷
   rw 11 q27 ∷
   rw 10 q78 ∷ []) Eq.refl

private
  q80 : Eqn
  q80 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q81 : Eqn
  q81 = wE 2561 W

-- merge-all Gad(t=0, W=(), d=SK, e=-1): 5 steps
lem-merge-all-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ : ⟪ (ℓ "丈上中九丮九下三丞丈上中九丮九下三丞丘丈上中九丮九下三丘丘丞丈上中九丮九下三丘丞") ⟫ʷ ≈ ⟪ (ℓ "丳丢") ⟫ʷ
lem-merge-all-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩ = derive (ℓ "丈上中九丮九下三丞丈上中九丮九下三丞丘丈上中九丮九下三丘丘丞丈上中九丮九下三丘丞") (ℓ "丳丢")
  (rw 0 q43 ∷
   rw 13 q35 ∷
   rw 22 q80 ∷
   rw 5 q43 ∷
   rw 0 q81 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q83 : Eqn
  q83 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q84 : Eqn
  q84 = wE 2549 W
  q85 : Eqn
  q85 = wE 1731 W
  q86 : Eqn
  q86 = wE 271 W
  q87 : Eqn
  q87 = wE 272 W
  q88 : Eqn
  q88 = wE 1207 W
  q89 : Eqn
  q89 = sE 3095 lem-merge-all-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩
  q90 : Eqn
  q90 = wE 320 W
  q91 : Eqn
  q91 = wE 326 W

-- merge-all Gad(t=0, W=(), d=SK, e=1) @1023: 157 steps
lem-merge-all-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩-at1023 : ⟪ (ℓ "与丐习丽习举丑丏丞与丐习丽习举丑丏丞丘与丐习丽习举丑丏丘丘丞与丐习丽习举丑丏丘丞") ⟫ʷ ≈ ⟪ (ℓ "丢丣") ⟫ʷ
lem-merge-all-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩-at1023 = derive (ℓ "与丐习丽习举丑丏丞与丐习丽习举丑丏丞丘与丐习丽习举丑丏丘丘丞与丐习丽习举丑丏丘丞") (ℓ "丢丣")
  (rw 40 q50 ∷
   rw⁻ 39 q82 ∷
   rw⁻ 38 q83 ∷
   rw 37 q84 ∷
   rw 36 q85 ∷
   re 35 1 (ℓ "乏丷乏") ∷
   rw⁻ 37 q52 ∷
   rw 36 q56 ∷
   rw⁻ 35 q52 ∷
   re 36 3 (ℓ "丮") ∷
   re 34 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 41 q59 ∷
   rw 40 q86 ∷
   rw 39 q54 ∷
   rw 38 q55 ∷
   rw 37 q56 ∷
   rw 36 q55 ∷
   rw 35 q57 ∷
   rw 34 q86 ∷
   rw 35 q87 ∷
   re 35 8 (ℓ "九") ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw⁻ 35 q52 ∷
   rw 34 q57 ∷
   rw⁻ 33 q52 ∷
   re 34 3 (ℓ "中") ∷
   re 32 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 39 q59 ∷
   rw 38 q86 ∷
   rw 37 q54 ∷
   rw 36 q55 ∷
   rw 35 q56 ∷
   rw 34 q55 ∷
   rw 33 q57 ∷
   rw 32 q86 ∷
   rw 33 q87 ∷
   re 33 8 (ℓ "九") ∷
   rw 31 q86 ∷
   rw 30 q88 ∷
   rw⁻ 29 q82 ∷
   rw⁻ 28 q83 ∷
   rw⁻ 27 q83 ∷
   rw 26 q84 ∷
   rw 25 q85 ∷
   re 24 1 (ℓ "乏丷乏") ∷
   rw⁻ 26 q52 ∷
   rw 25 q56 ∷
   rw⁻ 24 q52 ∷
   re 25 3 (ℓ "丮") ∷
   re 23 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 30 q59 ∷
   rw 29 q86 ∷
   rw 28 q54 ∷
   rw 27 q55 ∷
   rw 26 q56 ∷
   rw 25 q55 ∷
   rw 24 q57 ∷
   rw 23 q86 ∷
   rw 24 q87 ∷
   re 24 8 (ℓ "九") ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw⁻ 24 q52 ∷
   rw 23 q57 ∷
   rw⁻ 22 q52 ∷
   re 23 3 (ℓ "中") ∷
   re 21 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 28 q59 ∷
   rw 27 q86 ∷
   rw 26 q54 ∷
   rw 25 q55 ∷
   rw 24 q56 ∷
   rw 23 q55 ∷
   rw 22 q57 ∷
   rw 21 q86 ∷
   rw 22 q87 ∷
   re 22 8 (ℓ "九") ∷
   rw 20 q86 ∷
   rw 19 q88 ∷
   rw⁻ 18 q83 ∷
   rw⁻ 17 q82 ∷
   rw 16 q84 ∷
   rw 15 q85 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw⁻ 16 q52 ∷
   rw 15 q56 ∷
   rw⁻ 14 q52 ∷
   re 15 3 (ℓ "丮") ∷
   re 13 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 20 q59 ∷
   rw 19 q86 ∷
   rw 18 q54 ∷
   rw 17 q55 ∷
   rw 16 q56 ∷
   rw 15 q55 ∷
   rw 14 q57 ∷
   rw 13 q86 ∷
   rw 14 q87 ∷
   re 14 8 (ℓ "九") ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw⁻ 14 q52 ∷
   rw 13 q57 ∷
   rw⁻ 12 q52 ∷
   re 13 3 (ℓ "中") ∷
   re 11 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 18 q59 ∷
   rw 17 q86 ∷
   rw 16 q54 ∷
   rw 15 q55 ∷
   rw 14 q56 ∷
   rw 13 q55 ∷
   rw 12 q57 ∷
   rw 11 q86 ∷
   rw 12 q87 ∷
   re 12 8 (ℓ "九") ∷
   rw 10 q86 ∷
   rw 9 q88 ∷
   rw⁻ 8 q82 ∷
   rw 7 q84 ∷
   rw 6 q85 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw⁻ 7 q52 ∷
   rw 6 q56 ∷
   rw⁻ 5 q52 ∷
   re 6 3 (ℓ "丮") ∷
   re 4 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 11 q59 ∷
   rw 10 q86 ∷
   rw 9 q54 ∷
   rw 8 q55 ∷
   rw 7 q56 ∷
   rw 6 q55 ∷
   rw 5 q57 ∷
   rw 4 q86 ∷
   rw 5 q87 ∷
   re 5 8 (ℓ "九") ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw⁻ 5 q52 ∷
   rw 4 q57 ∷
   rw⁻ 3 q52 ∷
   re 4 3 (ℓ "中") ∷
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 9 q59 ∷
   rw 8 q86 ∷
   rw 7 q54 ∷
   rw 6 q55 ∷
   rw 5 q56 ∷
   rw 4 q55 ∷
   rw 3 q57 ∷
   rw 2 q86 ∷
   rw 3 q87 ∷
   re 3 8 (ℓ "九") ∷
   rw 1 q86 ∷
   rw 0 q88 ∷
   rw 1 q89 ∷
   rw 0 q90 ∷
   rw 1 q91 ∷
   rw 2 q75 ∷ []) Eq.refl

private
  q92 : Eqn
  q92 = wE 2562 W
  q93 : Eqn
  q93 = wE 2563 W
  q94 : Eqn
  q94 = wE 2564 W
  q95 : Eqn
  q95 = sE 3083 lem-CAw1-SS-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩
  q96 : Eqn
  q96 = sE 3100 lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SdK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡1⟩-at1023

-- conjF: 43 steps
lem-conjF : ⟪ (ℓ "丈上中九丮九下三丢並") ⟫ʷ ≈ ⟪ (ℓ "丢並与丐习丽习举丑丏") ⟫ʷ
lem-conjF = derive (ℓ "丈上中九丮九下三丢並") (ℓ "丢並与丐习丽习举丑丏")
  (rw 0 q92 ∷
   rw 1 q50 ∷
   rw 3 q93 ∷
   rw 13 q94 ∷
   rw 3 q95 ∷
   rw 2 q74 ∷
   rw 3 q66 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 4 q52 ∷
   rw 5 q70 ∷
   rw 6 q52 ∷
   re 4 3 (ℓ "丽") ∷
   re 6 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 5 q66 ∷
   rw 6 q67 ∷
   rw 7 q68 ∷
   rw 8 q69 ∷
   rw 9 q68 ∷
   rw 10 q70 ∷
   rw 11 q66 ∷
   rw 12 q71 ∷
   rw 5 q61 ∷
   re 5 8 (ℓ "习") ∷
   re 7 1 (ℓ "乏丨乏") ∷
   rw 6 q52 ∷
   rw 7 q72 ∷
   rw 8 q52 ∷
   re 6 3 (ℓ "举") ∷
   re 8 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 7 q66 ∷
   rw 8 q67 ∷
   rw 9 q68 ∷
   rw 10 q69 ∷
   rw 11 q68 ∷
   rw 12 q70 ∷
   rw 13 q66 ∷
   rw 14 q71 ∷
   rw 7 q61 ∷
   re 7 8 (ℓ "习") ∷
   rw 8 q73 ∷
   rw 9 q65 ∷
   rw 10 q75 ∷
   rw 2 q96 ∷ []) Eq.refl

private
  q97 : Eqn
  q97 = sE 2689 lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-3
  q98 : Eqn
  q98 = sE 3079 lem-pass-CSd31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3
  q99 : Eqn
  q99 = sE 3077 lem-pass-CKd31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3
  q100 : Eqn
  q100 = sE 3098 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3
  q101 : Eqn
  q101 = sE 3076 lem-pass-CK31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3
  q102 : Eqn
  q102 = sE 3078 lem-pass-CS31-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3
  q103 : Eqn
  q103 = sE 2689 lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SK-e≡1⟩-3

-- pass [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1] [X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X3]: 7 steps
lem-pass-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 : ⟪ (ℓ "与丐习丽习举丑丏丞丈上中九丮九下三丞") ⟫ʷ ≈ ⟪ (ℓ "丞丈上中九丮九下三丞与丐习丽习举丑丏") ⟫ʷ
lem-pass-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3 = derive (ℓ "与丐习丽习举丑丏丞丈上中九丮九下三丞") (ℓ "丞丈上中九丮九下三丞与丐习丽习举丑丏")
  (rw 0 q97 ∷
   rw 7 q98 ∷
   rw 6 q99 ∷
   rw 2 q100 ∷
   rw 1 q101 ∷
   rw 0 q102 ∷
   rw⁻ 10 q103 ∷ []) Eq.refl

private
  q104 : Eqn
  q104 = sE 2732 lem-ca-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3
  q105 : Eqn
  q105 = sE 3075 lem-pass-X3-CSd32-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q106 : Eqn
  q106 = sE 2136 lem-pass-X3-CKd32-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q107 : Eqn
  q107 = sE 3074 lem-pass-X3-CS32-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q108 : Eqn
  q108 = sE 3097 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3
  q109 : Eqn
  q109 = sE 2135 lem-pass-X3-CK32-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q110 : Eqn
  q110 = sE 2732 lem-ca-split-Gad⟨t≡2-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3

-- pass [TOFF012 CS03 TOFF012 CSd03] [X3 Sd2 Kd2 S2 S2 CS23 TOFF201 CSd23 TOFF201 Sd2 Sd2 K2 S2 X3]: 11 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 : ⟪ (ℓ "九中九丮丞丕丗且且义乣乊乣丕丕世且丞") ⟫ʷ ≈ ⟪ (ℓ "丞丕丗且且义乣乊乣丕丕世且丞九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-Sd2-Kd2-S2-S2-CS23-TOFF201-CSd23-TOFF201-Sd2-Sd2-K2-S2-X3 = derive (ℓ "九中九丮丞丕丗且且义乣乊乣丕丕世且丞") (ℓ "丞丕丗且且义乣乊乣丕丕世且丞九中九丮")
  (rw 4 q104 ∷
   rw⁻ 0 q105 ∷
   rw⁻ 3 q106 ∷
   rw⁻ 6 q107 ∷
   rw⁻ 9 q107 ∷
   rw 12 q108 ∷
   rw⁻ 18 q105 ∷
   rw⁻ 21 q105 ∷
   rw⁻ 24 q109 ∷
   rw⁻ 27 q107 ∷
   rw⁻ 0 q110 ∷ []) Eq.refl

private
  q111 : Eqn
  q111 = sE 2971 lem-ca-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩-3
  q112 : Eqn
  q112 = sE 3072 lem-pass-X3-CS31-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q113 : Eqn
  q113 = sE 3070 lem-pass-X3-CK31-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q114 : Eqn
  q114 = sE 3096 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3
  q115 : Eqn
  q115 = sE 3071 lem-pass-X3-CKd31-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q116 : Eqn
  q116 = sE 3073 lem-pass-X3-CSd31-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q117 : Eqn
  q117 = sE 2971 lem-ca-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SK-e≡-1⟩-3

-- pass [TOFF012 CS03 TOFF012 CSd03] [X0 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X0 X3]: 7 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 : ⟪ (ℓ "九中九丮丌丞与丐丽习举习丑丏丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞与丐丽习举习丑丏丌丞九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X0-X3 = derive (ℓ "九中九丮丌丞与丐丽习举习丑丏丌丞") (ℓ "丌丞与丐丽习举习丑丏丌丞九中九丮")
  (rw 4 q111 ∷
   rw⁻ 0 q112 ∷
   rw⁻ 3 q113 ∷
   rw 6 q114 ∷
   rw⁻ 14 q115 ∷
   rw⁻ 17 q116 ∷
   rw⁻ 0 q117 ∷ []) Eq.refl
