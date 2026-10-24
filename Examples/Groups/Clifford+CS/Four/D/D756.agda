{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD756 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D756 (W : Ws) (Sᴰ : SD756) where

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
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK30-X3 : St 1216
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK30-X3 = pickᴰ 0 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CKd30-X3 : St 1217
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CKd30-X3 = pickᴰ 1 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK20-X2 : St 1278
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK20-X2 = pickᴰ 2 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CKd20-X2 : St 1279
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CKd20-X2 = pickᴰ 3 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS03-X3 : St 2723
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS03-X3 = pickᴰ 4 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd03-X3 : St 2724
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd03-X3 = pickᴰ 5 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd02-X2 : St 2813
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd02-X2 = pickᴰ 6 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS02-X2 : St 2814
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS02-X2 = pickᴰ 7 Sᴰ
  lem-CA-CS10-Gad⟨t≡0-W≡⟨2⟩-d≡Sd-e≡-1⟩ : St 2815
  lem-CA-CS10-Gad⟨t≡0-W≡⟨2⟩-d≡Sd-e≡-1⟩ = pickᴰ 8 Sᴰ
  lem-CA-CSd10-Gad⟨t≡0-W≡⟨2⟩-d≡1-e≡-1⟩ : St 2816
  lem-CA-CSd10-Gad⟨t≡0-W≡⟨2⟩-d≡1-e≡-1⟩ = pickᴰ 9 Sᴰ
  lem-pass-CKd31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : St 2817
  lem-pass-CKd31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = pickᴰ 10 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ : St 2818
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 11 Sᴰ
  lem-pass-CK20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 2233
  lem-pass-CK20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 12 Sᴰ
  lem-CCZ⟨213⟩-passes-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩ : St 2819
  lem-CCZ⟨213⟩-passes-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 13 Sᴰ
  lem-pass-CK20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 2487
  lem-pass-CK20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 14 Sᴰ
  lem-pass-CS30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 2622
  lem-pass-CS30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 15 Sᴰ
  lem-pass-CSd30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 2623
  lem-pass-CSd30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 16 Sᴰ
  lem-CA-CS30-Gad⟨t≡0-W≡⟨2⟩-d≡Sd-e≡-1⟩ : St 2820
  lem-CA-CS30-Gad⟨t≡0-W≡⟨2⟩-d≡Sd-e≡-1⟩ = pickᴰ 17 Sᴰ
  lem-CA-CSd30-Gad⟨t≡0-W≡⟨2⟩-d≡1-e≡-1⟩ : St 2821
  lem-CA-CSd30-Gad⟨t≡0-W≡⟨2⟩-d≡1-e≡-1⟩ = pickᴰ 18 Sᴰ
  lem-pass-CKd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 2714
  lem-pass-CKd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 19 Sᴰ
  lem-pass-CS31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : St 2734
  lem-pass-CS31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = pickᴰ 20 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩-2 : St 2822
  lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩-2 = pickᴰ 21 Sᴰ
  lem-pass-CKd20-vs-X2-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2 : St 2823
  lem-pass-CKd20-vs-X2-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2 = pickᴰ 22 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-3 : St 2824
  lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-3 = pickᴰ 23 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 2825
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 24 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 2826
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 25 Sᴰ
  lem-pass-CSd31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : St 2827
  lem-pass-CSd31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = pickᴰ 26 Sᴰ
  lem-pass-X2-CKd21-X2-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 : St 2828
  lem-pass-X2-CKd21-X2-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 = pickᴰ 27 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = wE 140 W
  q4 : Eqn
  q4 = wE 7 W
  q5 : Eqn
  q5 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q6 : Eqn
  q6 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q7 : Eqn
  q7 = wE 2432 W
  q8 : Eqn
  q8 = wE 142 W
  q9 : Eqn
  q9 = wE 27 W
  q10 : Eqn
  q10 = wE 139 W
  q11 : Eqn
  q11 = wE 29 W
  q12 : Eqn
  q12 = wE 31 W
  q13 : Eqn
  q13 = sE 2821 lem-CA-CSd30-Gad⟨t≡0-W≡⟨2⟩-d≡1-e≡-1⟩
  q14 : Eqn
  q14 = sE 2823 lem-pass-CKd20-vs-X2-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2
  q15 : Eqn
  q15 = sE 2820 lem-CA-CS30-Gad⟨t≡0-W≡⟨2⟩-d≡Sd-e≡-1⟩
  q16 : Eqn
  q16 = sE 2233 lem-pass-CK20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q17 : Eqn
  q17 = wE 76 W
  q18 : Eqn
  q18 = wE 137 W
  q19 : Eqn
  q19 = wE 2433 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 236 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘中九丮九丘") ⟫ʷ ≈ ⟪ (ℓ "丘中九丮九丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘中九丮九丘") (ℓ "丘中九丮九丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 29 q1 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw⁻ 30 q2 ∷
   rw 29 q3 ∷
   rw⁻ 28 q2 ∷
   re 29 3 (ℓ "乔") ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw⁻ 29 q2 ∷
   rw 28 q3 ∷
   rw⁻ 27 q2 ∷
   re 28 3 (ℓ "乔") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q2 ∷
   rw 27 q4 ∷
   rw⁻ 26 q2 ∷
   re 27 3 (ℓ "丽") ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw⁻ 27 q2 ∷
   rw 26 q3 ∷
   rw⁻ 25 q2 ∷
   re 26 3 (ℓ "乔") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw⁻ 26 q2 ∷
   rw 25 q4 ∷
   rw⁻ 24 q2 ∷
   re 25 3 (ℓ "丽") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q2 ∷
   rw 24 q4 ∷
   rw⁻ 23 q2 ∷
   re 24 3 (ℓ "丽") ∷
   rw⁻ 22 q5 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q2 ∷
   rw 22 q4 ∷
   rw⁻ 21 q2 ∷
   re 22 3 (ℓ "丽") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q2 ∷
   rw 21 q4 ∷
   rw⁻ 20 q2 ∷
   re 21 3 (ℓ "丽") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q2 ∷
   rw 20 q4 ∷
   rw⁻ 19 q2 ∷
   re 20 3 (ℓ "丽") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q2 ∷
   rw 19 q4 ∷
   rw⁻ 18 q2 ∷
   re 19 3 (ℓ "丽") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q2 ∷
   rw 18 q4 ∷
   rw⁻ 17 q2 ∷
   re 18 3 (ℓ "丽") ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q2 ∷
   rw 17 q4 ∷
   rw⁻ 16 q2 ∷
   re 17 3 (ℓ "丽") ∷
   rw⁻ 15 q6 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw⁻ 16 q2 ∷
   rw 15 q3 ∷
   rw⁻ 14 q2 ∷
   re 15 3 (ℓ "乔") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q2 ∷
   rw 14 q4 ∷
   rw⁻ 13 q2 ∷
   re 14 3 (ℓ "丽") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q2 ∷
   rw 13 q4 ∷
   rw⁻ 12 q2 ∷
   re 13 3 (ℓ "丽") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q2 ∷
   rw 12 q4 ∷
   rw⁻ 11 q2 ∷
   re 12 3 (ℓ "丽") ∷
   rw⁻ 10 q6 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw⁻ 11 q2 ∷
   rw 10 q3 ∷
   rw⁻ 9 q2 ∷
   re 10 3 (ℓ "乔") ∷
   rw⁻ 8 q6 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw⁻ 9 q2 ∷
   rw 8 q3 ∷
   rw⁻ 7 q2 ∷
   re 8 3 (ℓ "乔") ∷
   rw⁻ 6 q5 ∷
   rw 5 q3 ∷
   rw 4 q3 ∷
   rw 3 q4 ∷
   rw 2 q3 ∷
   rw 1 q4 ∷
   rw 0 q4 ∷
   rw 1 q7 ∷
   rw 0 q8 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q2 ∷
   rw 2 q9 ∷
   rw 3 q2 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q10 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 3 q2 ∷
   rw 4 q11 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "丮") ∷
   rw 4 q12 ∷
   rw 3 q13 ∷
   rw 2 q14 ∷
   rw 1 q15 ∷
   rw 0 q16 ∷
   rw 10 q1 ∷
   re 9 1 (ℓ "乏丨乏") ∷
   rw⁻ 11 q2 ∷
   rw 10 q17 ∷
   rw⁻ 9 q2 ∷
   re 10 3 (ℓ "举") ∷
   rw 8 q18 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw⁻ 9 q2 ∷
   rw 8 q4 ∷
   rw⁻ 7 q2 ∷
   re 8 3 (ℓ "丽") ∷
   rw 6 q3 ∷
   rw 7 q19 ∷
   rw 6 q9 ∷
   rw 7 q9 ∷
   rw 8 q8 ∷
   rw 9 q9 ∷
   rw 10 q8 ∷
   rw 11 q8 ∷
   rw 12 q5 ∷
   re 14 1 (ℓ "乏乇乏") ∷
   rw 13 q2 ∷
   rw 14 q8 ∷
   rw 15 q2 ∷
   re 13 3 (ℓ "乑") ∷
   rw 14 q6 ∷
   re 16 1 (ℓ "乏乇乏") ∷
   rw 15 q2 ∷
   rw 16 q8 ∷
   rw 17 q2 ∷
   re 15 3 (ℓ "乑") ∷
   rw 16 q6 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q2 ∷
   rw 18 q9 ∷
   rw 19 q2 ∷
   re 17 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q2 ∷
   rw 19 q9 ∷
   rw 20 q2 ∷
   re 18 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q2 ∷
   rw 20 q9 ∷
   rw 21 q2 ∷
   re 19 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏乇乏") ∷
   rw 20 q2 ∷
   rw 21 q8 ∷
   rw 22 q2 ∷
   re 20 3 (ℓ "乑") ∷
   rw 21 q6 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q2 ∷
   rw 23 q9 ∷
   rw 24 q2 ∷
   re 22 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q2 ∷
   rw 24 q9 ∷
   rw 25 q2 ∷
   re 23 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q2 ∷
   rw 25 q9 ∷
   rw 26 q2 ∷
   re 24 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q2 ∷
   rw 26 q9 ∷
   rw 27 q2 ∷
   re 25 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q2 ∷
   rw 27 q9 ∷
   rw 28 q2 ∷
   re 26 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q2 ∷
   rw 28 q9 ∷
   rw 29 q2 ∷
   re 27 3 (ℓ "中") ∷
   rw 28 q5 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q2 ∷
   rw 30 q9 ∷
   rw 31 q2 ∷
   re 29 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q2 ∷
   rw 31 q9 ∷
   rw 32 q2 ∷
   re 30 3 (ℓ "中") ∷
   re 32 1 (ℓ "乏乇乏") ∷
   rw 31 q2 ∷
   rw 32 q8 ∷
   rw 33 q2 ∷
   re 31 3 (ℓ "乑") ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q2 ∷
   rw 33 q9 ∷
   rw 34 q2 ∷
   re 32 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏乇乏") ∷
   rw 33 q2 ∷
   rw 34 q8 ∷
   rw 35 q2 ∷
   re 33 3 (ℓ "乑") ∷
   re 35 1 (ℓ "乏乇乏") ∷
   rw 34 q2 ∷
   rw 35 q8 ∷
   rw 36 q2 ∷
   re 34 3 (ℓ "乑") ∷
   rw 35 q12 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = sE 2822 lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩-2
  q21 : Eqn
  q21 = sE 2819 lem-CCZ⟨213⟩-passes-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩
  q22 : Eqn
  q22 = sE 2822 lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩-2

-- pass [CCZ123] [X2 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2]: 3 steps
lem-pass-CCZ123-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 : ⟪ (ℓ "乜丘三下丈丈中九丮九三三上丈丘") ⟫ʷ ≈ ⟪ (ℓ "丘三下丈丈中九丮九三三上丈丘乜") ⟫ʷ
lem-pass-CCZ123-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 = derive (ℓ "乜丘三下丈丈中九丮九三三上丈丘") (ℓ "丘三下丈丈中九丮九三三上丈丘乜")
  (rw 1 q20 ∷
   rw 0 q21 ∷
   rw⁻ 0 q22 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = sE 2813 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CSd02-X2
  q24 : Eqn
  q24 = sE 1279 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CKd20-X2
  q25 : Eqn
  q25 = sE 2814 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS02-X2
  q26 : Eqn
  q26 = sE 2825 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q27 : Eqn
  q27 = sE 1278 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CK20-X2

-- Bar(SSSKSS;2,3->0) passes split Gad(t=0, W=(2,), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘丨丘丘久丘丘丧丘丘丧丘丘中九丮九丘丘丨丘丘丨丘丘乄丘丘丧丘") ⟫ʷ ≈ ⟪ (ℓ "丘丨丘丘久丘丘丧丘丘丧丘丘中九丮九丘丘丨丘丘丨丘丘乄丘丘丧丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘丨丘丘久丘丘丧丘丘丧丘丘中九丮九丘丘丨丘丘丨丘丘乄丘丘丧丘") (ℓ "丘丨丘丘久丘丘丧丘丘丧丘丘中九丮九丘丘丨丘丘丨丘丘乄丘丘丧丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 0 q23 ∷
   rw 3 q24 ∷
   rw 6 q25 ∷
   rw 9 q25 ∷
   rw 12 q26 ∷
   rw 18 q23 ∷
   rw 21 q23 ∷
   rw 24 q27 ∷
   rw 27 q25 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = wE 2299 W
  q29 : Eqn
  q29 = sE 2816 lem-CA-CSd10-Gad⟨t≡0-W≡⟨2⟩-d≡1-e≡-1⟩
  q30 : Eqn
  q30 = sE 2815 lem-CA-CS10-Gad⟨t≡0-W≡⟨2⟩-d≡Sd-e≡-1⟩
  q31 : Eqn
  q31 = wE 2300 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 6 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘中九丮九丘") ⟫ʷ ≈ ⟪ (ℓ "丘中九丮九丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = derive (ℓ "丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘中九丮九丘") (ℓ "丘中九丮九丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临")
  (rw 0 q28 ∷
   rw 3 q29 ∷
   rw 2 q14 ∷
   rw 1 q30 ∷
   rw 0 q16 ∷
   rw 6 q31 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = sE 2824 lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-3
  q33 : Eqn
  q33 = sE 2818 lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩
  q34 : Eqn
  q34 = sE 2824 lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-3

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2 X3]: 3 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丘丞三下丈丈中九丮九三三上丈丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞三下丈丈中九丮九三三上丈丘丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丘丞三下丈丈中九丮九三三上丈丘丞") (ℓ "丘丞三下丈丈中九丮九三三上丈丘丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 29 q32 ∷
   rw 0 q33 ∷
   rw⁻ 0 q34 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q36 : Eqn
  q36 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q37 : Eqn
  q37 = wE 2423 W
  q38 : Eqn
  q38 = sE 2714 lem-pass-CKd20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q39 : Eqn
  q39 = sE 2623 lem-pass-CSd30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q40 : Eqn
  q40 = sE 2487 lem-pass-CK20-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q41 : Eqn
  q41 = sE 2622 lem-pass-CS30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q42 : Eqn
  q42 = wE 2424 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 144 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丘丞中九丮九丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞中九丮九丘丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丘丞中九丮九丘丞") (ℓ "丘丞中九丮九丘丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 31 q1 ∷
   rw 30 q4 ∷
   rw 29 q4 ∷
   rw 28 q3 ∷
   rw 27 q4 ∷
   rw 26 q4 ∷
   rw 25 q4 ∷
   rw⁻ 24 q35 ∷
   rw 23 q4 ∷
   rw 22 q4 ∷
   rw 21 q4 ∷
   rw 20 q4 ∷
   rw 19 q4 ∷
   rw 18 q4 ∷
   rw 17 q4 ∷
   rw 16 q4 ∷
   rw 15 q4 ∷
   rw⁻ 14 q36 ∷
   rw 13 q3 ∷
   rw 12 q4 ∷
   rw 11 q4 ∷
   rw 10 q4 ∷
   rw 9 q4 ∷
   rw 8 q4 ∷
   rw 7 q4 ∷
   rw⁻ 6 q35 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q2 ∷
   rw 6 q4 ∷
   rw⁻ 5 q2 ∷
   re 6 3 (ℓ "丽") ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q2 ∷
   rw 5 q4 ∷
   rw⁻ 4 q2 ∷
   re 5 3 (ℓ "丽") ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw⁻ 5 q2 ∷
   rw 4 q3 ∷
   rw⁻ 3 q2 ∷
   re 4 3 (ℓ "乔") ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw⁻ 4 q2 ∷
   rw 3 q4 ∷
   rw⁻ 2 q2 ∷
   re 3 3 (ℓ "丽") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q2 ∷
   rw 2 q4 ∷
   rw⁻ 1 q2 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q2 ∷
   rw 1 q4 ∷
   rw⁻ 0 q2 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q37 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 0 q2 ∷
   rw 1 q9 ∷
   rw 2 q2 ∷
   re 0 3 (ℓ "中") ∷
   rw 1 q8 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 2 q2 ∷
   rw 3 q11 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "丮") ∷
   rw 3 q10 ∷
   rw 4 q12 ∷
   rw 3 q38 ∷
   rw 2 q39 ∷
   rw 1 q40 ∷
   rw 0 q41 ∷
   rw 12 q1 ∷
   rw 11 q18 ∷
   re 10 1 (ℓ "乏丨乏") ∷
   rw⁻ 12 q2 ∷
   rw 11 q17 ∷
   rw⁻ 10 q2 ∷
   re 11 3 (ℓ "举") ∷
   rw 9 q3 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q2 ∷
   rw 9 q4 ∷
   rw⁻ 8 q2 ∷
   re 9 3 (ℓ "丽") ∷
   rw 9 q42 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q2 ∷
   rw 9 q9 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "中") ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q2 ∷
   rw 10 q9 ∷
   rw 11 q2 ∷
   re 9 3 (ℓ "中") ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q2 ∷
   rw 11 q9 ∷
   rw 12 q2 ∷
   re 10 3 (ℓ "中") ∷
   re 12 1 (ℓ "乏乇乏") ∷
   rw 11 q2 ∷
   rw 12 q8 ∷
   rw 13 q2 ∷
   re 11 3 (ℓ "乑") ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q2 ∷
   rw 13 q9 ∷
   rw 14 q2 ∷
   re 12 3 (ℓ "中") ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q2 ∷
   rw 14 q9 ∷
   rw 15 q2 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q35 ∷
   rw 15 q9 ∷
   rw 16 q9 ∷
   rw 17 q9 ∷
   rw 18 q9 ∷
   rw 19 q9 ∷
   rw 20 q9 ∷
   rw 21 q8 ∷
   rw 22 q36 ∷
   rw 23 q9 ∷
   rw 24 q9 ∷
   rw 25 q9 ∷
   rw 26 q9 ∷
   rw 27 q9 ∷
   rw 28 q9 ∷
   rw 29 q9 ∷
   rw 30 q9 ∷
   rw 31 q9 ∷
   rw 32 q35 ∷
   rw 33 q9 ∷
   rw 34 q9 ∷
   rw 35 q9 ∷
   rw 36 q8 ∷
   rw 37 q9 ∷
   rw 38 q9 ∷
   rw 39 q12 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = sE 2724 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd03-X3
  q44 : Eqn
  q44 = sE 1217 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CKd30-X3
  q45 : Eqn
  q45 = sE 2723 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS03-X3
  q46 : Eqn
  q46 = sE 2826 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q47 : Eqn
  q47 = sE 1216 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK30-X3

-- Bar(SSKSKK;3,1->0) passes split Gad(t=0, W=(2, 3), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞丮丞丞乒丞丞中丞丞中丞丘丞中九丮九丘丞丞丮丞丞丮丞丞乑丞丞中丞") ⟫ʷ ≈ ⟪ (ℓ "丞丮丞丞乒丞丞中丞丞中丞丘丞中九丮九丘丞丞丮丞丞丮丞丞乑丞丞中丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSKSKK31-⟶0⟩-passes-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞丮丞丞乒丞丞中丞丞中丞丘丞中九丮九丘丞丞丮丞丞丮丞丞乑丞丞中丞") (ℓ "丞丮丞丞乒丞丞中丞丞中丞丘丞中九丮九丘丞丞丮丞丞丮丞丞乑丞丞中丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 0 q43 ∷
   rw 3 q44 ∷
   rw 6 q45 ∷
   rw 9 q45 ∷
   rw 12 q46 ∷
   rw 20 q43 ∷
   rw 23 q43 ∷
   rw 26 q47 ∷
   rw 29 q45 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = eqn (ℓ "丏丞") (ℓ "丞丏") (low-comm (((S • S • S) ↑)) ((X ↑)))
  q49 : Eqn
  q49 = eqn (ℓ "丌丏") (ℓ "丏丌") (low₁-comm (X) ((S • S • S)))
  q50 : Eqn
  q50 = eqn (ℓ "丑丞") (ℓ "丞丑") (low-comm (((K • iI) ↑)) ((X ↑)))
  q51 : Eqn
  q51 = eqn (ℓ "丌丑") (ℓ "丑丌") (low₁-comm (X) ((K • iI)))
  q52 : Eqn
  q52 = eqn (ℓ "与丞") (ℓ "丞与") (low-comm ((S ↑)) ((X ↑)))
  q53 : Eqn
  q53 = eqn (ℓ "丌与") (ℓ "与丌") (low₁-comm (X) (S))
  q54 : Eqn
  q54 = eqn (ℓ "丌丐") (ℓ "丐丌") (low₁-comm (X) (K))
  q55 : Eqn
  q55 = eqn (ℓ "丐丞") (ℓ "丞丐") (low-comm ((K ↑)) ((X ↑)))
  q56 : Eqn
  q56 = wE 2509 W
  q57 : Eqn
  q57 = wE 2510 W
  q58 : Eqn
  q58 = sE 2734 lem-pass-CS31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3
  q59 : Eqn
  q59 = sE 2817 lem-pass-CKd31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3
  q60 : Eqn
  q60 = sE 2827 lem-pass-CSd31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3
  q61 : Eqn
  q61 = wE 2511 W

-- ca-split Gad(t=1, W=(0, 3), d=SdKdSS, e=-1) 3: 23 steps
lem-ca-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩-3 : ⟪ (ℓ "丌丞丏丑与与丽习举习丏丏丐与丌丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞丞乕丞丞丽丞丞丽丞丌丞丽习举习丌丞丞举丞丞举丞丞乔丞丞丽丞") ⟫ʷ
lem-ca-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩-3 = derive (ℓ "丌丞丏丑与与丽习举习丏丏丐与丌丞") (ℓ "丞举丞丞乕丞丞丽丞丞丽丞丌丞丽习举习丌丞丞举丞丞举丞丞乔丞丞丽丞")
  (rw⁻ 1 q48 ∷
   rw 0 q49 ∷
   rw⁻ 2 q50 ∷
   rw 1 q51 ∷
   rw⁻ 3 q52 ∷
   rw 2 q53 ∷
   rw⁻ 4 q52 ∷
   rw 3 q53 ∷
   rw⁻ 13 q53 ∷
   rw⁻ 12 q54 ∷
   rw⁻ 11 q49 ∷
   rw⁻ 10 q49 ∷
   rw 14 q52 ∷
   rw 13 q55 ∷
   rw 12 q48 ∷
   rw 11 q48 ∷
   rw 0 q56 ∷
   rw 24 q57 ∷
   rw 15 q58 ∷
   rw 14 q58 ∷
   rw 13 q59 ∷
   rw 12 q60 ∷
   rw 20 q61 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = eqn (ℓ "丌丘") (ℓ "丘丌") (low₁-comm (X) ((X ↑)))
  q63 : Eqn
  q63 = wE 1478 W
  q64 : Eqn
  q64 = sE 2828 lem-pass-X2-CKd21-X2-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0
  q65 : Eqn
  q65 = wE 1479 W

-- pass [CKd21] [X0 X2 CS13 TOFF102 CSd13 TOFF102 X0 X2]: 5 steps
lem-pass-CKd21-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 : ⟪ (ℓ "么丌丘丽习举习丌丘") ⟫ʷ ≈ ⟪ (ℓ "丌丘丽习举习丌丘么") ⟫ʷ
lem-pass-CKd21-vs-X0-X2-CS13-TOFF102-CSd13-TOFF102-X0-X2 = derive (ℓ "么丌丘丽习举习丌丘") (ℓ "丌丘丽习举习丌丘么")
  (rw 1 q62 ∷
   rw 0 q63 ∷
   rw 1 q64 ∷
   rw 7 q65 ∷
   rw⁻ 0 q62 ∷ []) Eq.refl
