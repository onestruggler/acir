{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD748 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D748 (W : Ws) (Sᴰ : SD748) where

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
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK31-X3 : St 190
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK31-X3 = pickᴰ 0 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd31-X3 : St 191
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd31-X3 = pickᴰ 1 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-X3 : St 196
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-X3 = pickᴰ 2 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd13-X3 : St 198
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd13-X3 = pickᴰ 3 Sᴰ
  lem-pass-CS20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 2219
  lem-pass-CS20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 4 Sᴰ
  lem-CA-CKd30-Gad⟨t≡0-W≡⟨2⟩-d≡1-e≡-1⟩ : St 2618
  lem-CA-CKd30-Gad⟨t≡0-W≡⟨2⟩-d≡1-e≡-1⟩ = pickᴰ 5 Sᴰ
  lem-pass-CK30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 1764
  lem-pass-CK30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 6 Sᴰ
  lem-CA-CS10-Gad⟨t≡0-W≡⟨2-3⟩-d≡Sd-e≡-1⟩ : St 2619
  lem-CA-CS10-Gad⟨t≡0-W≡⟨2-3⟩-d≡Sd-e≡-1⟩ = pickᴰ 7 Sᴰ
  lem-CA-CSd10-Gad⟨t≡0-W≡⟨2-3⟩-d≡1-e≡-1⟩ : St 2620
  lem-CA-CSd10-Gad⟨t≡0-W≡⟨2-3⟩-d≡1-e≡-1⟩ = pickᴰ 8 Sᴰ
  lem-CA-CK30-Gad⟨t≡0-W≡⟨2⟩-d≡Kd-e≡-1⟩ : St 2621
  lem-CA-CK30-Gad⟨t≡0-W≡⟨2⟩-d≡Kd-e≡-1⟩ = pickᴰ 9 Sᴰ
  lem-pass-CKd30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 1767
  lem-pass-CKd30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 10 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : St 2548
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = pickᴰ 11 Sᴰ
  lem-pass-CS30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 2622
  lem-pass-CS30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 12 Sᴰ
  lem-pass-CSd30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : St 2623
  lem-pass-CSd30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = pickᴰ 13 Sᴰ
  lem-pass-CKd30-vs-X2-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2-X3 : St 2624
  lem-pass-CKd30-vs-X2-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2-X3 = pickᴰ 14 Sᴰ
  lem-pass-CSd20-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2 : St 2625
  lem-pass-CSd20-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2 = pickᴰ 15 Sᴰ
  lem-pass-X3-CK32-X3-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 : St 2626
  lem-pass-X3-CK32-X3-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 = pickᴰ 16 Sᴰ
  lem-pass-X3-CK32-X3-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 : St 2627
  lem-pass-X3-CK32-X3-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 = pickᴰ 17 Sᴰ
  lem-pass-X3-CKd32-X3-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 : St 2628
  lem-pass-X3-CKd32-X3-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0 = pickᴰ 18 Sᴰ
  lem-pass-X3-CKd32-X3-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 : St 2629
  lem-pass-X3-CKd32-X3-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 = pickᴰ 19 Sᴰ
  lem-pass-X3-CSd31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 : St 2630
  lem-pass-X3-CSd31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 = pickᴰ 20 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = wE 7 W
  q4 : Eqn
  q4 = wE 140 W
  q5 : Eqn
  q5 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q6 : Eqn
  q6 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q7 : Eqn
  q7 = wE 2437 W
  q8 : Eqn
  q8 = wE 27 W
  q9 : Eqn
  q9 = wE 142 W
  q10 : Eqn
  q10 = wE 29 W
  q11 : Eqn
  q11 = wE 139 W
  q12 : Eqn
  q12 = wE 31 W
  q13 : Eqn
  q13 = sE 2618 lem-CA-CKd30-Gad⟨t≡0-W≡⟨2⟩-d≡1-e≡-1⟩
  q14 : Eqn
  q14 = sE 2625 lem-pass-CSd20-vs-X2-Kd0-CS03-TOFF012-CSd03-TOFF012-K0-X2
  q15 : Eqn
  q15 = sE 2621 lem-CA-CK30-Gad⟨t≡0-W≡⟨2⟩-d≡Kd-e≡-1⟩
  q16 : Eqn
  q16 = sE 2219 lem-pass-CS20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q17 : Eqn
  q17 = wE 137 W
  q18 : Eqn
  q18 = wE 76 W
  q19 : Eqn
  q19 = wE 2438 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 272 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘中九丮九丘") ⟫ʷ ≈ ⟪ (ℓ "丘中九丮九丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘中九丮九丘") (ℓ "丘中九丮九丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 31 q1 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q2 ∷
   rw 31 q3 ∷
   rw⁻ 30 q2 ∷
   re 31 3 (ℓ "丽") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q2 ∷
   rw 30 q3 ∷
   rw⁻ 29 q2 ∷
   re 30 3 (ℓ "丽") ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw⁻ 30 q2 ∷
   rw 29 q4 ∷
   rw⁻ 28 q2 ∷
   re 29 3 (ℓ "乔") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q2 ∷
   rw 28 q3 ∷
   rw⁻ 27 q2 ∷
   re 28 3 (ℓ "丽") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q2 ∷
   rw 27 q3 ∷
   rw⁻ 26 q2 ∷
   re 27 3 (ℓ "丽") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw⁻ 27 q2 ∷
   rw 26 q3 ∷
   rw⁻ 25 q2 ∷
   re 26 3 (ℓ "丽") ∷
   rw⁻ 24 q5 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q2 ∷
   rw 24 q3 ∷
   rw⁻ 23 q2 ∷
   re 24 3 (ℓ "丽") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw⁻ 24 q2 ∷
   rw 23 q3 ∷
   rw⁻ 22 q2 ∷
   re 23 3 (ℓ "丽") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q2 ∷
   rw 22 q3 ∷
   rw⁻ 21 q2 ∷
   re 22 3 (ℓ "丽") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q2 ∷
   rw 21 q3 ∷
   rw⁻ 20 q2 ∷
   re 21 3 (ℓ "丽") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw⁻ 21 q2 ∷
   rw 20 q3 ∷
   rw⁻ 19 q2 ∷
   re 20 3 (ℓ "丽") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q2 ∷
   rw 19 q3 ∷
   rw⁻ 18 q2 ∷
   re 19 3 (ℓ "丽") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q2 ∷
   rw 18 q3 ∷
   rw⁻ 17 q2 ∷
   re 18 3 (ℓ "丽") ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw⁻ 18 q2 ∷
   rw 17 q3 ∷
   rw⁻ 16 q2 ∷
   re 17 3 (ℓ "丽") ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw⁻ 17 q2 ∷
   rw 16 q3 ∷
   rw⁻ 15 q2 ∷
   re 16 3 (ℓ "丽") ∷
   rw⁻ 14 q6 ∷
   re 13 1 (ℓ "乏乄乏") ∷
   rw⁻ 15 q2 ∷
   rw 14 q4 ∷
   rw⁻ 13 q2 ∷
   re 14 3 (ℓ "乔") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q2 ∷
   rw 13 q3 ∷
   rw⁻ 12 q2 ∷
   re 13 3 (ℓ "丽") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q2 ∷
   rw 12 q3 ∷
   rw⁻ 11 q2 ∷
   re 12 3 (ℓ "丽") ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q2 ∷
   rw 11 q3 ∷
   rw⁻ 10 q2 ∷
   re 11 3 (ℓ "丽") ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q2 ∷
   rw 10 q3 ∷
   rw⁻ 9 q2 ∷
   re 10 3 (ℓ "丽") ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q2 ∷
   rw 9 q3 ∷
   rw⁻ 8 q2 ∷
   re 9 3 (ℓ "丽") ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw⁻ 9 q2 ∷
   rw 8 q3 ∷
   rw⁻ 7 q2 ∷
   re 8 3 (ℓ "丽") ∷
   rw⁻ 6 q5 ∷
   rw 5 q3 ∷
   rw 4 q3 ∷
   rw 3 q4 ∷
   rw 2 q3 ∷
   rw 1 q3 ∷
   rw 0 q3 ∷
   rw 1 q7 ∷
   rw 0 q8 ∷
   re 2 1 (ℓ "乏乇乏") ∷
   rw 1 q2 ∷
   rw 2 q9 ∷
   rw 3 q2 ∷
   re 1 3 (ℓ "乑") ∷
   rw 2 q10 ∷
   re 4 1 (ℓ "乏么乏") ∷
   rw 3 q2 ∷
   rw 4 q11 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "乒") ∷
   rw 4 q12 ∷
   rw 3 q13 ∷
   rw 2 q14 ∷
   rw 1 q15 ∷
   rw 0 q16 ∷
   rw 10 q1 ∷
   re 9 1 (ℓ "乏久乏") ∷
   rw⁻ 11 q2 ∷
   rw 10 q17 ∷
   rw⁻ 9 q2 ∷
   re 10 3 (ℓ "乕") ∷
   rw 8 q18 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw⁻ 9 q2 ∷
   rw 8 q4 ∷
   rw⁻ 7 q2 ∷
   re 8 3 (ℓ "乔") ∷
   rw 6 q3 ∷
   rw 7 q19 ∷
   rw 6 q8 ∷
   rw 7 q8 ∷
   rw 8 q8 ∷
   rw 9 q9 ∷
   rw 10 q8 ∷
   rw 11 q8 ∷
   rw 12 q5 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q2 ∷
   rw 14 q8 ∷
   rw 15 q2 ∷
   re 13 3 (ℓ "中") ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q2 ∷
   rw 15 q8 ∷
   rw 16 q2 ∷
   re 14 3 (ℓ "中") ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q2 ∷
   rw 16 q8 ∷
   rw 17 q2 ∷
   re 15 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q2 ∷
   rw 17 q8 ∷
   rw 18 q2 ∷
   re 16 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q2 ∷
   rw 18 q8 ∷
   rw 19 q2 ∷
   re 17 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q2 ∷
   rw 19 q8 ∷
   rw 20 q2 ∷
   re 18 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏乇乏") ∷
   rw 19 q2 ∷
   rw 20 q9 ∷
   rw 21 q2 ∷
   re 19 3 (ℓ "乑") ∷
   rw 20 q6 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q2 ∷
   rw 22 q8 ∷
   rw 23 q2 ∷
   re 21 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q2 ∷
   rw 23 q8 ∷
   rw 24 q2 ∷
   re 22 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q2 ∷
   rw 24 q8 ∷
   rw 25 q2 ∷
   re 23 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q2 ∷
   rw 25 q8 ∷
   rw 26 q2 ∷
   re 24 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q2 ∷
   rw 26 q8 ∷
   rw 27 q2 ∷
   re 25 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q2 ∷
   rw 27 q8 ∷
   rw 28 q2 ∷
   re 26 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q2 ∷
   rw 28 q8 ∷
   rw 29 q2 ∷
   re 27 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q2 ∷
   rw 29 q8 ∷
   rw 30 q2 ∷
   re 28 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q2 ∷
   rw 30 q8 ∷
   rw 31 q2 ∷
   re 29 3 (ℓ "中") ∷
   rw 30 q5 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q2 ∷
   rw 32 q8 ∷
   rw 33 q2 ∷
   re 31 3 (ℓ "中") ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q2 ∷
   rw 33 q8 ∷
   rw 34 q2 ∷
   re 32 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏丶乏") ∷
   rw 33 q2 ∷
   rw 34 q8 ∷
   rw 35 q2 ∷
   re 33 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏乇乏") ∷
   rw 34 q2 ∷
   rw 35 q9 ∷
   rw 36 q2 ∷
   re 34 3 (ℓ "乑") ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q2 ∷
   rw 36 q8 ∷
   rw 37 q2 ∷
   re 35 3 (ℓ "中") ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q2 ∷
   rw 37 q8 ∷
   rw 38 q2 ∷
   re 36 3 (ℓ "中") ∷
   rw 37 q12 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = eqn (ℓ "三丞") (ℓ "丞三") (low₁-comm ((S • S • S)) ((X ↑ ↑)))
  q21 : Eqn
  q21 = eqn (ℓ "三丘") (ℓ "丘三") (low₁-comm ((S • S • S)) ((X ↑)))
  q22 : Eqn
  q22 = eqn (ℓ "下丞") (ℓ "丞下") (low₁-comm ((K • iI)) ((X ↑ ↑)))
  q23 : Eqn
  q23 = eqn (ℓ "下丘") (ℓ "丘下") (low₁-comm ((K • iI)) ((X ↑)))
  q24 : Eqn
  q24 = eqn (ℓ "丈丞") (ℓ "丞丈") (low₁-comm (S) ((X ↑ ↑)))
  q25 : Eqn
  q25 = eqn (ℓ "丈丘") (ℓ "丘丈") (low₁-comm (S) ((X ↑)))
  q26 : Eqn
  q26 = eqn (ℓ "上丘") (ℓ "丘上") (low₁-comm (K) ((X ↑)))
  q27 : Eqn
  q27 = eqn (ℓ "上丞") (ℓ "丞上") (low₁-comm (K) ((X ↑ ↑)))
  q28 : Eqn
  q28 = wE 1 W
  q29 : Eqn
  q29 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q30 : Eqn
  q30 = eqn (ℓ "下乏") (ℓ "乏下") (low₁-comm ((K • iI)) ((Swap ↑)))
  q31 : Eqn
  q31 = eqn (ℓ "三乏") (ℓ "乏三") (low₁-comm ((S • S • S)) ((Swap ↑)))
  q32 : Eqn
  q32 = wE 2239 W
  q33 : Eqn
  q33 = wE 175 W
  q34 : Eqn
  q34 = wE 3 W
  q35 : Eqn
  q35 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q36 : Eqn
  q36 = wE 2240 W
  q37 : Eqn
  q37 = sE 2622 lem-pass-CS30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q38 : Eqn
  q38 = sE 1767 lem-pass-CKd30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q39 : Eqn
  q39 = sE 2623 lem-pass-CSd30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q40 : Eqn
  q40 = wE 2241 W

-- ca-split Gad(t=0, W=(2, 3), d=SdKdSS, e=-1) 3: 101 steps
lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-3 : ⟪ (ℓ "丘丞三下丈丈中九丮九三三上丈丘丞") ⟫ʷ ≈ ⟪ (ℓ "丞丮丞丞乒丞丞中丞丞中丞丘丞中九丮九丘丞丞丮丞丞丮丞丞乑丞丞中丞") ⟫ʷ
lem-ca-split-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩-3 = derive (ℓ "丘丞三下丈丈中九丮九三三上丈丘丞") (ℓ "丞丮丞丞乒丞丞中丞丞中丞丘丞中九丮九丘丞丞丮丞丞丮丞丞乑丞丞中丞")
  (rw⁻ 1 q20 ∷
   rw⁻ 0 q21 ∷
   rw⁻ 2 q22 ∷
   rw⁻ 1 q23 ∷
   rw⁻ 3 q24 ∷
   rw⁻ 2 q25 ∷
   rw⁻ 4 q24 ∷
   rw⁻ 3 q25 ∷
   rw 13 q25 ∷
   rw 12 q26 ∷
   rw 11 q21 ∷
   rw 10 q21 ∷
   rw 14 q24 ∷
   rw 13 q27 ∷
   rw 12 q20 ∷
   rw 11 q20 ∷
   rw 4 q28 ∷
   rw 3 q29 ∷
   rw 2 q29 ∷
   rw 1 q30 ∷
   rw 0 q31 ∷
   rw 1 q32 ∷
   rw 0 q33 ∷
   rw 3 q28 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q33 ∷
   rw 3 q33 ∷
   rw 6 q28 ∷
   re 4 3 (ℓ "乒") ∷
   rw 5 q33 ∷
   rw 6 q33 ∷
   rw 9 q28 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q33 ∷
   rw 9 q33 ∷
   rw 12 q28 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q33 ∷
   rw 14 q28 ∷
   re 12 3 (ℓ "丮") ∷
   rw 15 q28 ∷
   re 13 3 (ℓ "乒") ∷
   rw 16 q28 ∷
   re 14 3 (ℓ "中") ∷
   rw 17 q28 ∷
   re 15 3 (ℓ "中") ∷
   rw 16 q34 ∷
   rw 28 q28 ∷
   rw 27 q29 ∷
   rw 26 q35 ∷
   rw 25 q31 ∷
   rw 24 q31 ∷
   rw 25 q36 ∷
   rw 26 q28 ∷
   re 24 3 (ℓ "丮") ∷
   rw 27 q28 ∷
   re 25 3 (ℓ "丮") ∷
   rw 28 q28 ∷
   re 26 3 (ℓ "乑") ∷
   rw 29 q28 ∷
   re 27 3 (ℓ "中") ∷
   rw 28 q33 ∷
   rw 31 q28 ∷
   re 29 3 (ℓ "丮") ∷
   rw 30 q33 ∷
   rw 31 q33 ∷
   rw 34 q28 ∷
   re 32 3 (ℓ "丮") ∷
   rw 33 q33 ∷
   rw 34 q33 ∷
   rw 37 q28 ∷
   re 35 3 (ℓ "乑") ∷
   rw 36 q33 ∷
   rw 37 q33 ∷
   rw 40 q28 ∷
   re 38 3 (ℓ "中") ∷
   rw 39 q33 ∷
   rw 40 q34 ∷
   rw 15 q37 ∷
   rw 14 q37 ∷
   rw 13 q38 ∷
   rw 12 q39 ∷
   rw 28 q28 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q34 ∷
   re 26 1 (ℓ "乏乄乏") ∷
   rw 28 q34 ∷
   re 25 1 (ℓ "乏丨乏") ∷
   rw 27 q34 ∷
   re 24 1 (ℓ "乏丨乏") ∷
   rw 26 q34 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q34 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q34 ∷
   re 21 1 (ℓ "乏久乏") ∷
   rw 23 q34 ∷
   re 20 1 (ℓ "乏丨乏") ∷
   rw 22 q34 ∷
   rw 21 q40 ∷
   rw 20 q34 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q42 : Eqn
  q42 = wE 1674 W
  q43 : Eqn
  q43 = sE 2629 lem-pass-X3-CKd32-X3-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2
  q44 : Eqn
  q44 = wE 1675 W

-- pass [CKd32] [X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2 X3]: 5 steps
lem-pass-CKd32-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : ⟪ (ℓ "乘丘丞三下丈丈中九丮九三三上丈丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞三下丈丈中九丮九三三上丈丘丞乘") ⟫ʷ
lem-pass-CKd32-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = derive (ℓ "乘丘丞三下丈丈中九丮九三三上丈丘丞") (ℓ "丘丞三下丈丈中九丮九三三上丈丘丞乘")
  (rw 1 q41 ∷
   rw 0 q42 ∷
   rw 1 q43 ∷
   rw 15 q44 ∷
   rw⁻ 0 q41 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = wE 1409 W
  q46 : Eqn
  q46 = sE 2627 lem-pass-X3-CK32-X3-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2
  q47 : Eqn
  q47 = wE 1410 W

-- pass [CK32] [X2 X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2 X3]: 5 steps
lem-pass-CK32-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 : ⟪ (ℓ "乗丘丞三下丈丈中九丮九三三上丈丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞三下丈丈中九丮九三三上丈丘丞乗") ⟫ʷ
lem-pass-CK32-vs-X2-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2-X3 = derive (ℓ "乗丘丞三下丈丈中九丮九三三上丈丘丞") (ℓ "丘丞三下丈丈中九丮九三三上丈丘丞乗")
  (rw 1 q41 ∷
   rw 0 q45 ∷
   rw 1 q46 ∷
   rw 15 q47 ∷
   rw⁻ 0 q41 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q49 : Eqn
  q49 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q50 : Eqn
  q50 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q51 : Eqn
  q51 = wE 2299 W
  q52 : Eqn
  q52 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q53 : Eqn
  q53 = sE 2620 lem-CA-CSd10-Gad⟨t≡0-W≡⟨2-3⟩-d≡1-e≡-1⟩
  q54 : Eqn
  q54 = sE 2624 lem-pass-CKd30-vs-X2-X3-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2-X3
  q55 : Eqn
  q55 = sE 2619 lem-CA-CS10-Gad⟨t≡0-W≡⟨2-3⟩-d≡Sd-e≡-1⟩
  q56 : Eqn
  q56 = sE 1764 lem-pass-CK30-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3
  q57 : Eqn
  q57 = wE 2300 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 96 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丘丞中九丮九丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞中九丮九丘丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丘丞中九丮九丘丞") (ℓ "丘丞中九丮九丘丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 29 q28 ∷
   rw 28 q48 ∷
   rw 27 q48 ∷
   rw 26 q49 ∷
   rw 25 q48 ∷
   rw 24 q49 ∷
   rw 23 q49 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 24 q34 ∷
   rw 21 q49 ∷
   rw 20 q49 ∷
   rw 19 q49 ∷
   rw 18 q49 ∷
   rw 17 q49 ∷
   rw 16 q49 ∷
   rw 15 q50 ∷
   rw 14 q48 ∷
   rw 13 q49 ∷
   rw 12 q49 ∷
   rw 11 q49 ∷
   rw 10 q50 ∷
   rw 9 q48 ∷
   rw 8 q50 ∷
   rw 7 q48 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 8 q34 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw 7 q34 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw 6 q34 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q34 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw 4 q34 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q34 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q34 ∷
   rw 1 q51 ∷
   rw 2 q28 ∷
   re 0 3 (ℓ "乑") ∷
   rw⁻ 1 q49 ∷
   rw 4 q28 ∷
   re 2 3 (ℓ "乒") ∷
   rw⁻ 3 q52 ∷
   rw 4 q34 ∷
   rw 3 q53 ∷
   rw 2 q54 ∷
   rw 1 q55 ∷
   rw 0 q56 ∷
   rw 12 q28 ∷
   rw 11 q52 ∷
   re 10 1 (ℓ "乏久乏") ∷
   rw 12 q34 ∷
   rw 9 q49 ∷
   re 8 1 (ℓ "乏乄乏") ∷
   rw 10 q34 ∷
   rw 9 q57 ∷
   rw 10 q28 ∷
   re 8 3 (ℓ "中") ∷
   rw 11 q28 ∷
   re 9 3 (ℓ "中") ∷
   rw 12 q28 ∷
   re 10 3 (ℓ "乑") ∷
   rw 13 q28 ∷
   re 11 3 (ℓ "中") ∷
   rw 14 q28 ∷
   re 12 3 (ℓ "乑") ∷
   rw 15 q28 ∷
   re 13 3 (ℓ "乑") ∷
   rw 16 q28 ∷
   re 14 3 (ℓ "乓") ∷
   rw⁻ 15 q48 ∷
   rw⁻ 16 q50 ∷
   rw⁻ 17 q48 ∷
   rw⁻ 18 q50 ∷
   rw⁻ 19 q49 ∷
   rw⁻ 20 q49 ∷
   rw⁻ 21 q49 ∷
   rw⁻ 22 q48 ∷
   rw⁻ 23 q50 ∷
   rw⁻ 24 q49 ∷
   rw⁻ 25 q49 ∷
   rw⁻ 26 q49 ∷
   rw⁻ 27 q49 ∷
   rw⁻ 28 q49 ∷
   rw⁻ 29 q49 ∷
   rw 32 q28 ∷
   re 30 3 (ℓ "乓") ∷
   rw⁻ 31 q49 ∷
   rw⁻ 32 q49 ∷
   rw⁻ 33 q48 ∷
   rw⁻ 34 q49 ∷
   rw⁻ 35 q48 ∷
   rw⁻ 36 q48 ∷
   rw 37 q34 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q59 : Eqn
  q59 = wE 2113 W
  q60 : Eqn
  q60 = sE 2630 lem-pass-X3-CSd31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0
  q61 : Eqn
  q61 = wE 2114 W

-- pass [CSd31] [X0 X3 CS13 TOFF102 CSd13 TOFF102 X0 X3]: 5 steps
lem-pass-CSd31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : ⟪ (ℓ "举丌丞丽习举习丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丽习举习丌丞举") ⟫ʷ
lem-pass-CSd31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = derive (ℓ "举丌丞丽习举习丌丞") (ℓ "丌丞丽习举习丌丞举")
  (rw 1 q58 ∷
   rw 0 q59 ∷
   rw 1 q60 ∷
   rw 7 q61 ∷
   rw⁻ 0 q58 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = sE 198 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd13-X3
  q63 : Eqn
  q63 = sE 191 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd31-X3
  q64 : Eqn
  q64 = sE 196 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-X3
  q65 : Eqn
  q65 = sE 2548 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3
  q66 : Eqn
  q66 = sE 190 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK31-X3

-- Bar(SSKSKK;3,2->0) passes split Gad(t=1, W=(0, 3), d=SdKdSS, e=-1): 9 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞举丞丞乕丞丞丽丞丞丽丞丌丞丽习举习丌丞丞举丞丞举丞丞乔丞丞丽丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞丞乕丞丞丽丞丞丽丞丌丞丽习举习丌丞丞举丞丞举丞丞乔丞丞丽丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-split-Gad⟨t≡1-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞举丞丞乕丞丞丽丞丞丽丞丌丞丽习举习丌丞丞举丞丞举丞丞乔丞丞丽丞") (ℓ "丞举丞丞乕丞丞丽丞丞丽丞丌丞丽习举习丌丞丞举丞丞举丞丞乔丞丞丽丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 0 q62 ∷
   rw 3 q63 ∷
   rw 6 q64 ∷
   rw 9 q64 ∷
   rw 12 q65 ∷
   rw 20 q62 ∷
   rw 23 q62 ∷
   rw 26 q66 ∷
   rw 29 q64 ∷ []) Eq.refl

private
  q67 : Eqn
  q67 = sE 2628 lem-pass-X3-CKd32-X3-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0

-- pass [CKd32] [X0 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X3]: 5 steps
lem-pass-CKd32-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 : ⟪ (ℓ "乘丌丞丏丑与与丽习举习丏丏丐与丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丏丑与与丽习举习丏丏丐与丌丞乘") ⟫ʷ
lem-pass-CKd32-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 = derive (ℓ "乘丌丞丏丑与与丽习举习丏丏丐与丌丞") (ℓ "丌丞丏丑与与丽习举习丏丏丐与丌丞乘")
  (rw 1 q58 ∷
   rw 0 q42 ∷
   rw 1 q67 ∷
   rw 15 q44 ∷
   rw⁻ 0 q58 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = sE 2626 lem-pass-X3-CK32-X3-vs-X0-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0

-- pass [CK32] [X0 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X3]: 5 steps
lem-pass-CK32-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 : ⟪ (ℓ "乗丌丞丏丑与与丽习举习丏丏丐与丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丏丑与与丽习举习丏丏丐与丌丞乗") ⟫ʷ
lem-pass-CK32-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 = derive (ℓ "乗丌丞丏丑与与丽习举习丏丏丐与丌丞") (ℓ "丌丞丏丑与与丽习举习丏丏丐与丌丞乗")
  (rw 1 q58 ∷
   rw 0 q45 ∷
   rw 1 q68 ∷
   rw 15 q47 ∷
   rw⁻ 0 q58 ∷ []) Eq.refl
