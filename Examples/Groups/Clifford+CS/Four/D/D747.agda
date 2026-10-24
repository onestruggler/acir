{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD747 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D747 (W : Ws) (Sᴰ : SD747) where

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
  lem-pass-X2-CK20-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 914
  lem-pass-X2-CK20-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 0 Sᴰ
  lem-pass-X2-CKd20-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 915
  lem-pass-X2-CKd20-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 1 Sᴰ
  lem-pass-X2-CS20-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 916
  lem-pass-X2-CS20-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 2 Sᴰ
  lem-pass-X2-CSd20-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 917
  lem-pass-X2-CSd20-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 3 Sᴰ
  lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 1195
  lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 4 Sᴰ
  lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 1197
  lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 5 Sᴰ
  lem-pass-CK32-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 : St 2603
  lem-pass-CK32-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 = pickᴰ 6 Sᴰ
  lem-pass-CS20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 2219
  lem-pass-CS20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 7 Sᴰ
  lem-pass-CSd20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 2462
  lem-pass-CSd20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 8 Sᴰ
  lem-pass-CKd32-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 : St 2604
  lem-pass-CKd32-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 = pickᴰ 9 Sᴰ
  lem-pass-CCZ123-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : St 2006
  lem-pass-CCZ123-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = pickᴰ 10 Sᴰ
  lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 2605
  lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 11 Sᴰ
  lem-pass-CK20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : St 2581
  lem-pass-CK20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = pickᴰ 12 Sᴰ
  lem-pass-CS30-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : St 2606
  lem-pass-CS30-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = pickᴰ 13 Sᴰ
  lem-pass-CSd30-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : St 2607
  lem-pass-CSd30-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = pickᴰ 14 Sᴰ
  lem-CCZ⟨312⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩ : St 2608
  lem-CCZ⟨312⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩ = pickᴰ 15 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩-2 : St 2482
  lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩-2 = pickᴰ 16 Sᴰ
  lem-pass-CKd20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : St 2489
  lem-pass-CKd20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = pickᴰ 17 Sᴰ
  lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3 : St 2505
  lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3 = pickᴰ 18 Sᴰ
  lem-pass-X2-CKd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : St 2527
  lem-pass-X2-CKd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 19 Sᴰ
  lem-pass-CK23-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : St 2609
  lem-pass-CK23-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = pickᴰ 20 Sᴰ
  lem-pass-CKd20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : St 2595
  lem-pass-CKd20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = pickᴰ 21 Sᴰ
  lem-pass-CKd23-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : St 2610
  lem-pass-CKd23-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = pickᴰ 22 Sᴰ
  lem-pass-CS32-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 : St 2611
  lem-pass-CS32-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3 = pickᴰ 23 Sᴰ
  lem-pass-X2-CK23-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : St 2612
  lem-pass-X2-CK23-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = pickᴰ 24 Sᴰ
  lem-pass-X2-CKd20-X2-vs-Sd0-CS03-TOFF012-CSd03-TOFF012-S0 : St 2613
  lem-pass-X2-CKd20-X2-vs-Sd0-CS03-TOFF012-CSd03-TOFF012-S0 = pickᴰ 25 Sᴰ
  lem-pass-X2-CKd21-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : St 2614
  lem-pass-X2-CKd21-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = pickᴰ 26 Sᴰ
  lem-pass-X2-CKd23-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : St 2615
  lem-pass-X2-CKd23-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = pickᴰ 27 Sᴰ
  lem-pass-X3-CK32-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : St 2616
  lem-pass-X3-CK32-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = pickᴰ 28 Sᴰ
  lem-pass-X3-CKd32-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 : St 2617
  lem-pass-X3-CKd32-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 = pickᴰ 29 Sᴰ

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
  q13 = sE 2607 lem-pass-CSd30-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3
  q14 : Eqn
  q14 = sE 2595 lem-pass-CKd20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3
  q15 : Eqn
  q15 = sE 2606 lem-pass-CS30-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3
  q16 : Eqn
  q16 = sE 2581 lem-pass-CK20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3
  q17 : Eqn
  q17 = wE 76 W
  q18 : Eqn
  q18 = wE 137 W
  q19 : Eqn
  q19 = wE 2433 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 X3 TOFF012 CS03 TOFF012 CSd03 X2 X3]: 236 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丞九中九丮丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞九中九丮丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丞九中九丮丘丞") (ℓ "丘丞九中九丮丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
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
   rw 12 q1 ∷
   re 11 1 (ℓ "乏丨乏") ∷
   rw⁻ 13 q2 ∷
   rw 12 q17 ∷
   rw⁻ 11 q2 ∷
   re 12 3 (ℓ "举") ∷
   rw 10 q18 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q2 ∷
   rw 10 q4 ∷
   rw⁻ 9 q2 ∷
   re 10 3 (ℓ "丽") ∷
   rw 8 q3 ∷
   rw 9 q19 ∷
   rw 8 q9 ∷
   rw 9 q9 ∷
   rw 10 q8 ∷
   rw 11 q9 ∷
   rw 12 q8 ∷
   rw 13 q8 ∷
   rw 14 q5 ∷
   re 16 1 (ℓ "乏乇乏") ∷
   rw 15 q2 ∷
   rw 16 q8 ∷
   rw 17 q2 ∷
   re 15 3 (ℓ "乑") ∷
   rw 16 q6 ∷
   re 18 1 (ℓ "乏乇乏") ∷
   rw 17 q2 ∷
   rw 18 q8 ∷
   rw 19 q2 ∷
   re 17 3 (ℓ "乑") ∷
   rw 18 q6 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q2 ∷
   rw 20 q9 ∷
   rw 21 q2 ∷
   re 19 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q2 ∷
   rw 21 q9 ∷
   rw 22 q2 ∷
   re 20 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q2 ∷
   rw 22 q9 ∷
   rw 23 q2 ∷
   re 21 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏乇乏") ∷
   rw 22 q2 ∷
   rw 23 q8 ∷
   rw 24 q2 ∷
   re 22 3 (ℓ "乑") ∷
   rw 23 q6 ∷
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
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q2 ∷
   rw 29 q9 ∷
   rw 30 q2 ∷
   re 28 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q2 ∷
   rw 30 q9 ∷
   rw 31 q2 ∷
   re 29 3 (ℓ "中") ∷
   rw 30 q5 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q2 ∷
   rw 32 q9 ∷
   rw 33 q2 ∷
   re 31 3 (ℓ "中") ∷
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
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q2 ∷
   rw 35 q9 ∷
   rw 36 q2 ∷
   re 34 3 (ℓ "中") ∷
   re 36 1 (ℓ "乏乇乏") ∷
   rw 35 q2 ∷
   rw 36 q8 ∷
   rw 37 q2 ∷
   re 35 3 (ℓ "乑") ∷
   re 37 1 (ℓ "乏乇乏") ∷
   rw 36 q2 ∷
   rw 37 q8 ∷
   rw 38 q2 ∷
   re 36 3 (ℓ "乑") ∷
   rw 37 q12 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = wE 2425 W
  q21 : Eqn
  q21 = sE 2610 lem-pass-CKd23-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3
  q22 : Eqn
  q22 = sE 2006 lem-pass-CCZ123-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3
  q23 : Eqn
  q23 = sE 2609 lem-pass-CK23-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3
  q24 : Eqn
  q24 = wE 2426 W

-- pass [TOFF312] [X0 X2 X3 TOFF102 CS13 TOFF102 CSd13 X0 X2 X3]: 5 steps
lem-pass-TOFF312-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : ⟪ (ℓ "乨丌丘丞习丽习举丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞习丽习举丌丘丞乨") ⟫ʷ
lem-pass-TOFF312-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = derive (ℓ "乨丌丘丞习丽习举丌丘丞") (ℓ "丌丘丞习丽习举丌丘丞乨")
  (rw 0 q20 ∷
   rw 2 q21 ∷
   rw 1 q22 ∷
   rw 0 q23 ∷
   rw 10 q24 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = eqn (ℓ "世丞") (ℓ "丞世") (low₃-comm ((K ↑ ↑)) (X))
  q26 : Eqn
  q26 = eqn (ℓ "丌世") (ℓ "世丌") (low₁-comm (X) ((K ↑)))
  q27 : Eqn
  q27 = eqn (ℓ "且丞") (ℓ "丞且") (low₃-comm ((S ↑ ↑)) (X))
  q28 : Eqn
  q28 = eqn (ℓ "丌且") (ℓ "且丌") (low₁-comm (X) ((S ↑)))
  q29 : Eqn
  q29 = eqn (ℓ "丗丞") (ℓ "丞丗") (low₃-comm (((K • iI) ↑ ↑)) (X))
  q30 : Eqn
  q30 = eqn (ℓ "丌丗") (ℓ "丗丌") (low₁-comm (X) (((K • iI) ↑)))
  q31 : Eqn
  q31 = eqn (ℓ "丌丕") (ℓ "丕丌") (low₁-comm (X) (((S • S • S) ↑)))
  q32 : Eqn
  q32 = eqn (ℓ "丕丞") (ℓ "丞丕") (low₃-comm (((S • S • S) ↑ ↑)) (X))
  q33 : Eqn
  q33 = wE 2305 W
  q34 : Eqn
  q34 = wE 2306 W
  q35 : Eqn
  q35 = sE 2604 lem-pass-CKd32-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3
  q36 : Eqn
  q36 = sE 2611 lem-pass-CS32-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3
  q37 : Eqn
  q37 = sE 2603 lem-pass-CK32-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3
  q38 : Eqn
  q38 = wE 2307 W

-- ca-split Gad(t=2, W=(0, 3), d=KSSKd, e=1) 3: 23 steps
lem-ca-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡KSSKd-e≡1⟩-3 : ⟪ (ℓ "丌丞世且且丗乣义乣乊世丕丕丗丌丞") ⟫ʷ ≈ ⟪ (ℓ "丞乗丞丞义丞丞义丞丞乘丞丌丞乣义乣乊丌丞丞乗丞丞乊丞丞乊丞丞乘丞") ⟫ʷ
lem-ca-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡KSSKd-e≡1⟩-3 = derive (ℓ "丌丞世且且丗乣义乣乊世丕丕丗丌丞") (ℓ "丞乗丞丞义丞丞义丞丞乘丞丌丞乣义乣乊丌丞丞乗丞丞乊丞丞乊丞丞乘丞")
  (rw⁻ 1 q25 ∷
   rw 0 q26 ∷
   rw⁻ 2 q27 ∷
   rw 1 q28 ∷
   rw⁻ 3 q27 ∷
   rw 2 q28 ∷
   rw⁻ 4 q29 ∷
   rw 3 q30 ∷
   rw⁻ 13 q30 ∷
   rw⁻ 12 q31 ∷
   rw⁻ 11 q31 ∷
   rw⁻ 10 q26 ∷
   rw 14 q29 ∷
   rw 13 q32 ∷
   rw 12 q32 ∷
   rw 11 q25 ∷
   rw 0 q33 ∷
   rw 24 q34 ∷
   rw 15 q35 ∷
   rw 14 q36 ∷
   rw 13 q36 ∷
   rw 12 q37 ∷
   rw 20 q38 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = eqn (ℓ "丌丘") (ℓ "丘丌") (low₁-comm (X) ((X ↑)))
  q40 : Eqn
  q40 = wE 1478 W
  q41 : Eqn
  q41 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q42 : Eqn
  q42 = sE 2614 lem-pass-X2-CKd21-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3
  q43 : Eqn
  q43 = wE 1479 W

-- pass [CKd21] [X0 X2 X3 TOFF102 CS13 TOFF102 CSd13 X0 X2 X3]: 7 steps
lem-pass-CKd21-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : ⟪ (ℓ "么丌丘丞习丽习举丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞习丽习举丌丘丞么") ⟫ʷ
lem-pass-CKd21-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = derive (ℓ "么丌丘丞习丽习举丌丘丞") (ℓ "丌丘丞习丽习举丌丘丞么")
  (rw 1 q39 ∷
   rw 0 q40 ∷
   rw 11 q41 ∷
   rw 1 q42 ∷
   rw 9 q43 ∷
   rw⁻ 0 q39 ∷
   rw⁻ 8 q41 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = wE 2434 W
  q45 : Eqn
  q45 = wE 2435 W
  q46 : Eqn
  q46 = sE 1195 lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q47 : Eqn
  q47 = sE 2527 lem-pass-X2-CKd21-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q48 : Eqn
  q48 = sE 1197 lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q49 : Eqn
  q49 = wE 2436 W

-- ca-split Gad(t=1, W=(), d=SdKdSS, e=-1) 2: 7 steps
lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SdKdSS-e≡-1⟩-2 : ⟪ (ℓ "丏丑与与丽习举习丏丏丐与") ⟫ʷ ≈ ⟪ (ℓ "丷么丶丶丽习举习丷丷乇丶") ⟫ʷ
lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SdKdSS-e≡-1⟩-2 = derive (ℓ "丏丑与与丽习举习丏丏丐与") (ℓ "丷么丶丶丽习举习丷丷乇丶")
  (rw 0 q44 ∷
   rw 20 q45 ∷
   rw 13 q46 ∷
   rw 10 q46 ∷
   rw 7 q47 ∷
   rw 4 q48 ∷
   rw 8 q49 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = sE 2482 lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩-2
  q51 : Eqn
  q51 = sE 916 lem-pass-X2-CS20-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q52 : Eqn
  q52 = sE 914 lem-pass-X2-CK20-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q53 : Eqn
  q53 = sE 2605 lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q54 : Eqn
  q54 = sE 915 lem-pass-X2-CKd20-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q55 : Eqn
  q55 = sE 917 lem-pass-X2-CSd20-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q56 : Eqn
  q56 = sE 2482 lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩-2

-- pass [CS13 TOFF102 CSd13 TOFF102] [X2 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2]: 7 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 : ⟪ (ℓ "丽习举习丘丈上中九丮九下三丘") ⟫ʷ ≈ ⟪ (ℓ "丘丈上中九丮九下三丘丽习举习") ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 = derive (ℓ "丽习举习丘丈上中九丮九下三丘") (ℓ "丘丈上中九丮九下三丘丽习举习")
  (rw 4 q50 ∷
   rw⁻ 0 q51 ∷
   rw⁻ 3 q52 ∷
   rw 6 q53 ∷
   rw⁻ 12 q54 ∷
   rw⁻ 15 q55 ∷
   rw⁻ 0 q56 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = wE 1674 W
  q58 : Eqn
  q58 = sE 2617 lem-pass-X3-CKd32-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0
  q59 : Eqn
  q59 = wE 1675 W

-- pass [CKd32] [X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X3]: 3 steps
lem-pass-CKd32-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : ⟪ (ℓ "乘丞三下丈丈中九丮九三三上丈丞") ⟫ʷ ≈ ⟪ (ℓ "丞三下丈丈中九丮九三三上丈丞乘") ⟫ʷ
lem-pass-CKd32-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = derive (ℓ "乘丞三下丈丈中九丮九三三上丈丞") (ℓ "丞三下丈丈中九丮九三三上丈丞乘")
  (rw 0 q57 ∷
   rw 1 q58 ∷
   rw 13 q59 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = sE 2505 lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3
  q61 : Eqn
  q61 = sE 2608 lem-CCZ⟨312⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩
  q62 : Eqn
  q62 = sE 2505 lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3

-- pass [CCZ123] [X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X3]: 3 steps
lem-pass-CCZ123-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : ⟪ (ℓ "乜丞三下丈丈中九丮九三三上丈丞") ⟫ʷ ≈ ⟪ (ℓ "丞三下丈丈中九丮九三三上丈丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = derive (ℓ "乜丞三下丈丈中九丮九三三上丈丞") (ℓ "丞三下丈丈中九丮九三三上丈丞乜")
  (rw 1 q60 ∷
   rw 0 q61 ∷
   rw⁻ 0 q62 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = wE 1409 W
  q64 : Eqn
  q64 = sE 2616 lem-pass-X3-CK32-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0
  q65 : Eqn
  q65 = wE 1410 W

-- pass [CK32] [X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X3]: 3 steps
lem-pass-CK32-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : ⟪ (ℓ "乗丞三下丈丈中九丮九三三上丈丞") ⟫ʷ ≈ ⟪ (ℓ "丞三下丈丈中九丮九三三上丈丞乗") ⟫ʷ
lem-pass-CK32-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = derive (ℓ "乗丞三下丈丈中九丮九三三上丈丞") (ℓ "丞三下丈丈中九丮九三三上丈丞乗")
  (rw 0 q63 ∷
   rw 1 q64 ∷
   rw 13 q65 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = eqn (ℓ "三丘") (ℓ "丘三") (low₁-comm ((S • S • S)) ((X ↑)))
  q67 : Eqn
  q67 = eqn (ℓ "下丘") (ℓ "丘下") (low₁-comm ((K • iI)) ((X ↑)))
  q68 : Eqn
  q68 = eqn (ℓ "丈丘") (ℓ "丘丈") (low₁-comm (S) ((X ↑)))
  q69 : Eqn
  q69 = eqn (ℓ "上丘") (ℓ "丘上") (low₁-comm (K) ((X ↑)))
  q70 : Eqn
  q70 = wE 2239 W
  q71 : Eqn
  q71 = wE 2240 W
  q72 : Eqn
  q72 = sE 2219 lem-pass-CS20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q73 : Eqn
  q73 = sE 2489 lem-pass-CKd20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q74 : Eqn
  q74 = sE 2462 lem-pass-CSd20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2
  q75 : Eqn
  q75 = wE 2241 W

-- ca-split Gad(t=0, W=(2,), d=SdKdSS, e=-1) 2: 15 steps
lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩-2 : ⟪ (ℓ "丘三下丈丈中九丮九三三上丈丘") ⟫ʷ ≈ ⟪ (ℓ "丘丨丘丘久丘丘丧丘丘丧丘丘中九丮九丘丘丨丘丘丨丘丘乄丘丘丧丘") ⟫ʷ
lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩-2 = derive (ℓ "丘三下丈丈中九丮九三三上丈丘") (ℓ "丘丨丘丘久丘丘丧丘丘丧丘丘中九丮九丘丘丨丘丘丨丘丘乄丘丘丧丘")
  (rw⁻ 0 q66 ∷
   rw⁻ 1 q67 ∷
   rw⁻ 2 q68 ∷
   rw⁻ 3 q68 ∷
   rw 12 q68 ∷
   rw 11 q69 ∷
   rw 10 q66 ∷
   rw 9 q66 ∷
   rw 0 q70 ∷
   rw 22 q71 ∷
   rw 15 q72 ∷
   rw 14 q72 ∷
   rw 13 q73 ∷
   rw 12 q74 ∷
   rw 18 q75 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = wE 1464 W
  q77 : Eqn
  q77 = sE 2613 lem-pass-X2-CKd20-X2-vs-Sd0-CS03-TOFF012-CSd03-TOFF012-S0
  q78 : Eqn
  q78 = wE 1465 W

-- pass [CKd20] [X2 Sd0 CS03 TOFF012 CSd03 TOFF012 S0 X2]: 3 steps
lem-pass-CKd20-vs-X2-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2 : ⟪ (ℓ "久丘三中九丮九丈丘") ⟫ʷ ≈ ⟪ (ℓ "丘三中九丮九丈丘久") ⟫ʷ
lem-pass-CKd20-vs-X2-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2 = derive (ℓ "久丘三中九丮九丈丘") (ℓ "丘三中九丮九丈丘久")
  (rw 0 q76 ∷
   rw 1 q77 ∷
   rw 7 q78 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = wE 2301 W
  q80 : Eqn
  q80 = sE 2615 lem-pass-X2-CKd23-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0
  q81 : Eqn
  q81 = wE 2302 W

-- pass [CKd23] [X2 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2]: 3 steps
lem-pass-CKd23-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 : ⟪ (ℓ "乎丘三下丈丈中九丮九三三上丈丘") ⟫ʷ ≈ ⟪ (ℓ "丘三下丈丈中九丮九三三上丈丘乎") ⟫ʷ
lem-pass-CKd23-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 = derive (ℓ "乎丘三下丈丈中九丮九三三上丈丘") (ℓ "丘三下丈丈中九丮九三三上丈丘乎")
  (rw 0 q79 ∷
   rw 1 q80 ∷
   rw 13 q81 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = wE 2303 W
  q83 : Eqn
  q83 = sE 2612 lem-pass-X2-CK23-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0
  q84 : Eqn
  q84 = wE 2304 W

-- pass [CK23] [X2 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2]: 3 steps
lem-pass-CK23-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 : ⟪ (ℓ "乍丘三下丈丈中九丮九三三上丈丘") ⟫ʷ ≈ ⟪ (ℓ "丘三下丈丈中九丮九三三上丈丘乍") ⟫ʷ
lem-pass-CK23-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 = derive (ℓ "乍丘三下丈丈中九丮九三三上丈丘") (ℓ "丘三下丈丈中九丮九三三上丈丘乍")
  (rw 0 q82 ∷
   rw 1 q83 ∷
   rw 13 q84 ∷ []) Eq.refl
