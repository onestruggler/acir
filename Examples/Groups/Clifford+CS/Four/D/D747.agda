{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D747 (W : Ws) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Four.D.D517 W using (lem-pass-X2-CK20-X2-vs-CS13-TOFF102-CSd13-TOFF102 ; lem-pass-X2-CKd20-X2-vs-CS13-TOFF102-CSd13-TOFF102 ; lem-pass-X2-CS20-X2-vs-CS13-TOFF102-CSd13-TOFF102 ; lem-pass-X2-CSd20-X2-vs-CS13-TOFF102-CSd13-TOFF102)
open import Examples.Groups.Clifford+CS.Four.D.D544 W using (lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102 ; lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102)
open import Examples.Groups.Clifford+CS.Four.D.D589 W using (lem-pass-CK32-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3)
open import Examples.Groups.Clifford+CS.Four.D.D596 W using (lem-pass-CS20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 ; lem-pass-CSd20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2)
open import Examples.Groups.Clifford+CS.Four.D.D612 W using (lem-pass-CKd32-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3)
open import Examples.Groups.Clifford+CS.Four.D.D698 W using (lem-pass-CCZ123-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 ; lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2)
open import Examples.Groups.Clifford+CS.Four.D.D722 W using (lem-pass-CK20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 ; lem-pass-CS30-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 ; lem-pass-CSd30-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3)
open import Examples.Groups.Clifford+CS.Four.D.D723 W using (lem-CCZ⟨312⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩)
open import Examples.Groups.Clifford+CS.Four.D.D730 W using (lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩-2 ; lem-pass-CKd20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2)
open import Examples.Groups.Clifford+CS.Four.D.D731 W using (lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3)
open import Examples.Groups.Clifford+CS.Four.D.D734 W using (lem-pass-X2-CKd21-X2-vs-CS13-TOFF102-CSd13-TOFF102)
open import Examples.Groups.Clifford+CS.Four.D.D739 W using (lem-pass-CK23-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 ; lem-pass-CKd20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 ; lem-pass-CKd23-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 ; lem-pass-CS32-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3)
open import Examples.Groups.Clifford+CS.Four.D.D740 W using (lem-pass-X2-CK23-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 ; lem-pass-X2-CKd20-X2-vs-Sd0-CS03-TOFF012-CSd03-TOFF012-S0 ; lem-pass-X2-CKd21-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 ; lem-pass-X2-CKd23-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 ; lem-pass-X3-CK32-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0 ; lem-pass-X3-CKd32-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0)

private
  q1 : Eqn
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q4 : Eqn
  q4 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q5 : Eqn
  q5 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q6 : Eqn
  q6 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q7 : Eqn
  q7 = eqn (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) (CK21 ∷ CS13 ∷ CK21⁻ ∷ CS13⁻ ∷ []) (wn 2432 W)
  q8 : Eqn
  q8 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CK21⁻ ∷ []) (CK20⁻ ∷ Sw01 ∷ []) (wn 139 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q13 : Eqn
  q13 = eqn (CS03⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS03⁻ ∷ []) (lem-pass-CSd30-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3)
  q14 : Eqn
  q14 = eqn (CK20⁻ ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CK20⁻ ∷ []) (lem-pass-CKd20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3)
  q15 : Eqn
  q15 = eqn (CS03 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ []) (lem-pass-CS30-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3)
  q16 : Eqn
  q16 = eqn (CK20 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CK20 ∷ []) (lem-pass-CK20-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3)
  q17 : Eqn
  q17 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q18 : Eqn
  q18 = eqn (CK20⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK21⁻ ∷ []) (wn 137 W)
  q19 : Eqn
  q19 = eqn (CK21 ∷ CS13 ∷ CK21⁻ ∷ CS13⁻ ∷ []) (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) (wn 2433 W)

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 X3 TOFF012 CS03 TOFF012 CSd03 X2 X3]: 236 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-TOFF012-CS03-TOFF012-CSd03-X2-X3 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 29 q1 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q2 ∷
   rw 29 q3 ∷
   rw⁻ 28 q2 ∷
   re 29 3 (CK31 ∷ []) ∷
   re 27 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q2 ∷
   rw 28 q3 ∷
   rw⁻ 27 q2 ∷
   re 28 3 (CK31 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q2 ∷
   rw 27 q4 ∷
   rw⁻ 26 q2 ∷
   re 27 3 (CS13 ∷ []) ∷
   re 25 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q2 ∷
   rw 26 q3 ∷
   rw⁻ 25 q2 ∷
   re 26 3 (CK31 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q2 ∷
   rw 25 q4 ∷
   rw⁻ 24 q2 ∷
   re 25 3 (CS13 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q2 ∷
   rw 24 q4 ∷
   rw⁻ 23 q2 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw⁻ 22 q5 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q2 ∷
   rw 22 q4 ∷
   rw⁻ 21 q2 ∷
   re 22 3 (CS13 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q2 ∷
   rw 21 q4 ∷
   rw⁻ 20 q2 ∷
   re 21 3 (CS13 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q2 ∷
   rw 20 q4 ∷
   rw⁻ 19 q2 ∷
   re 20 3 (CS13 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q2 ∷
   rw 19 q4 ∷
   rw⁻ 18 q2 ∷
   re 19 3 (CS13 ∷ []) ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q2 ∷
   rw 18 q4 ∷
   rw⁻ 17 q2 ∷
   re 18 3 (CS13 ∷ []) ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q2 ∷
   rw 17 q4 ∷
   rw⁻ 16 q2 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw⁻ 15 q6 ∷
   re 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q2 ∷
   rw 15 q3 ∷
   rw⁻ 14 q2 ∷
   re 15 3 (CK31 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q2 ∷
   rw 14 q4 ∷
   rw⁻ 13 q2 ∷
   re 14 3 (CS13 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q2 ∷
   rw 13 q4 ∷
   rw⁻ 12 q2 ∷
   re 13 3 (CS13 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q2 ∷
   rw 12 q4 ∷
   rw⁻ 11 q2 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw⁻ 10 q6 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q2 ∷
   rw 10 q3 ∷
   rw⁻ 9 q2 ∷
   re 10 3 (CK31 ∷ []) ∷
   rw⁻ 8 q6 ∷
   re 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q2 ∷
   rw 8 q3 ∷
   rw⁻ 7 q2 ∷
   re 8 3 (CK31 ∷ []) ∷
   rw⁻ 6 q5 ∷
   rw 5 q3 ∷
   rw 4 q3 ∷
   rw 3 q4 ∷
   rw 2 q3 ∷
   rw 1 q4 ∷
   rw 0 q4 ∷
   rw 1 q7 ∷
   rw 0 q8 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q2 ∷
   rw 2 q9 ∷
   rw 3 q2 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q10 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q2 ∷
   rw 4 q11 ∷
   rw 5 q2 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 4 q12 ∷
   rw 3 q13 ∷
   rw 2 q14 ∷
   rw 1 q15 ∷
   rw 0 q16 ∷
   rw 12 q1 ∷
   re 11 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q2 ∷
   rw 12 q17 ∷
   rw⁻ 11 q2 ∷
   re 12 3 (CS13⁻ ∷ []) ∷
   rw 10 q18 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q2 ∷
   rw 10 q4 ∷
   rw⁻ 9 q2 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 8 q3 ∷
   rw 9 q19 ∷
   rw 8 q9 ∷
   rw 9 q9 ∷
   rw 10 q8 ∷
   rw 11 q9 ∷
   rw 12 q8 ∷
   rw 13 q8 ∷
   rw 14 q5 ∷
   re 16 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 15 q2 ∷
   rw 16 q8 ∷
   rw 17 q2 ∷
   re 15 3 (CK30 ∷ []) ∷
   rw 16 q6 ∷
   re 18 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 17 q2 ∷
   rw 18 q8 ∷
   rw 19 q2 ∷
   re 17 3 (CK30 ∷ []) ∷
   rw 18 q6 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q2 ∷
   rw 20 q9 ∷
   rw 21 q2 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q2 ∷
   rw 21 q9 ∷
   rw 22 q2 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q2 ∷
   rw 22 q9 ∷
   rw 23 q2 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 22 q2 ∷
   rw 23 q8 ∷
   rw 24 q2 ∷
   re 22 3 (CK30 ∷ []) ∷
   rw 23 q6 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   rw 25 q9 ∷
   rw 26 q2 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q2 ∷
   rw 26 q9 ∷
   rw 27 q2 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q2 ∷
   rw 27 q9 ∷
   rw 28 q2 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q2 ∷
   rw 28 q9 ∷
   rw 29 q2 ∷
   re 27 3 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q2 ∷
   rw 29 q9 ∷
   rw 30 q2 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q2 ∷
   rw 30 q9 ∷
   rw 31 q2 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 30 q5 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q2 ∷
   rw 32 q9 ∷
   rw 33 q2 ∷
   re 31 3 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q2 ∷
   rw 33 q9 ∷
   rw 34 q2 ∷
   re 32 3 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 33 q2 ∷
   rw 34 q8 ∷
   rw 35 q2 ∷
   re 33 3 (CK30 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q2 ∷
   rw 35 q9 ∷
   rw 36 q2 ∷
   re 34 3 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 35 q2 ∷
   rw 36 q8 ∷
   rw 37 q2 ∷
   re 35 3 (CK30 ∷ []) ∷
   re 37 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 36 q2 ∷
   rw 37 q8 ∷
   rw 38 q2 ∷
   re 36 3 (CK30 ∷ []) ∷
   rw 37 q12 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = eqn (Toff312 ∷ []) (CK23 ∷ CCZ123 ∷ CK23⁻ ∷ []) (wn 2425 W)
  q21 : Eqn
  q21 = eqn (CK23⁻ ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CK23⁻ ∷ []) (lem-pass-CKd23-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3)
  q22 : Eqn
  q22 = eqn (CCZ123 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3)
  q23 : Eqn
  q23 = eqn (CK23 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CK23 ∷ []) (lem-pass-CK23-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3)
  q24 : Eqn
  q24 = eqn (CK23 ∷ CCZ123 ∷ CK23⁻ ∷ []) (Toff312 ∷ []) (wn 2426 W)

-- pass [TOFF312] [X0 X2 X3 TOFF102 CS13 TOFF102 CSd13 X0 X2 X3]: 5 steps
lem-pass-TOFF312-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : ⟪ (Toff312 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ Toff312 ∷ []) ⟫ʷ
lem-pass-TOFF312-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = derive (Toff312 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ Toff312 ∷ [])
  (rw 0 q20 ∷
   rw 2 q21 ∷
   rw 1 q22 ∷
   rw 0 q23 ∷
   rw 10 q24 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = eqn (K2 ∷ X3 ∷ []) (X3 ∷ K2 ∷ []) (low₃-comm ((K ↑ ↑)) (X))
  q26 : Eqn
  q26 = eqn (X0 ∷ K2 ∷ []) (K2 ∷ X0 ∷ []) (low₁-comm (X) ((K ↑)))
  q27 : Eqn
  q27 = eqn (S2 ∷ X3 ∷ []) (X3 ∷ S2 ∷ []) (low₃-comm ((S ↑ ↑)) (X))
  q28 : Eqn
  q28 = eqn (X0 ∷ S2 ∷ []) (S2 ∷ X0 ∷ []) (low₁-comm (X) ((S ↑)))
  q29 : Eqn
  q29 = eqn (K2⁻ ∷ X3 ∷ []) (X3 ∷ K2⁻ ∷ []) (low₃-comm (((K • iI) ↑ ↑)) (X))
  q30 : Eqn
  q30 = eqn (X0 ∷ K2⁻ ∷ []) (K2⁻ ∷ X0 ∷ []) (low₁-comm (X) (((K • iI) ↑)))
  q31 : Eqn
  q31 = eqn (X0 ∷ S2⁻ ∷ []) (S2⁻ ∷ X0 ∷ []) (low₁-comm (X) (((S • S • S) ↑)))
  q32 : Eqn
  q32 = eqn (S2⁻ ∷ X3 ∷ []) (X3 ∷ S2⁻ ∷ []) (low₃-comm (((S • S • S) ↑ ↑)) (X))
  q33 : Eqn
  q33 = eqn (K2 ∷ S2 ∷ S2 ∷ K2⁻ ∷ []) (X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CK32⁻ ∷ []) (wn 2305 W)
  q34 : Eqn
  q34 = eqn (K2 ∷ S2⁻ ∷ S2⁻ ∷ K2⁻ ∷ []) (CK32 ∷ CS23⁻ ∷ CS23⁻ ∷ CK32⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (wn 2306 W)
  q35 : Eqn
  q35 = eqn (CK32⁻ ∷ X0 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X0 ∷ X3 ∷ CK32⁻ ∷ []) (lem-pass-CKd32-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3)
  q36 : Eqn
  q36 = eqn (CS23 ∷ X0 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X0 ∷ X3 ∷ CS23 ∷ []) (lem-pass-CS32-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3)
  q37 : Eqn
  q37 = eqn (CK32 ∷ X0 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X0 ∷ X3 ∷ CK32 ∷ []) (lem-pass-CK32-vs-X0-X3-TOFF201-CS23-TOFF201-CSd23-X0-X3)
  q38 : Eqn
  q38 = eqn (CK32 ∷ CS23 ∷ CS23 ∷ CK32⁻ ∷ CK32 ∷ CS23⁻ ∷ CS23⁻ ∷ CK32⁻ ∷ []) [] (wn 2307 W)

-- ca-split Gad(t=2, W=(0, 3), d=KSSKd, e=1) 3: 23 steps
lem-ca-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡KSSKd-e≡1⟩-3 : ⟪ (X0 ∷ X3 ∷ K2 ∷ S2 ∷ S2 ∷ K2⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ K2 ∷ S2⁻ ∷ S2⁻ ∷ K2⁻ ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X0 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X0 ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
lem-ca-split-Gad⟨t≡2-W≡⟨0-3⟩-d≡KSSKd-e≡1⟩-3 = derive (X0 ∷ X3 ∷ K2 ∷ S2 ∷ S2 ∷ K2⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ K2 ∷ S2⁻ ∷ S2⁻ ∷ K2⁻ ∷ X0 ∷ X3 ∷ []) (X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CS23 ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ X0 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X0 ∷ X3 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ [])
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
  q39 = eqn (X0 ∷ X2 ∷ []) (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑)))
  q40 : Eqn
  q40 = eqn (CK21⁻ ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (wn 1478 W)
  q41 : Eqn
  q41 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q42 : Eqn
  q42 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3)
  q43 : Eqn
  q43 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK21⁻ ∷ []) (wn 1479 W)

-- pass [CKd21] [X0 X2 X3 TOFF102 CS13 TOFF102 CSd13 X0 X2 X3]: 7 steps
lem-pass-CKd21-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 : ⟪ (CK21⁻ ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CK21⁻ ∷ []) ⟫ʷ
lem-pass-CKd21-vs-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3 = derive (CK21⁻ ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CK21⁻ ∷ [])
  (rw 1 q39 ∷
   rw 0 q40 ∷
   rw 11 q41 ∷
   rw 1 q42 ∷
   rw 9 q43 ∷
   rw⁻ 0 q39 ∷
   rw⁻ 8 q41 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = eqn (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (wn 2434 W)
  q45 : Eqn
  q45 = eqn (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ CS12⁻ ∷ CS12⁻ ∷ CK21 ∷ CS12 ∷ []) (wn 2435 W)
  q46 : Eqn
  q46 = eqn (X2 ∷ CS12 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102)
  q47 : Eqn
  q47 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd21-X2-vs-CS13-TOFF102-CSd13-TOFF102)
  q48 : Eqn
  q48 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102)
  q49 : Eqn
  q49 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ X2 ∷ CK21 ∷ X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) [] (wn 2436 W)

-- ca-split Gad(t=1, W=(), d=SdKdSS, e=-1) 2: 7 steps
lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SdKdSS-e≡-1⟩-2 : ⟪ (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CS12⁻ ∷ CS12⁻ ∷ CK21 ∷ CS12 ∷ []) ⟫ʷ
lem-ca-split-Gad⟨t≡1-W≡⟨⟩-d≡SdKdSS-e≡-1⟩-2 = derive (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (CS12⁻ ∷ CK21⁻ ∷ CS12 ∷ CS12 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CS12⁻ ∷ CS12⁻ ∷ CK21 ∷ CS12 ∷ [])
  (rw 0 q44 ∷
   rw 20 q45 ∷
   rw 13 q46 ∷
   rw 10 q46 ∷
   rw 7 q47 ∷
   rw 4 q48 ∷
   rw 8 q49 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = eqn (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩-2)
  q51 : Eqn
  q51 = eqn (X2 ∷ CS02 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS02 ∷ X2 ∷ []) lem-pass-X2-CS20-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q52 : Eqn
  q52 = eqn (X2 ∷ CK20 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK20 ∷ X2 ∷ []) lem-pass-X2-CK20-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q53 : Eqn
  q53 = eqn (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2)
  q54 : Eqn
  q54 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) lem-pass-X2-CKd20-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q55 : Eqn
  q55 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) lem-pass-X2-CSd20-X2-vs-CS13-TOFF102-CSd13-TOFF102
  q56 : Eqn
  q56 = eqn (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SK-e≡-1⟩-2

-- pass [CS13 TOFF102 CSd13 TOFF102] [X2 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2]: 7 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 : ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-X2-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2 = derive (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ []) (X2 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ [])
  (rw 4 q50 ∷
   rw⁻ 0 q51 ∷
   rw⁻ 3 q52 ∷
   rw 6 q53 ∷
   rw⁻ 12 q54 ∷
   rw⁻ 15 q55 ∷
   rw⁻ 0 q56 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = eqn (CK32⁻ ∷ X3 ∷ []) (X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (wn 1674 W)
  q58 : Eqn
  q58 = eqn (X3 ∷ CK32⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd32-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0)
  q59 : Eqn
  q59 = eqn (X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ []) (X3 ∷ CK32⁻ ∷ []) (wn 1675 W)

-- pass [CKd32] [X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X3]: 3 steps
lem-pass-CKd32-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : ⟪ (CK32⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK32⁻ ∷ []) ⟫ʷ
lem-pass-CKd32-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = derive (CK32⁻ ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK32⁻ ∷ [])
  (rw 0 q57 ∷
   rw 1 q58 ∷
   rw 13 q59 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = eqn (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) (X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3)
  q61 : Eqn
  q61 = eqn (CCZ123 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ []) (X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ CCZ123 ∷ []) (lem-CCZ⟨312⟩-passes-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩)
  q62 : Eqn
  q62 = eqn (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) (X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ CS03 ∷ X3 ∷ []) lem-ca-split-Gad⟨t≡0-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩-3

-- pass [CCZ123] [X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X3]: 3 steps
lem-pass-CCZ123-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : ⟪ (CCZ123 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = derive (CCZ123 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CCZ123 ∷ [])
  (rw 1 q60 ∷
   rw 0 q61 ∷
   rw⁻ 0 q62 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = eqn (CK32 ∷ X3 ∷ []) (X3 ∷ X3 ∷ CK32 ∷ X3 ∷ []) (wn 1409 W)
  q64 : Eqn
  q64 = eqn (X3 ∷ CK32 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK32 ∷ X3 ∷ []) (lem-pass-X3-CK32-X3-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0)
  q65 : Eqn
  q65 = eqn (X3 ∷ CK32 ∷ X3 ∷ X3 ∷ []) (X3 ∷ CK32 ∷ []) (wn 1410 W)

-- pass [CK32] [X3 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X3]: 3 steps
lem-pass-CK32-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 : ⟪ (CK32 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK32 ∷ []) ⟫ʷ
lem-pass-CK32-vs-X3-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X3 = derive (CK32 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X3 ∷ CK32 ∷ [])
  (rw 0 q63 ∷
   rw 1 q64 ∷
   rw 13 q65 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = eqn (S0⁻ ∷ X2 ∷ []) (X2 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑)))
  q67 : Eqn
  q67 = eqn (K0⁻ ∷ X2 ∷ []) (X2 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((X ↑)))
  q68 : Eqn
  q68 = eqn (S0 ∷ X2 ∷ []) (X2 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑)))
  q69 : Eqn
  q69 = eqn (K0 ∷ X2 ∷ []) (X2 ∷ K0 ∷ []) (low₁-comm (K) ((X ↑)))
  q70 : Eqn
  q70 = eqn (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ []) (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02 ∷ CS02 ∷ []) (wn 2239 W)
  q71 : Eqn
  q71 = eqn (S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (CS02⁻ ∷ CS02⁻ ∷ CK20 ∷ CS02 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 2240 W)
  q72 : Eqn
  q72 = eqn (CS02 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02 ∷ []) (lem-pass-CS20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2)
  q73 : Eqn
  q73 = eqn (CK20⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CK20⁻ ∷ []) (lem-pass-CKd20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2)
  q74 : Eqn
  q74 = eqn (CS02⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS02⁻ ∷ []) (lem-pass-CSd20-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2)
  q75 : Eqn
  q75 = eqn (CS02⁻ ∷ CK20⁻ ∷ CS02 ∷ CS02 ∷ CS02⁻ ∷ CS02⁻ ∷ CK20 ∷ CS02 ∷ []) [] (wn 2241 W)

-- ca-split Gad(t=0, W=(2,), d=SdKdSS, e=-1) 2: 15 steps
lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩-2 : ⟪ (X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
lem-ca-split-Gad⟨t≡0-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩-2 = derive (X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ []) (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ CK20 ∷ X2 ∷ X2 ∷ CS02 ∷ X2 ∷ [])
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
  q76 = eqn (CK20⁻ ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1464 W)
  q77 : Eqn
  q77 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ []) (S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-Sd0-CS03-TOFF012-CSd03-TOFF012-S0)
  q78 : Eqn
  q78 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK20⁻ ∷ []) (wn 1465 W)

-- pass [CKd20] [X2 Sd0 CS03 TOFF012 CSd03 TOFF012 S0 X2]: 3 steps
lem-pass-CKd20-vs-X2-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2 : ⟪ (CK20⁻ ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ CK20⁻ ∷ []) ⟫ʷ
lem-pass-CKd20-vs-X2-Sd0-CS03-TOFF012-CSd03-TOFF012-S0-X2 = derive (CK20⁻ ∷ X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ []) (X2 ∷ S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ X2 ∷ CK20⁻ ∷ [])
  (rw 0 q76 ∷
   rw 1 q77 ∷
   rw 7 q78 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = eqn (CK23⁻ ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (wn 2301 W)
  q80 : Eqn
  q80 = eqn (X2 ∷ CK23⁻ ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK23⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd23-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0)
  q81 : Eqn
  q81 = eqn (X2 ∷ CK23⁻ ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK23⁻ ∷ []) (wn 2302 W)

-- pass [CKd23] [X2 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2]: 3 steps
lem-pass-CKd23-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 : ⟪ (CK23⁻ ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK23⁻ ∷ []) ⟫ʷ
lem-pass-CKd23-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 = derive (CK23⁻ ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ []) (X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK23⁻ ∷ [])
  (rw 0 q79 ∷
   rw 1 q80 ∷
   rw 13 q81 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = eqn (CK23 ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK23 ∷ X2 ∷ []) (wn 2303 W)
  q83 : Eqn
  q83 = eqn (X2 ∷ CK23 ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ []) (S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK23 ∷ X2 ∷ []) (lem-pass-X2-CK23-X2-vs-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0)
  q84 : Eqn
  q84 = eqn (X2 ∷ CK23 ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK23 ∷ []) (wn 2304 W)

-- pass [CK23] [X2 Sd0 Kd0 S0 S0 CS03 TOFF012 CSd03 TOFF012 Sd0 Sd0 K0 S0 X2]: 3 steps
lem-pass-CK23-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 : ⟪ (CK23 ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK23 ∷ []) ⟫ʷ
lem-pass-CK23-vs-X2-Sd0-Kd0-S0-S0-CS03-TOFF012-CSd03-TOFF012-Sd0-Sd0-K0-S0-X2 = derive (CK23 ∷ X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ []) (X2 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ CK23 ∷ [])
  (rw 0 q82 ∷
   rw 1 q83 ∷
   rw 13 q84 ∷ []) Eq.refl
