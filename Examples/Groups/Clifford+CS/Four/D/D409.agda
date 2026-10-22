{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D409 (W : Ws) where

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

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q3 : Eqn
  q3 = wE 7 W
  q4 : Eqn
  q4 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q5 : Eqn
  q5 = wE 140 W
  q6 : Eqn
  q6 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q8 : Eqn
  q8 = wE 1148 W
  q9 : Eqn
  q9 = wE 27 W
  q10 : Eqn
  q10 = wE 142 W
  q11 : Eqn
  q11 = wE 31 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X2 CS02 X2]: 247 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS02-X2 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CS02-X2 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (X2 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (rw 34 q1 ∷
   rw⁻ 33 q2 ∷
   rw 32 q3 ∷
   rw⁻ 31 q2 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q4 ∷
   rw 31 q3 ∷
   rw⁻ 30 q4 ∷
   re 31 3 (CS13 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q4 ∷
   rw 30 q3 ∷
   rw⁻ 29 q4 ∷
   re 30 3 (CS13 ∷ []) ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q4 ∷
   rw 29 q5 ∷
   rw⁻ 28 q4 ∷
   re 29 3 (CK31 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q4 ∷
   rw 28 q3 ∷
   rw⁻ 27 q4 ∷
   re 28 3 (CS13 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q4 ∷
   rw 27 q3 ∷
   rw⁻ 26 q4 ∷
   re 27 3 (CS13 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q4 ∷
   rw 26 q3 ∷
   rw⁻ 25 q4 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw⁻ 24 q6 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q4 ∷
   rw 24 q3 ∷
   rw⁻ 23 q4 ∷
   re 24 3 (CS13 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q4 ∷
   rw 23 q3 ∷
   rw⁻ 22 q4 ∷
   re 23 3 (CS13 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q4 ∷
   rw 22 q3 ∷
   rw⁻ 21 q4 ∷
   re 22 3 (CS13 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q4 ∷
   rw 21 q3 ∷
   rw⁻ 20 q4 ∷
   re 21 3 (CS13 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q4 ∷
   rw 20 q3 ∷
   rw⁻ 19 q4 ∷
   re 20 3 (CS13 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q4 ∷
   rw 19 q3 ∷
   rw⁻ 18 q4 ∷
   re 19 3 (CS13 ∷ []) ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q4 ∷
   rw 18 q3 ∷
   rw⁻ 17 q4 ∷
   re 18 3 (CS13 ∷ []) ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q4 ∷
   rw 17 q3 ∷
   rw⁻ 16 q4 ∷
   re 17 3 (CS13 ∷ []) ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q4 ∷
   rw 16 q3 ∷
   rw⁻ 15 q4 ∷
   re 16 3 (CS13 ∷ []) ∷
   rw⁻ 14 q7 ∷
   re 13 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q4 ∷
   rw 14 q5 ∷
   rw⁻ 13 q4 ∷
   re 14 3 (CK31 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q4 ∷
   rw 13 q3 ∷
   rw⁻ 12 q4 ∷
   re 13 3 (CS13 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q4 ∷
   rw 12 q3 ∷
   rw⁻ 11 q4 ∷
   re 12 3 (CS13 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q4 ∷
   rw 11 q3 ∷
   rw⁻ 10 q4 ∷
   re 11 3 (CS13 ∷ []) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q4 ∷
   rw 10 q3 ∷
   rw⁻ 9 q4 ∷
   re 10 3 (CS13 ∷ []) ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q4 ∷
   rw 9 q3 ∷
   rw⁻ 8 q4 ∷
   re 9 3 (CS13 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q4 ∷
   rw 8 q3 ∷
   rw⁻ 7 q4 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 6 q6 ∷
   rw 5 q3 ∷
   rw 4 q3 ∷
   rw 3 q5 ∷
   rw 2 q3 ∷
   rw 1 q3 ∷
   rw 0 q3 ∷
   rw 1 q8 ∷
   rw 0 q2 ∷
   rw 1 q9 ∷
   rw 2 q2 ∷
   rw 3 q9 ∷
   rw 4 q9 ∷
   rw 5 q9 ∷
   rw 6 q10 ∷
   rw 7 q9 ∷
   rw 8 q9 ∷
   rw 9 q6 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q4 ∷
   rw 11 q9 ∷
   rw 12 q4 ∷
   re 10 3 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q4 ∷
   rw 12 q9 ∷
   rw 13 q4 ∷
   re 11 3 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q4 ∷
   rw 13 q9 ∷
   rw 14 q4 ∷
   re 12 3 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q4 ∷
   rw 14 q9 ∷
   rw 15 q4 ∷
   re 13 3 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q4 ∷
   rw 15 q9 ∷
   rw 16 q4 ∷
   re 14 3 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q4 ∷
   rw 16 q9 ∷
   rw 17 q4 ∷
   re 15 3 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 16 q4 ∷
   rw 17 q10 ∷
   rw 18 q4 ∷
   re 16 3 (CK30 ∷ []) ∷
   rw 17 q7 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q4 ∷
   rw 19 q9 ∷
   rw 20 q4 ∷
   re 18 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q4 ∷
   rw 20 q9 ∷
   rw 21 q4 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q4 ∷
   rw 21 q9 ∷
   rw 22 q4 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q4 ∷
   rw 22 q9 ∷
   rw 23 q4 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q4 ∷
   rw 23 q9 ∷
   rw 24 q4 ∷
   re 22 3 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q4 ∷
   rw 24 q9 ∷
   rw 25 q4 ∷
   re 23 3 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q4 ∷
   rw 25 q9 ∷
   rw 26 q4 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q4 ∷
   rw 26 q9 ∷
   rw 27 q4 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q4 ∷
   rw 27 q9 ∷
   rw 28 q4 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 27 q6 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q4 ∷
   rw 29 q9 ∷
   rw 30 q4 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q4 ∷
   rw 30 q9 ∷
   rw 31 q4 ∷
   re 29 3 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q4 ∷
   rw 31 q9 ∷
   rw 32 q4 ∷
   re 30 3 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 31 q4 ∷
   rw 32 q10 ∷
   rw 33 q4 ∷
   re 31 3 (CK30 ∷ []) ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q4 ∷
   rw 33 q9 ∷
   rw 34 q4 ∷
   re 32 3 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q4 ∷
   rw 34 q9 ∷
   rw 35 q4 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 34 q11 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q13 : Eqn
  q13 = eqn (S0 ∷ X2 ∷ []) (X2 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑)))
  q14 : Eqn
  q14 = eqn (K0 ∷ X3 ∷ []) (X3 ∷ K0 ∷ []) (low₁-comm (K) ((X ↑ ↑)))
  q15 : Eqn
  q15 = eqn (K0 ∷ X2 ∷ []) (X2 ∷ K0 ∷ []) (low₁-comm (K) ((X ↑)))
  q16 : Eqn
  q16 = wE 391 W
  q17 : Eqn
  q17 = eqn (K0⁻ ∷ X2 ∷ []) (X2 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((X ↑)))
  q18 : Eqn
  q18 = eqn (S0⁻ ∷ X2 ∷ []) (X2 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑)))
  q19 : Eqn
  q19 = eqn (K0⁻ ∷ X3 ∷ []) (X3 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((X ↑ ↑)))
  q20 : Eqn
  q20 = eqn (S0⁻ ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑ ↑)))
  q21 : Eqn
  q21 = eqn (X0 ∷ X3 ∷ []) (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑)))
  q22 : Eqn
  q22 = eqn (X0 ∷ X2 ∷ []) (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑)))
  q23 : Eqn
  q23 = wE 392 W

-- xconj [0] Gad(t=0, W=(2, 3), d=SK, e=-1): 16 steps
lem-xconj-0-Gad⟨t≡0-W≡⟨2-3⟩-d≡SK-e≡-1⟩ : ⟪ (X0 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xconj-0-Gad⟨t≡0-W≡⟨2-3⟩-d≡SK-e≡-1⟩ = derive (X0 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ X0 ∷ []) (X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 2 q12 ∷
   rw⁻ 1 q13 ∷
   rw⁻ 3 q14 ∷
   rw⁻ 2 q15 ∷
   rw 0 q16 ∷
   rw 3 q13 ∷
   rw 2 q13 ∷
   rw 1 q17 ∷
   rw 0 q18 ∷
   rw 4 q12 ∷
   rw 3 q12 ∷
   rw 2 q19 ∷
   rw 1 q20 ∷
   rw⁻ 13 q21 ∷
   rw⁻ 12 q22 ∷
   rw 10 q23 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = wE 1145 W
  q25 : Eqn
  q25 = wE 1146 W

-- xconj [0] Gad(t=0, W=(2, 3), d=SdKdSS, e=-1): 16 steps
lem-xconj-0-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (X0 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xconj-0-Gad⟨t≡0-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ = derive (X0 ∷ X2 ∷ X3 ∷ S0⁻ ∷ K0⁻ ∷ S0 ∷ S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ S0⁻ ∷ K0 ∷ S0 ∷ X2 ∷ X3 ∷ X0 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 2 q20 ∷
   rw⁻ 1 q18 ∷
   rw⁻ 3 q19 ∷
   rw⁻ 2 q17 ∷
   rw⁻ 4 q12 ∷
   rw⁻ 3 q13 ∷
   rw⁻ 5 q12 ∷
   rw⁻ 4 q13 ∷
   rw 0 q24 ∷
   rw 1 q15 ∷
   rw 0 q13 ∷
   rw 2 q14 ∷
   rw 1 q12 ∷
   rw⁻ 13 q21 ∷
   rw⁻ 12 q22 ∷
   rw 8 q25 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = eqn (S1⁻ ∷ X3 ∷ []) (X3 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) ((X ↑)))
  q27 : Eqn
  q27 = eqn (K1⁻ ∷ X3 ∷ []) (X3 ∷ K1⁻ ∷ []) (low-comm (((K • iI) ↑)) ((X ↑)))
  q28 : Eqn
  q28 = eqn (S1 ∷ X3 ∷ []) (X3 ∷ S1 ∷ []) (low-comm ((S ↑)) ((X ↑)))
  q29 : Eqn
  q29 = eqn (X0 ∷ S1 ∷ []) (S1 ∷ X0 ∷ []) (low₁-comm (X) (S))
  q30 : Eqn
  q30 = eqn (X0 ∷ K1 ∷ []) (K1 ∷ X0 ∷ []) (low₁-comm (X) (K))
  q31 : Eqn
  q31 = eqn (X0 ∷ S1⁻ ∷ []) (S1⁻ ∷ X0 ∷ []) (low₁-comm (X) ((S • S • S)))

-- xconj [0] Gad(t=1, W=(3,), d=SdKdSS, e=-1): 17 steps
lem-xconj-0-Gad⟨t≡1-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ []) ⟫ʷ
lem-xconj-0-Gad⟨t≡1-W≡⟨3⟩-d≡SdKdSS-e≡-1⟩ = derive (X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X0 ∷ []) (X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ [])
  (rw⁻ 1 q26 ∷
   rw⁻ 2 q27 ∷
   rw⁻ 3 q28 ∷
   rw⁻ 4 q28 ∷
   rw 4 q28 ∷
   rw 3 q28 ∷
   rw 2 q27 ∷
   rw 1 q26 ∷
   rw⁻ 14 q21 ∷
   rw⁻ 13 q29 ∷
   rw⁻ 12 q30 ∷
   rw⁻ 11 q31 ∷
   rw⁻ 10 q31 ∷
   rw 10 q31 ∷
   rw 11 q31 ∷
   rw 12 q30 ∷
   rw 13 q29 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = wE 387 W

-- xconj [0] Gad(t=1, W=(0, 3), d=SdKdSS, e=-1): 19 steps
lem-xconj-0-Gad⟨t≡1-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (X0 ∷ X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ []) ⟫ʷ
lem-xconj-0-Gad⟨t≡1-W≡⟨0-3⟩-d≡SdKdSS-e≡-1⟩ = derive (X0 ∷ X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ X0 ∷ []) (X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ [])
  (rw⁻ 2 q26 ∷
   rw⁻ 3 q27 ∷
   rw⁻ 4 q28 ∷
   rw⁻ 5 q28 ∷
   rw 0 q32 ∷
   rw 3 q28 ∷
   rw 2 q28 ∷
   rw 1 q27 ∷
   rw 0 q26 ∷
   rw⁻ 12 q29 ∷
   rw⁻ 11 q30 ∷
   rw⁻ 10 q31 ∷
   rw⁻ 9 q31 ∷
   rw⁻ 14 q21 ∷
   rw⁻ 13 q29 ∷
   rw⁻ 12 q30 ∷
   rw⁻ 11 q31 ∷
   rw⁻ 10 q31 ∷
   rw 9 q32 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = eqn (S1⁻ ∷ X2 ∷ []) (X2 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (X))
  q34 : Eqn
  q34 = eqn (K1⁻ ∷ X2 ∷ []) (X2 ∷ K1⁻ ∷ []) (low-comm (((K • iI) ↑)) (X))
  q35 : Eqn
  q35 = eqn (S1 ∷ X2 ∷ []) (X2 ∷ S1 ∷ []) (low-comm ((S ↑)) (X))

-- xconj [0] Gad(t=1, W=(2,), d=SdKdSS, e=-1): 17 steps
lem-xconj-0-Gad⟨t≡1-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (X0 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ []) ⟫ʷ
lem-xconj-0-Gad⟨t≡1-W≡⟨2⟩-d≡SdKdSS-e≡-1⟩ = derive (X0 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X0 ∷ []) (X0 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ [])
  (rw⁻ 1 q33 ∷
   rw⁻ 2 q34 ∷
   rw⁻ 3 q35 ∷
   rw⁻ 4 q35 ∷
   rw 4 q35 ∷
   rw 3 q35 ∷
   rw 2 q34 ∷
   rw 1 q33 ∷
   rw⁻ 14 q22 ∷
   rw⁻ 13 q29 ∷
   rw⁻ 12 q30 ∷
   rw⁻ 11 q31 ∷
   rw⁻ 10 q31 ∷
   rw 10 q31 ∷
   rw 11 q31 ∷
   rw 12 q30 ∷
   rw 13 q29 ∷ []) Eq.refl

-- xconj [0] Gad(t=1, W=(0, 2), d=SdKdSS, e=-1): 19 steps
lem-xconj-0-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (X0 ∷ X0 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ []) ⟫ʷ
lem-xconj-0-Gad⟨t≡1-W≡⟨0-2⟩-d≡SdKdSS-e≡-1⟩ = derive (X0 ∷ X0 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X0 ∷ []) (X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ [])
  (rw⁻ 2 q33 ∷
   rw⁻ 3 q34 ∷
   rw⁻ 4 q35 ∷
   rw⁻ 5 q35 ∷
   rw 0 q32 ∷
   rw 3 q35 ∷
   rw 2 q35 ∷
   rw 1 q34 ∷
   rw 0 q33 ∷
   rw⁻ 12 q29 ∷
   rw⁻ 11 q30 ∷
   rw⁻ 10 q31 ∷
   rw⁻ 9 q31 ∷
   rw⁻ 14 q22 ∷
   rw⁻ 13 q29 ∷
   rw⁻ 12 q30 ∷
   rw⁻ 11 q31 ∷
   rw⁻ 10 q31 ∷
   rw 9 q32 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = wE 1149 W
  q37 : Eqn
  q37 = eqn (X0 ∷ CS13 ∷ []) (CS13 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))
  q38 : Eqn
  q38 = wE 257 W
  q39 : Eqn
  q39 = wE 389 W
  q40 : Eqn
  q40 = eqn (X0 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑ • (CS • CS • CS) • Swap ↑)))
  q41 : Eqn
  q41 = wE 258 W

-- distribute Gad(t=1, W=(0, 2), d=1, e=-1) CS13 TOFF102 CSd13 TOFF102: 13 steps
lem-distribute-Gad⟨t≡1-W≡⟨0-2⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ []) ⟫ʷ
lem-distribute-Gad⟨t≡1-W≡⟨0-2⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102 = derive (X0 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X2 ∷ []) (CS13 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ [])
  (rw 3 q36 ∷
   rw 8 q36 ∷
   rw 13 q36 ∷
   rw 0 q22 ∷
   rw 1 q37 ∷
   rw 2 q32 ∷
   rw 0 q38 ∷
   rw 1 q39 ∷
   rw 6 q22 ∷
   rw 7 q40 ∷
   rw 8 q32 ∷
   rw 6 q41 ∷
   rw 7 q39 ∷ []) Eq.refl

-- xconj [0] Gad(t=1, W=(2, 3), d=SdKdSS, e=-1): 26 steps
lem-xconj-0-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xconj-0-Gad⟨t≡1-W≡⟨2-3⟩-d≡SdKdSS-e≡-1⟩ = derive (X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ X0 ∷ []) (X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 2 q26 ∷
   rw⁻ 1 q33 ∷
   rw⁻ 3 q27 ∷
   rw⁻ 2 q34 ∷
   rw⁻ 4 q28 ∷
   rw⁻ 3 q35 ∷
   rw⁻ 5 q28 ∷
   rw⁻ 4 q35 ∷
   rw 4 q35 ∷
   rw 3 q35 ∷
   rw 2 q34 ∷
   rw 1 q33 ∷
   rw 5 q28 ∷
   rw 4 q28 ∷
   rw 3 q27 ∷
   rw 2 q26 ∷
   rw⁻ 16 q21 ∷
   rw⁻ 15 q22 ∷
   rw⁻ 14 q29 ∷
   rw⁻ 13 q30 ∷
   rw⁻ 12 q31 ∷
   rw⁻ 11 q31 ∷
   rw 11 q31 ∷
   rw 12 q31 ∷
   rw 13 q30 ∷
   rw 14 q29 ∷ []) Eq.refl

-- xconj [0] Gad(t=1, W=(0, 2, 3), d=SdKdSS, e=-1): 28 steps
lem-xconj-0-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ : ⟪ (X0 ∷ X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-xconj-0-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡SdKdSS-e≡-1⟩ = derive (X0 ∷ X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ X0 ∷ []) (X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ [])
  (rw⁻ 3 q26 ∷
   rw⁻ 2 q33 ∷
   rw⁻ 4 q27 ∷
   rw⁻ 3 q34 ∷
   rw⁻ 5 q28 ∷
   rw⁻ 4 q35 ∷
   rw⁻ 6 q28 ∷
   rw⁻ 5 q35 ∷
   rw 0 q32 ∷
   rw 3 q35 ∷
   rw 2 q35 ∷
   rw 1 q34 ∷
   rw 0 q33 ∷
   rw 4 q28 ∷
   rw 3 q28 ∷
   rw 2 q27 ∷
   rw 1 q26 ∷
   rw⁻ 13 q29 ∷
   rw⁻ 12 q30 ∷
   rw⁻ 11 q31 ∷
   rw⁻ 10 q31 ∷
   rw⁻ 16 q21 ∷
   rw⁻ 15 q22 ∷
   rw⁻ 14 q29 ∷
   rw⁻ 13 q30 ∷
   rw⁻ 12 q31 ∷
   rw⁻ 11 q31 ∷
   rw 10 q32 ∷ []) Eq.refl
