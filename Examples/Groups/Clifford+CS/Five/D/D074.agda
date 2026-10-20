{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D074 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F4-I-I ; lem-F4-I-S2 ; lem-F4-I-S3 ; lem-F4-K3-I ; lem-F4-K3-S2 ; lem-F4-K3-S3 ; lem-F4-S2-I ; lem-F4-S2-S2 ; lem-F4-S2-S3)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F4-I-K3-at132132 ; lem-F4-I-S2-at132132 ; lem-F4-K3-K3-at132132 ; lem-F4-S2-I-at132132 ; lem-F4-S2-K3-at132132 ; lem-F4-S2-S2-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-F4-CS2-I ; lem-F4-CS2-S2 ; lem-F4-CS2-S3)
open import Examples.Groups.Clifford+CS.Five.D.D022 using (lem-F4-CS2-CS2-at132132 ; lem-F4-I-CS2-at132132 ; lem-F4-S2-CS2-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D032 using (lem-F5-23-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D047 using (lem-F4-CS2-K3-at132132 ; lem-F4-K3-CS2-at132132)
open import Examples.Groups.Clifford+CS.Five.D.D048 using (lem-deb-AD-split-a ; lem-deb-AD-split-b)
open import Examples.Groups.Clifford+CS.Five.D.D049 using (lem-deb-CKS-split-a)
open import Examples.Groups.Clifford+CS.Five.D.D050 using (lem-deb-CKS-split-b)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CS12 ∷ []) (lem-F5-23-at132132 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (K2 ∷ []) (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (wl 1409 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K3-CS2-at132132 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-K3-at132132 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS2-CS2-at132132 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (X4 ∷ CK42 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-F4-K3-K3-at132132 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (S1 ∷ []) (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (wl 1412 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S2-CS2-at132132 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S2-K3-at132132 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S2-S2-at132132 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (ι ∷ []) (wl 1411 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2-at132132 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2-at132132 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K3-at132132 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lem-F4-S2-I-at132132 c4)

-- deb-Q-lo-split-a @132132: 55 steps
lem-deb-Q-lo-split-a-at132132 : Ws → ⟪ (CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ []) ⟫ʷ
lem-deb-Q-lo-split-a-at132132 c4 = derive (CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ S1 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS14 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 4 (q2 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 12 (q2 c4) ∷
   rw⁻ 11 (q3 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 15 (q4 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   rw⁻ 13 (q4 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   rw 20 (q7 c4) ∷
   rw⁻ 19 (q8 c4) ∷
   rw⁻ 18 (q9 c4) ∷
   rw⁻ 17 (q8 c4) ∷
   rw⁻ 16 (q9 c4) ∷
   rw⁻ 15 (q8 c4) ∷
   rw 24 (q7 c4) ∷
   rw⁻ 23 (q10 c4) ∷
   rw⁻ 22 (q8 c4) ∷
   rw⁻ 21 (q9 c4) ∷
   rw⁻ 20 (q8 c4) ∷
   rw⁻ 19 (q9 c4) ∷
   rw⁻ 18 (q8 c4) ∷
   rw 28 (q7 c4) ∷
   rw⁻ 27 (q10 c4) ∷
   rw⁻ 26 (q10 c4) ∷
   rw⁻ 25 (q8 c4) ∷
   rw⁻ 24 (q9 c4) ∷
   rw⁻ 23 (q8 c4) ∷
   rw⁻ 22 (q9 c4) ∷
   rw⁻ 21 (q8 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw⁻ 31 (q12 c4) ∷
   rw⁻ 30 (q12 c4) ∷
   rw⁻ 29 (q12 c4) ∷
   rw⁻ 28 (q13 c4) ∷
   rw⁻ 27 (q14 c4) ∷
   rw⁻ 26 (q13 c4) ∷
   rw⁻ 25 (q14 c4) ∷
   rw⁻ 24 (q13 c4) ∷
   rw 36 (q7 c4) ∷
   rw⁻ 35 (q15 c4) ∷
   rw⁻ 34 (q10 c4) ∷
   rw⁻ 33 (q10 c4) ∷
   rw⁻ 32 (q10 c4) ∷
   rw⁻ 31 (q8 c4) ∷
   rw⁻ 30 (q9 c4) ∷
   rw⁻ 29 (q8 c4) ∷
   rw⁻ 28 (q9 c4) ∷
   rw⁻ 27 (q8 c4) ∷ []) Eq.refl

-- deb-Q-lo-split-b @132132: 45 steps
lem-deb-Q-lo-split-b-at132132 : Ws → ⟪ (CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ []) ⟫ʷ
lem-deb-Q-lo-split-b-at132132 c4 = derive (CS12 ∷ K2 ∷ CS12 ∷ K2 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ ι ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ CS14 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 4 (q2 c4) ∷
   rw⁻ 3 (q3 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 12 (q2 c4) ∷
   rw⁻ 11 (q3 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   rw⁻ 9 (q3 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 15 (q4 c4) ∷
   rw⁻ 14 (q5 c4) ∷
   rw⁻ 13 (q4 c4) ∷
   rw⁻ 12 (q5 c4) ∷
   rw 20 (q7 c4) ∷
   rw⁻ 19 (q8 c4) ∷
   rw⁻ 18 (q9 c4) ∷
   rw⁻ 17 (q8 c4) ∷
   rw⁻ 16 (q9 c4) ∷
   rw⁻ 15 (q8 c4) ∷
   rw 24 (q7 c4) ∷
   rw⁻ 23 (q10 c4) ∷
   rw⁻ 22 (q8 c4) ∷
   rw⁻ 21 (q9 c4) ∷
   rw⁻ 20 (q8 c4) ∷
   rw⁻ 19 (q9 c4) ∷
   rw⁻ 18 (q8 c4) ∷
   rw 28 (q7 c4) ∷
   rw⁻ 27 (q10 c4) ∷
   rw⁻ 26 (q10 c4) ∷
   rw⁻ 25 (q8 c4) ∷
   rw⁻ 24 (q9 c4) ∷
   rw⁻ 23 (q8 c4) ∷
   rw⁻ 22 (q9 c4) ∷
   rw⁻ 21 (q8 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw⁻ 31 (q12 c4) ∷
   rw⁻ 30 (q12 c4) ∷
   rw⁻ 29 (q12 c4) ∷
   rw⁻ 28 (q13 c4) ∷
   rw⁻ 27 (q14 c4) ∷
   rw⁻ 26 (q13 c4) ∷
   rw⁻ 25 (q14 c4) ∷
   rw⁻ 24 (q13 c4) ∷ []) Eq.refl

private
  q16 : Ws → Eqn
  q16 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S3 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S3 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2-S3 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-S3 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ []) (lem-deb-AD-split-a c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) (lem-deb-AD-split-b c4)

-- deb-AD part1: 35 steps
lem-deb-AD-part1 : Ws → ⟪ (CK43 ∷ CS34 ∷ CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CS34 ∷ CCZ234 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) ⟫ʷ
lem-deb-AD-part1 c4 = derive (CK43 ∷ CS34 ∷ CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) (CK43 ∷ CS34 ∷ CCZ234 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS34 ∷ CS34 ∷ CS34 ∷ [])
  (rw 103 (q16 c4) ∷
   rw 100 (q16 c4) ∷
   rw 97 (q17 c4) ∷
   rw 94 (q18 c4) ∷
   rw 91 (q18 c4) ∷
   rw 88 (q18 c4) ∷
   rw 85 (q16 c4) ∷
   rw 82 (q19 c4) ∷
   rw 79 (q16 c4) ∷
   rw 76 (q19 c4) ∷
   rw 73 (q16 c4) ∷
   rw 104 (q16 c4) ∷
   rw 101 (q16 c4) ∷
   rw 98 (q17 c4) ∷
   rw 95 (q18 c4) ∷
   rw 92 (q18 c4) ∷
   rw 89 (q18 c4) ∷
   rw 86 (q16 c4) ∷
   rw 83 (q19 c4) ∷
   rw 80 (q16 c4) ∷
   rw 77 (q19 c4) ∷
   rw 74 (q16 c4) ∷
   rw 105 (q16 c4) ∷
   rw 102 (q16 c4) ∷
   rw 99 (q17 c4) ∷
   rw 96 (q18 c4) ∷
   rw 93 (q18 c4) ∷
   rw 90 (q18 c4) ∷
   rw 87 (q16 c4) ∷
   rw 84 (q19 c4) ∷
   rw 81 (q16 c4) ∷
   rw 78 (q19 c4) ∷
   rw 75 (q16 c4) ∷
   rw⁻ 3 (q20 c4) ∷
   rw⁻ 28 (q21 c4) ∷ []) Eq.refl

private
  q22 : Ws → Eqn
  q22 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2-S2 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-S2 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-S2 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-S2 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-I c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2-I c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) (lem-F4-CS2-I c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (X4 ∷ CK43 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK43 ∷ X4 ∷ []) (lem-F4-K3-I c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ []) (lem-deb-CKS-split-a c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ []) (lem-deb-CKS-split-b c4)

-- deb-CKS part2: 151 steps
lem-deb-CKS-part2 : Ws → ⟪ (CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS34 ∷ []) ⟫ʷ
lem-deb-CKS-part2 c4 = derive (CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ []) (CCZ234 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ CS34 ∷ CS34 ∷ CS34 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS34 ∷ [])
  (rw 133 (q22 c4) ∷
   rw 130 (q23 c4) ∷
   rw 127 (q24 c4) ∷
   rw 124 (q23 c4) ∷
   rw 121 (q24 c4) ∷
   rw 118 (q23 c4) ∷
   rw 115 (q23 c4) ∷
   rw 112 (q25 c4) ∷
   rw 109 (q22 c4) ∷
   rw 106 (q22 c4) ∷
   rw 103 (q22 c4) ∷
   rw 100 (q23 c4) ∷
   rw 97 (q24 c4) ∷
   rw 94 (q23 c4) ∷
   rw 91 (q24 c4) ∷
   rw 88 (q23 c4) ∷
   rw 143 (q25 c4) ∷
   rw 140 (q22 c4) ∷
   rw 137 (q22 c4) ∷
   rw 134 (q22 c4) ∷
   rw 131 (q23 c4) ∷
   rw 128 (q24 c4) ∷
   rw 125 (q23 c4) ∷
   rw 122 (q24 c4) ∷
   rw 119 (q23 c4) ∷
   rw 116 (q23 c4) ∷
   rw 113 (q25 c4) ∷
   rw 110 (q22 c4) ∷
   rw 107 (q22 c4) ∷
   rw 104 (q22 c4) ∷
   rw 101 (q23 c4) ∷
   rw 98 (q24 c4) ∷
   rw 95 (q23 c4) ∷
   rw 92 (q24 c4) ∷
   rw 89 (q23 c4) ∷
   rw 144 (q25 c4) ∷
   rw 141 (q22 c4) ∷
   rw 138 (q22 c4) ∷
   rw 135 (q22 c4) ∷
   rw 132 (q23 c4) ∷
   rw 129 (q24 c4) ∷
   rw 126 (q23 c4) ∷
   rw 123 (q24 c4) ∷
   rw 120 (q23 c4) ∷
   rw 117 (q23 c4) ∷
   rw 114 (q25 c4) ∷
   rw 111 (q22 c4) ∷
   rw 108 (q22 c4) ∷
   rw 105 (q22 c4) ∷
   rw 102 (q23 c4) ∷
   rw 99 (q24 c4) ∷
   rw 96 (q23 c4) ∷
   rw 93 (q24 c4) ∷
   rw 90 (q23 c4) ∷
   rw 145 (q26 c4) ∷
   rw 142 (q27 c4) ∷
   rw 139 (q27 c4) ∷
   rw 136 (q27 c4) ∷
   rw 133 (q28 c4) ∷
   rw 130 (q29 c4) ∷
   rw 127 (q28 c4) ∷
   rw 124 (q29 c4) ∷
   rw 121 (q28 c4) ∷
   rw 118 (q28 c4) ∷
   rw 115 (q26 c4) ∷
   rw 112 (q27 c4) ∷
   rw 109 (q27 c4) ∷
   rw 106 (q27 c4) ∷
   rw 103 (q28 c4) ∷
   rw 100 (q29 c4) ∷
   rw 97 (q28 c4) ∷
   rw 94 (q29 c4) ∷
   rw 91 (q28 c4) ∷
   rw 146 (q25 c4) ∷
   rw 143 (q22 c4) ∷
   rw 140 (q22 c4) ∷
   rw 137 (q22 c4) ∷
   rw 134 (q23 c4) ∷
   rw 131 (q24 c4) ∷
   rw 128 (q23 c4) ∷
   rw 125 (q24 c4) ∷
   rw 122 (q23 c4) ∷
   rw 119 (q23 c4) ∷
   rw 116 (q25 c4) ∷
   rw 113 (q22 c4) ∷
   rw 110 (q22 c4) ∷
   rw 107 (q22 c4) ∷
   rw 104 (q23 c4) ∷
   rw 101 (q24 c4) ∷
   rw 98 (q23 c4) ∷
   rw 95 (q24 c4) ∷
   rw 92 (q23 c4) ∷
   rw 147 (q17 c4) ∷
   rw 144 (q18 c4) ∷
   rw 141 (q18 c4) ∷
   rw 138 (q18 c4) ∷
   rw 135 (q16 c4) ∷
   rw 132 (q19 c4) ∷
   rw 129 (q16 c4) ∷
   rw 126 (q19 c4) ∷
   rw 123 (q16 c4) ∷
   rw 120 (q16 c4) ∷
   rw 117 (q17 c4) ∷
   rw 114 (q18 c4) ∷
   rw 111 (q18 c4) ∷
   rw 108 (q18 c4) ∷
   rw 105 (q16 c4) ∷
   rw 102 (q19 c4) ∷
   rw 99 (q16 c4) ∷
   rw 96 (q19 c4) ∷
   rw 93 (q16 c4) ∷
   rw 148 (q17 c4) ∷
   rw 145 (q18 c4) ∷
   rw 142 (q18 c4) ∷
   rw 139 (q18 c4) ∷
   rw 136 (q16 c4) ∷
   rw 133 (q19 c4) ∷
   rw 130 (q16 c4) ∷
   rw 127 (q19 c4) ∷
   rw 124 (q16 c4) ∷
   rw 121 (q16 c4) ∷
   rw 118 (q17 c4) ∷
   rw 115 (q18 c4) ∷
   rw 112 (q18 c4) ∷
   rw 109 (q18 c4) ∷
   rw 106 (q16 c4) ∷
   rw 103 (q19 c4) ∷
   rw 100 (q16 c4) ∷
   rw 97 (q19 c4) ∷
   rw 94 (q16 c4) ∷
   rw 149 (q17 c4) ∷
   rw 146 (q18 c4) ∷
   rw 143 (q18 c4) ∷
   rw 140 (q18 c4) ∷
   rw 137 (q16 c4) ∷
   rw 134 (q19 c4) ∷
   rw 131 (q16 c4) ∷
   rw 128 (q19 c4) ∷
   rw 125 (q16 c4) ∷
   rw 122 (q16 c4) ∷
   rw 119 (q17 c4) ∷
   rw 116 (q18 c4) ∷
   rw 113 (q18 c4) ∷
   rw 110 (q18 c4) ∷
   rw 107 (q16 c4) ∷
   rw 104 (q19 c4) ∷
   rw 101 (q16 c4) ∷
   rw 98 (q19 c4) ∷
   rw 95 (q16 c4) ∷
   rw⁻ 1 (q30 c4) ∷
   rw⁻ 27 (q31 c4) ∷ []) Eq.refl
