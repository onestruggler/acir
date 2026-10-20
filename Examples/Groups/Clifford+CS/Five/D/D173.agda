{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D173 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0001 ; wl0002 ; wl0007 ; wl0031 ; wl0056 ; wl0062 ; wl0076 ; wl0248 ; wl0249 ; wl0250 ; wl0283 ; wl0433 ; wl0474 ; wl0548 ; wl0560 ; wl0714 ; wl0715 ; wl0716 ; wl0717 ; wl0718 ; wl0719 ; wl0720 ; wl0721 ; wl0722 ; wl0723 ; wl0724 ; wl0725 ; wl0726 ; wl0727 ; wl0728 ; wl0729 ; wl0730 ; wl0731 ; wl0732 ; wp0034 ; wp0059 ; wp0126 ; wp0178 ; wp0340 ; wp0341 ; wp0342 ; wp0343 ; wp0344 ; wp0345 ; wp0346 ; wp0347 ; wp0348 ; wp0349 ; wp0350 ; wp0351 ; wp0352 ; wp0353 ; wp0354 ; wp0355 ; wp0356 ; wp0357 ; wp0358 ; wp0359 ; wp0360 ; wp0361 ; wp0362 ; wp0363 ; wp0364 ; wp0365 ; wp0366 ; wp0367 ; wp0368 ; wp0369)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-CS20-beta-ci)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-beta-T-at0210243143 ; lem-sym23-at021021)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-CS12-beta-at021021 ; lem-F5-CS01 ; lem-sym23-at02102331)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143 ; lem-beta-T-at0210233441 ; lem-sym23-at0210233441 ; lem-sym23-at02102441 ; lem-sym34-at0210243143 ; lem-sym34-at02102441)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-nat-0-SBOX⟨0·1·42·3⟩ ; lem-nat-0-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨1·0·42·3⟩ ; lem-nat-1-SBOX⟨2·0·41·3⟩ ; lem-nat-3-SBOX⟨0·1·32·4⟩ ; lem-nat-3-SBOX⟨0·1·42·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-nat-3-SBOX⟨2·0·31·4⟩)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-nat-3-SBOX⟨2·0·41·3⟩)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X4 ∷ X4 ∷ []) [] (wl0283 (lit c4))
  q2 : Ws → Eqn
  q2 c4 = eqn (CS04 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ CS04 ∷ []) (wp0340 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (CS04 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ CS04 ∷ []) (wp0341 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (CS04 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ CS04 ∷ []) (wp0342 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Bx2-0413 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-beta-T-at0210243143 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0433 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (CS04 ∷ X4 ∷ CS12 ∷ X4 ∷ []) (X4 ∷ CS12 ∷ X4 ∷ CS04 ∷ []) (wp0343 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CS04 ∷ X4 ∷ CX13 ∷ X4 ∷ []) (X4 ∷ CX13 ∷ X4 ∷ CS04 ∷ []) (wp0344 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CS04 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (X4 ∷ CS23⁻ ∷ X4 ∷ CS04 ∷ []) (wp0345 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (CS04 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (X4 ∷ CS23 ∷ X4 ∷ CS04 ∷ []) (wp0346 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CS04 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ CS04 ∷ []) (wp0347 c4)

-- F4 CS01^0|S0^1: 58 steps
lem-F4-CS01ᵖ0∣S0ᵖ1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣S0ᵖ1 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   re 13 1 (CS03⁻ ∷ []) ∷
   rw⁻ 12 (q2 c4) ∷
   re 14 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 9 (q3 c4) ∷
   re 7 1 (CS03 ∷ []) ∷
   rw⁻ 6 (q4 c4) ∷
   re 8 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 3 (q3 c4) ∷
   rw 1 (q5 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw 10 (q6 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw⁻ 17 (q1 c4) ∷
   rw⁻ 20 (q1 c4) ∷
   rw⁻ 21 (q7 c4) ∷
   rw⁻ 18 (q8 c4) ∷
   rw⁻ 15 (q9 c4) ∷
   rw⁻ 12 (q8 c4) ∷
   rw⁻ 9 (q10 c4) ∷
   rw 12 (q1 c4) ∷
   rw 13 (q1 c4) ∷
   rw 14 (q1 c4) ∷
   rw 15 (q1 c4) ∷
   rw⁻ 11 (q6 c4) ∷
   rw⁻ 6 (q11 c4) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw⁻ 15 (q7 c4) ∷
   rw⁻ 12 (q8 c4) ∷
   rw⁻ 9 (q9 c4) ∷
   rw⁻ 6 (q8 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   rw⁻ 0 (q11 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   re 2 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q12 : Ws → Eqn
  q12 c4 = eqn (CS14 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ CS14 ∷ []) (wp0348 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (CS14 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ CS14 ∷ []) (wl0714 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CS14 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ CS14 ∷ []) (wp0349 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (CS14 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ X4 ∷ CS14 ∷ []) (wl0715 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (CS14 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ CS14 ∷ []) (wp0350 c4)

-- F4 CS01^0|S1^1: 30 steps
lem-F4-CS01ᵖ0∣S1ᵖ1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣S1ᵖ1 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   re 13 1 (CS03⁻ ∷ []) ∷
   rw⁻ 12 (q12 c4) ∷
   re 14 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 9 (q13 c4) ∷
   re 7 1 (CS03 ∷ []) ∷
   rw⁻ 6 (q14 c4) ∷
   re 8 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 3 (q13 c4) ∷
   rw 1 (q5 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 9 (q15 c4) ∷
   rw⁻ 6 (q16 c4) ∷
   rw⁻ 3 (q15 c4) ∷
   rw⁻ 0 (q16 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   re 2 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = eqn (CS24 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ []) (wp0351 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CS24 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ CS24 ∷ []) (wl0716 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (CS24 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ CS24 ∷ []) (wp0352 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (CS24 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ X4 ∷ CS24 ∷ []) (wl0717 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (CS24 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ CS24 ∷ []) (wp0353 c4)

-- F4 CS01^0|S2^1: 30 steps
lem-F4-CS01ᵖ0∣S2ᵖ1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣S2ᵖ1 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   re 13 1 (CS03⁻ ∷ []) ∷
   rw⁻ 12 (q17 c4) ∷
   re 14 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 9 (q18 c4) ∷
   re 7 1 (CS03 ∷ []) ∷
   rw⁻ 6 (q19 c4) ∷
   re 8 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 3 (q18 c4) ∷
   rw 1 (q5 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 9 (q20 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   rw⁻ 3 (q20 c4) ∷
   rw⁻ 0 (q21 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   re 2 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q22 : Ws → Eqn
  q22 c4 = eqn (CS34 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ CS34 ∷ []) (wp0354 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CS34 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ CS34 ∷ []) (wl0718 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CS34 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ CS34 ∷ []) (wp0355 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CS34 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ X4 ∷ CS34 ∷ []) (wl0719 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CS34 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ CS34 ∷ []) (wp0356 c4)

-- F4 CS01^0|S3^1: 30 steps
lem-F4-CS01ᵖ0∣S3ᵖ1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣S3ᵖ1 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   re 13 1 (CS03⁻ ∷ []) ∷
   rw⁻ 12 (q22 c4) ∷
   re 14 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 9 (q23 c4) ∷
   re 7 1 (CS03 ∷ []) ∷
   rw⁻ 6 (q24 c4) ∷
   re 8 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 3 (q23 c4) ∷
   rw 1 (q5 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 9 (q25 c4) ∷
   rw⁻ 6 (q26 c4) ∷
   rw⁻ 3 (q25 c4) ∷
   rw⁻ 0 (q26 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw 3 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   re 2 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = eqn (CK40 ∷ []) (ι ∷ S4⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (wp0126 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (X4 ∷ ι ∷ []) (ι ∷ X4 ∷ []) (zc)
  q29 : Ws → Eqn
  q29 c4 = eqn (Sb2-0-41-3 ∷ ι ∷ []) (ι ∷ Sb2-0-41-3 ∷ []) (zc)
  q30 : Ws → Eqn
  q30 c4 = eqn (S4⁻ ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ S4⁻ ∷ []) (wp0357 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (S4⁻ ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ S4⁻ ∷ []) (wl0720 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (S4⁻ ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ S4⁻ ∷ []) (wp0358 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (S4⁻ ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ X4 ∷ S4⁻ ∷ []) (wl0721 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (S4⁻ ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ S4⁻ ∷ []) (wp0359 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (K0 ∷ CS04 ∷ K0 ∷ X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ X4 ∷ Toff314 ∷ X4 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ []) (wp0360 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ []) (wp0361 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (K0 ∷ X4 ∷ []) (X4 ∷ K0 ∷ []) (c₁ (K) (X ↑ ↑ ↑))
  q38 : Ws → Eqn
  q38 c4 = eqn (K0 ∷ CCZ123 ∷ []) (CCZ123 ∷ K0 ∷ []) (c₁ (K) (CCZ))
  q39 : Ws → Eqn
  q39 c4 = eqn (K0 ∷ CS04 ∷ K0 ∷ X4 ∷ Toff204 ∷ X4 ∷ []) (X4 ∷ Toff204 ∷ X4 ∷ K0 ∷ CS04 ∷ K0 ∷ []) (wp0362 c4)

-- F4 CS01^0|K0^1: 219 steps
lem-F4-CS01ᵖ0∣K0ᵖ1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣K0ᵖ1 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw 3 (q27 c4) ∷
   rw 2 (q28 c4) ∷
   rw 1 (q29 c4) ∷
   rw 0 (q28 c4) ∷
   re 2 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 3 (q1 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   re 14 1 (CS03⁻ ∷ []) ∷
   rw⁻ 13 (q30 c4) ∷
   re 15 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 10 (q31 c4) ∷
   re 8 1 (CS03 ∷ []) ∷
   rw⁻ 7 (q32 c4) ∷
   re 9 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 4 (q31 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 10 (q33 c4) ∷
   rw⁻ 7 (q34 c4) ∷
   rw⁻ 4 (q33 c4) ∷
   rw⁻ 1 (q34 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   re 3 5 (Sb2-0-41-3 ∷ []) ∷
   re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   rw⁻ 13 (q1 c4) ∷
   re 15 1 (CS03⁻ ∷ []) ∷
   rw⁻ 14 (q2 c4) ∷
   re 16 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 11 (q3 c4) ∷
   re 9 1 (CS03 ∷ []) ∷
   rw⁻ 8 (q4 c4) ∷
   re 10 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 5 (q3 c4) ∷
   rw 3 (q5 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   rw 12 (q6 c4) ∷
   rw⁻ 13 (q1 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw⁻ 23 (q7 c4) ∷
   rw⁻ 20 (q8 c4) ∷
   rw⁻ 17 (q9 c4) ∷
   rw⁻ 14 (q8 c4) ∷
   rw⁻ 11 (q10 c4) ∷
   rw 14 (q1 c4) ∷
   rw 15 (q1 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw⁻ 13 (q6 c4) ∷
   rw⁻ 8 (q11 c4) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   rw⁻ 13 (q1 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 17 (q7 c4) ∷
   rw⁻ 14 (q8 c4) ∷
   rw⁻ 11 (q9 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw⁻ 5 (q10 c4) ∷
   rw 8 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw⁻ 4 (q5 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   re 4 5 (Sb2-0-41-3 ∷ []) ∷
   re 4 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   re 10 1 (CS03 ∷ []) ∷
   re 16 1 (CS03⁻ ∷ []) ∷
   rw⁻ 9 (q35 c4) ∷
   re 13 1 (Sb2-0-3-1 ∷ []) ∷
   re 19 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 6 (q36 c4) ∷
   rw 4 (q5 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q37 c4) ∷
   rw⁻ 13 (q38 c4) ∷
   rw⁻ 12 (q37 c4) ∷
   rw 14 (q6 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 25 (q7 c4) ∷
   rw⁻ 22 (q8 c4) ∷
   rw⁻ 19 (q9 c4) ∷
   rw⁻ 16 (q8 c4) ∷
   rw⁻ 13 (q10 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw⁻ 15 (q6 c4) ∷
   rw⁻ 16 (q37 c4) ∷
   rw⁻ 15 (q38 c4) ∷
   rw⁻ 14 (q37 c4) ∷
   rw⁻ 9 (q39 c4) ∷
   rw⁻ 8 (q37 c4) ∷
   rw⁻ 7 (q38 c4) ∷
   rw⁻ 6 (q37 c4) ∷
   rw 8 (q6 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw⁻ 19 (q7 c4) ∷
   rw⁻ 16 (q8 c4) ∷
   rw⁻ 13 (q9 c4) ∷
   rw⁻ 10 (q8 c4) ∷
   rw⁻ 7 (q10 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw 12 (q1 c4) ∷
   rw 13 (q1 c4) ∷
   rw⁻ 9 (q6 c4) ∷
   rw⁻ 10 (q37 c4) ∷
   rw⁻ 9 (q38 c4) ∷
   rw⁻ 8 (q37 c4) ∷
   rw⁻ 3 (q39 c4) ∷
   rw 8 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw 8 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   re 7 5 (Sb2-0-41-3 ∷ []) ∷
   re 7 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw⁻ 17 (q1 c4) ∷
   re 19 1 (CS03⁻ ∷ []) ∷
   rw⁻ 18 (q2 c4) ∷
   re 20 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 15 (q3 c4) ∷
   re 13 1 (CS03 ∷ []) ∷
   rw⁻ 12 (q4 c4) ∷
   re 14 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 9 (q3 c4) ∷
   rw 7 (q5 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw 16 (q6 c4) ∷
   rw⁻ 17 (q1 c4) ∷
   rw⁻ 20 (q1 c4) ∷
   rw⁻ 23 (q1 c4) ∷
   rw⁻ 26 (q1 c4) ∷
   rw⁻ 27 (q7 c4) ∷
   rw⁻ 24 (q8 c4) ∷
   rw⁻ 21 (q9 c4) ∷
   rw⁻ 18 (q8 c4) ∷
   rw⁻ 15 (q10 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw 20 (q1 c4) ∷
   rw 21 (q1 c4) ∷
   rw⁻ 17 (q6 c4) ∷
   rw⁻ 12 (q11 c4) ∷
   rw 10 (q6 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw⁻ 17 (q1 c4) ∷
   rw⁻ 20 (q1 c4) ∷
   rw⁻ 21 (q7 c4) ∷
   rw⁻ 18 (q8 c4) ∷
   rw⁻ 15 (q9 c4) ∷
   rw⁻ 12 (q8 c4) ∷
   rw⁻ 9 (q10 c4) ∷
   rw 12 (q1 c4) ∷
   rw 13 (q1 c4) ∷
   rw 14 (q1 c4) ∷
   rw 15 (q1 c4) ∷
   rw⁻ 11 (q6 c4) ∷
   rw⁻ 6 (q11 c4) ∷
   rw 9 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw 9 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw 12 (q1 c4) ∷
   re 8 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 0 (q27 c4) ∷ []) Eq.refl

private
  q40 : Ws → Eqn
  q40 c4 = eqn (CK41 ∷ []) (ι1 ∷ S4⁻ ∷ CS14 ∷ K1 ∷ CS14 ∷ K1 ∷ CS14 ∷ []) (wp0178 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (ι1 ∷ []) (ι ∷ []) (uₛ (iI ↑) (iI) Eq.refl)
  q42 : Ws → Eqn
  q42 c4 = eqn (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ CS03⁻ ∷ X4 ∷ []) (X4 ∷ CS03⁻ ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ []) (wp0363 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ Toff314 ∷ X4 ∷ []) (X4 ∷ Toff314 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ []) (wl0722 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ CS03 ∷ X4 ∷ []) (X4 ∷ CS03 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ []) (wp0364 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0431 ∷ []) (lem-sym34-at0210243143 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0341 ∷ []) (lem-sym23-at02102441 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-beta-T-at0210233441 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (K1 ∷ CS14 ∷ K1 ∷ X4 ∷ CCZ124 ∷ X4 ∷ []) (X4 ∷ CCZ124 ∷ X4 ∷ K1 ∷ CS14 ∷ K1 ∷ []) (wl0723 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (K1 ∷ X4 ∷ []) (X4 ∷ K1 ∷ []) (c₂ (K ↑) (X ↑ ↑))
  q50 : Ws → Eqn
  q50 c4 = eqn (K1 ∷ Toff203 ∷ []) (Toff203 ∷ K1 ∷ []) (wl0724 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) (wl0548 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (CS14 ∷ X4 ∷ K2⁻ ∷ X4 ∷ []) (X4 ∷ K2⁻ ∷ X4 ∷ CS14 ∷ []) (wl0725 (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (wl0560 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (CS14 ∷ X4 ∷ CS02 ∷ X4 ∷ []) (X4 ∷ CS02 ∷ X4 ∷ CS14 ∷ []) (wp0365 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (CS14 ∷ X4 ∷ CX03 ∷ X4 ∷ []) (X4 ∷ CX03 ∷ X4 ∷ CS14 ∷ []) (wp0366 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (CS14 ∷ X4 ∷ CS23⁻ ∷ X4 ∷ []) (X4 ∷ CS23⁻ ∷ X4 ∷ CS14 ∷ []) (wl0726 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (CS14 ∷ X4 ∷ CS23 ∷ X4 ∷ []) (X4 ∷ CS23 ∷ X4 ∷ CS14 ∷ []) (wl0727 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (CS14 ∷ X4 ∷ K2 ∷ X4 ∷ []) (X4 ∷ K2 ∷ X4 ∷ CS14 ∷ []) (wl0728 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (Bx2-0341 ∷ []) (Bx2-0431 ∷ []) (lem-sym23-at0210233441 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0413 ∷ []) (lem-sym34-at02102441 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (ι ∷ []) (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl)

-- F4 CS01^0|K1^1: 187 steps
lem-F4-CS01ᵖ0∣K1ᵖ1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣K1ᵖ1 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw 3 (q40 c4) ∷
   rw 3 (q41 c4) ∷
   rw 2 (q28 c4) ∷
   rw 1 (q29 c4) ∷
   rw 0 (q28 c4) ∷
   re 2 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 3 (q1 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   re 14 1 (CS03⁻ ∷ []) ∷
   rw⁻ 13 (q30 c4) ∷
   re 15 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 10 (q31 c4) ∷
   re 8 1 (CS03 ∷ []) ∷
   rw⁻ 7 (q32 c4) ∷
   re 9 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 4 (q31 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 10 (q33 c4) ∷
   rw⁻ 7 (q34 c4) ∷
   rw⁻ 4 (q33 c4) ∷
   rw⁻ 1 (q34 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   re 3 5 (Sb2-0-41-3 ∷ []) ∷
   re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   rw⁻ 13 (q1 c4) ∷
   re 15 1 (CS03⁻ ∷ []) ∷
   rw⁻ 14 (q12 c4) ∷
   re 16 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 11 (q13 c4) ∷
   re 9 1 (CS03 ∷ []) ∷
   rw⁻ 8 (q14 c4) ∷
   re 10 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 5 (q13 c4) ∷
   rw 3 (q5 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   rw⁻ 11 (q15 c4) ∷
   rw⁻ 8 (q16 c4) ∷
   rw⁻ 5 (q15 c4) ∷
   rw⁻ 2 (q16 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw⁻ 4 (q5 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   re 4 5 (Sb2-0-41-3 ∷ []) ∷
   re 4 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   re 16 1 (CS03⁻ ∷ []) ∷
   rw⁻ 15 (q42 c4) ∷
   re 19 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 12 (q43 c4) ∷
   re 10 1 (CS03 ∷ []) ∷
   rw⁻ 9 (q44 c4) ∷
   re 13 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 6 (q43 c4) ∷
   rw 4 (q45 c4) ∷
   rw 4 (q46 c4) ∷
   rw 4 (q47 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 12 (q48 c4) ∷
   rw⁻ 11 (q49 c4) ∷
   rw⁻ 10 (q50 c4) ∷
   rw⁻ 9 (q49 c4) ∷
   rw⁻ 11 (q51 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   rw⁻ 16 (q52 c4) ∷
   rw 14 (q53 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw⁻ 21 (q1 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 25 (q54 c4) ∷
   rw⁻ 22 (q55 c4) ∷
   rw⁻ 19 (q56 c4) ∷
   rw⁻ 16 (q55 c4) ∷
   rw⁻ 13 (q57 c4) ∷
   rw 16 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw 19 (q1 c4) ∷
   rw⁻ 15 (q53 c4) ∷
   rw⁻ 10 (q58 c4) ∷
   rw 13 (q1 c4) ∷
   rw 14 (q1 c4) ∷
   rw 12 (q51 c4) ∷
   rw⁻ 13 (q49 c4) ∷
   rw⁻ 12 (q50 c4) ∷
   rw⁻ 11 (q49 c4) ∷
   rw⁻ 6 (q48 c4) ∷
   rw⁻ 5 (q49 c4) ∷
   rw⁻ 4 (q50 c4) ∷
   rw⁻ 3 (q49 c4) ∷
   rw⁻ 5 (q51 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 10 (q52 c4) ∷
   rw 8 (q53 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw⁻ 19 (q54 c4) ∷
   rw⁻ 16 (q55 c4) ∷
   rw⁻ 13 (q56 c4) ∷
   rw⁻ 10 (q55 c4) ∷
   rw⁻ 7 (q57 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw 12 (q1 c4) ∷
   rw 13 (q1 c4) ∷
   rw⁻ 9 (q53 c4) ∷
   rw⁻ 4 (q58 c4) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   rw 6 (q51 c4) ∷
   rw⁻ 7 (q49 c4) ∷
   rw⁻ 6 (q50 c4) ∷
   rw⁻ 5 (q49 c4) ∷
   rw 8 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw⁻ 7 (q47 c4) ∷
   rw 7 (q59 c4) ∷
   rw 7 (q60 c4) ∷
   rw 8 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   re 7 5 (Sb2-0-41-3 ∷ []) ∷
   re 7 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw⁻ 17 (q1 c4) ∷
   re 19 1 (CS03⁻ ∷ []) ∷
   rw⁻ 18 (q12 c4) ∷
   re 20 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 15 (q13 c4) ∷
   re 13 1 (CS03 ∷ []) ∷
   rw⁻ 12 (q14 c4) ∷
   re 14 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 9 (q13 c4) ∷
   rw 7 (q5 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw⁻ 15 (q15 c4) ∷
   rw⁻ 12 (q16 c4) ∷
   rw⁻ 9 (q15 c4) ∷
   rw⁻ 6 (q16 c4) ∷
   rw 9 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw 9 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw 12 (q1 c4) ∷
   re 8 5 (Sb2-0-41-3 ∷ []) ∷
   rw 0 (q61 c4) ∷
   rw⁻ 0 (q40 c4) ∷ []) Eq.refl

private
  q62 : Ws → Eqn
  q62 c4 = eqn (Sw34 ∷ Sw34 ∷ []) [] (wl0007 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (Sw34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-32-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·42·3⟩ (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (K0 ∷ Sw34 ∷ []) (Sw34 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ ↑))
  q65 : Ws → Eqn
  q65 c4 = eqn (Sb0-1-32-4 ∷ K0 ∷ []) (K0 ∷ Sb0-1-32-4 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at2332 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (Sw34 ∷ Sb0-1-32-4 ∷ []) (Sb0-1-42-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨0·1·32·4⟩ (lit c4))

-- auto SBOX(0;1;23;4) | K0 @243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at243243 : Ws → ⟪ (Sb0-1-42-3 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at243243 c4 = derive (Sb0-1-42-3 ∷ K0 ∷ []) (K0 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q62 c4) ∷
   rw 1 (q63 c4) ∷
   rw⁻ 2 (q64 c4) ∷
   rw 1 (q65 c4) ∷
   rw⁻ 0 (q64 c4) ∷
   rw 1 (q66 c4) ∷
   rw 2 (q62 c4) ∷ []) Eq.refl

private
  q67 : Ws → Eqn
  q67 c4 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wl0002 (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (Sw01 ∷ Sb1-0-42-3 ∷ []) (Sb0-1-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨1·0·42·3⟩ (lit c4))
  q69 : Ws → Eqn
  q69 c4 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wl0031 (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (Sb0-1-42-3 ∷ K0 ∷ []) (K0 ∷ Sb0-1-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at243243 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wl0076 (lit c4))
  q72 : Ws → Eqn
  q72 c4 = eqn (Sw01 ∷ Sb0-1-42-3 ∷ []) (Sb1-0-42-3 ∷ Sw01 ∷ []) (lem-nat-0-SBOX⟨0·1·42·3⟩ (lit c4))

-- auto SBOX(0;1;23;4) | K0 @0110243243: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at0110243243 : Ws → ⟪ (Sb1-0-42-3 ∷ K1 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ Sb1-0-42-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at0110243243 c4 = derive (Sb1-0-42-3 ∷ K1 ∷ []) (K1 ∷ Sb1-0-42-3 ∷ [])
  (rw⁻ 0 (q67 c4) ∷
   rw 1 (q68 c4) ∷
   rw⁻ 2 (q69 c4) ∷
   rw 1 (q70 c4) ∷
   rw⁻ 0 (q71 c4) ∷
   rw 1 (q72 c4) ∷
   rw 2 (q67 c4) ∷ []) Eq.refl

private
  q73 : Ws → Eqn
  q73 c4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wl0001 (lit c4))
  q74 : Ws → Eqn
  q74 c4 = eqn (Sw12 ∷ Sb2-0-41-3 ∷ []) (Sb1-0-42-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨2·0·41·3⟩ (lit c4))
  q75 : Ws → Eqn
  q75 c4 = eqn (K1 ∷ Sw12 ∷ []) (Sw12 ∷ K2 ∷ []) (wl0062 (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (Sb1-0-42-3 ∷ K1 ∷ []) (K1 ∷ Sb1-0-42-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at0110243243 c4)
  q77 : Ws → Eqn
  q77 c4 = eqn (K2 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ []) (wl0056 (lit c4))
  q78 : Ws → Eqn
  q78 c4 = eqn (Sw12 ∷ Sb1-0-42-3 ∷ []) (Sb2-0-41-3 ∷ Sw12 ∷ []) (lem-nat-1-SBOX⟨1·0·42·3⟩ (lit c4))

-- auto SBOX(0;1;23;4) | K0 @0210243143: 7 steps
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at0210243143 : Ws → ⟪ (Sb2-0-41-3 ∷ K2 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at0210243143 c4 = derive (Sb2-0-41-3 ∷ K2 ∷ []) (K2 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 0 (q73 c4) ∷
   rw 1 (q74 c4) ∷
   rw⁻ 2 (q75 c4) ∷
   rw 1 (q76 c4) ∷
   rw⁻ 0 (q77 c4) ∷
   rw 1 (q78 c4) ∷
   rw 2 (q73 c4) ∷ []) Eq.refl

private
  q79 : Ws → Eqn
  q79 c4 = eqn (CK42 ∷ []) (ι ∷ S4⁻ ∷ CS24 ∷ K2 ∷ CS24 ∷ K2 ∷ CS24 ∷ []) (wl0729 (lit c4))
  q80 : Ws → Eqn
  q80 c4 = eqn (K2 ∷ X4 ∷ []) (X4 ∷ K2 ∷ []) (wl0730 (lit c4))
  q81 : Ws → Eqn
  q81 c4 = eqn (Sb2-0-41-3 ∷ K2 ∷ []) (K2 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K0-at0210243143 c4)

-- F4 CS01^0|K2^1: 131 steps
lem-F4-CS01ᵖ0∣K2ᵖ1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣K2ᵖ1 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw 3 (q79 c4) ∷
   rw 2 (q28 c4) ∷
   rw 1 (q29 c4) ∷
   rw 0 (q28 c4) ∷
   re 2 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 3 (q1 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   re 14 1 (CS03⁻ ∷ []) ∷
   rw⁻ 13 (q30 c4) ∷
   re 15 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 10 (q31 c4) ∷
   re 8 1 (CS03 ∷ []) ∷
   rw⁻ 7 (q32 c4) ∷
   re 9 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 4 (q31 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 10 (q33 c4) ∷
   rw⁻ 7 (q34 c4) ∷
   rw⁻ 4 (q33 c4) ∷
   rw⁻ 1 (q34 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   re 3 5 (Sb2-0-41-3 ∷ []) ∷
   re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   rw⁻ 13 (q1 c4) ∷
   re 15 1 (CS03⁻ ∷ []) ∷
   rw⁻ 14 (q17 c4) ∷
   re 16 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 11 (q18 c4) ∷
   re 9 1 (CS03 ∷ []) ∷
   rw⁻ 8 (q19 c4) ∷
   re 10 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 5 (q18 c4) ∷
   rw 3 (q5 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   rw⁻ 11 (q20 c4) ∷
   rw⁻ 8 (q21 c4) ∷
   rw⁻ 5 (q20 c4) ∷
   rw⁻ 2 (q21 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw⁻ 4 (q5 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   re 4 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 5 (q80 c4) ∷
   rw 4 (q81 c4) ∷
   rw⁻ 3 (q80 c4) ∷
   re 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   re 17 1 (CS03⁻ ∷ []) ∷
   rw⁻ 16 (q17 c4) ∷
   re 18 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 13 (q18 c4) ∷
   re 11 1 (CS03 ∷ []) ∷
   rw⁻ 10 (q19 c4) ∷
   re 12 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 7 (q18 c4) ∷
   rw 5 (q5 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw⁻ 13 (q20 c4) ∷
   rw⁻ 10 (q21 c4) ∷
   rw⁻ 7 (q20 c4) ∷
   rw⁻ 4 (q21 c4) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   re 6 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 7 (q80 c4) ∷
   rw 6 (q81 c4) ∷
   rw⁻ 5 (q80 c4) ∷
   re 7 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw⁻ 17 (q1 c4) ∷
   re 19 1 (CS03⁻ ∷ []) ∷
   rw⁻ 18 (q17 c4) ∷
   re 20 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 15 (q18 c4) ∷
   re 13 1 (CS03 ∷ []) ∷
   rw⁻ 12 (q19 c4) ∷
   re 14 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 9 (q18 c4) ∷
   rw 7 (q5 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw⁻ 15 (q20 c4) ∷
   rw⁻ 12 (q21 c4) ∷
   rw⁻ 9 (q20 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   rw 9 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw 9 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw 12 (q1 c4) ∷
   re 8 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 0 (q79 c4) ∷ []) Eq.refl

private
  q82 : Ws → Eqn
  q82 c4 = eqn (CK43 ∷ []) (ι ∷ S4⁻ ∷ CS34 ∷ K3 ∷ CS34 ∷ K3 ∷ CS34 ∷ []) (wl0731 (lit c4))
  q83 : Ws → Eqn
  q83 c4 = eqn (K3 ∷ X4 ∷ []) (X4 ∷ K3 ∷ []) (wl0732 (lit c4))
  q84 : Ws → Eqn
  q84 c4 = eqn (Sb2-0-41-3 ∷ K3 ∷ []) (K3 ∷ Sb2-0-41-3 ∷ []) (lem-auto-SBOX⟨0·1·23·4⟩-∣-K4-at0210243143 c4)

-- F4 CS01^0|K3^1: 131 steps
lem-F4-CS01ᵖ0∣K3ᵖ1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣K3ᵖ1 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw 3 (q82 c4) ∷
   rw 2 (q28 c4) ∷
   rw 1 (q29 c4) ∷
   rw 0 (q28 c4) ∷
   re 2 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 3 (q1 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   re 14 1 (CS03⁻ ∷ []) ∷
   rw⁻ 13 (q30 c4) ∷
   re 15 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 10 (q31 c4) ∷
   re 8 1 (CS03 ∷ []) ∷
   rw⁻ 7 (q32 c4) ∷
   re 9 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 4 (q31 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 10 (q33 c4) ∷
   rw⁻ 7 (q34 c4) ∷
   rw⁻ 4 (q33 c4) ∷
   rw⁻ 1 (q34 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw 4 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   re 3 5 (Sb2-0-41-3 ∷ []) ∷
   re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   rw⁻ 13 (q1 c4) ∷
   re 15 1 (CS03⁻ ∷ []) ∷
   rw⁻ 14 (q22 c4) ∷
   re 16 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 11 (q23 c4) ∷
   re 9 1 (CS03 ∷ []) ∷
   rw⁻ 8 (q24 c4) ∷
   re 10 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 5 (q23 c4) ∷
   rw 3 (q5 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   rw⁻ 11 (q25 c4) ∷
   rw⁻ 8 (q26 c4) ∷
   rw⁻ 5 (q25 c4) ∷
   rw⁻ 2 (q26 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw⁻ 4 (q5 c4) ∷
   rw 5 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   re 4 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 5 (q83 c4) ∷
   rw 4 (q84 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   re 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 6 (q1 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   re 17 1 (CS03⁻ ∷ []) ∷
   rw⁻ 16 (q22 c4) ∷
   re 18 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 13 (q23 c4) ∷
   re 11 1 (CS03 ∷ []) ∷
   rw⁻ 10 (q24 c4) ∷
   re 12 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 7 (q23 c4) ∷
   rw 5 (q5 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw⁻ 13 (q25 c4) ∷
   rw⁻ 10 (q26 c4) ∷
   rw⁻ 7 (q25 c4) ∷
   rw⁻ 4 (q26 c4) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 7 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   re 6 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 7 (q83 c4) ∷
   rw 6 (q84 c4) ∷
   rw⁻ 5 (q83 c4) ∷
   re 7 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw⁻ 17 (q1 c4) ∷
   re 19 1 (CS03⁻ ∷ []) ∷
   rw⁻ 18 (q22 c4) ∷
   re 20 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 15 (q23 c4) ∷
   re 13 1 (CS03 ∷ []) ∷
   rw⁻ 12 (q24 c4) ∷
   re 14 1 (Sb2-0-3-1 ∷ []) ∷
   rw⁻ 9 (q23 c4) ∷
   rw 7 (q5 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw⁻ 15 (q25 c4) ∷
   rw⁻ 12 (q26 c4) ∷
   rw⁻ 9 (q25 c4) ∷
   rw⁻ 6 (q26 c4) ∷
   rw 9 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw⁻ 8 (q5 c4) ∷
   rw 9 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw 12 (q1 c4) ∷
   re 8 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 0 (q82 c4) ∷ []) Eq.refl

private
  q85 : Ws → Eqn
  q85 c4 = eqn (Bx2-0314 ∷ []) (Bx2-0134 ∷ []) (lem-sym23-at02102331 c4)
  q86 : Ws → Eqn
  q86 c4 = eqn (CS01 ∷ Bx2-0134 ∷ []) (Bx2-0134 ∷ CS01 ∷ []) (lem-CS12-beta-at021021 c4)
  q87 : Ws → Eqn
  q87 c4 = eqn (Bx2-0134 ∷ []) (Bx2-0314 ∷ []) (lem-sym23-at021021 c4)

-- auto CS01 | BOX(2;0314): 3 steps
lem-auto-CS01-∣-BOX⟨2·0314⟩ : Ws → ⟪ (CS01 ∷ Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-BOX⟨2·0314⟩ c4 = derive (CS01 ∷ Bx2-0314 ∷ []) (Bx2-0314 ∷ CS01 ∷ [])
  (rw 1 (q85 c4) ∷
   rw 0 (q86 c4) ∷
   rw 0 (q87 c4) ∷ []) Eq.refl

private
  q88 : Ws → Eqn
  q88 c4 = eqn (CS01 ∷ Bx2-0314 ∷ []) (Bx2-0314 ∷ CS01 ∷ []) (lem-auto-CS01-∣-BOX⟨2·0314⟩ c4)
  q89 : Ws → Eqn
  q89 c4 = eqn (CS01 ∷ Toff413 ∷ []) (Toff413 ∷ CS01 ∷ []) (wp0367 c4)
  q90 : Ws → Eqn
  q90 c4 = eqn (CS01 ∷ CS04 ∷ []) (CS04 ∷ CS01 ∷ []) (wp0368 c4)
  q91 : Ws → Eqn
  q91 c4 = eqn (CS01 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CS01 ∷ []) (wp0369 c4)

-- auto CS01 | SBOX(2;0;31;4): 11 steps
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩ : Ws → ⟪ (CS01 ∷ Sb2-0-31-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-31-4 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩ c4 = derive (CS01 ∷ Sb2-0-31-4 ∷ []) (Sb2-0-31-4 ∷ CS01 ∷ [])
  (re 1 1 (Bx2-0314 ∷ Toff413 ∷ Sb2-0-4-1 ∷ Toff413 ∷ Sb⁻2-0-4-1 ∷ []) ∷
   rw 0 (q88 c4) ∷
   rw 1 (q89 c4) ∷
   re 3 1 (CS04 ∷ []) ∷
   rw 2 (q90 c4) ∷
   re 2 1 (Sb2-0-4-1 ∷ []) ∷
   rw 3 (q89 c4) ∷
   re 5 1 (CS04⁻ ∷ []) ∷
   rw 4 (q91 c4) ∷
   re 4 1 (Sb⁻2-0-4-1 ∷ []) ∷
   re 0 5 (Sb2-0-31-4 ∷ []) ∷ []) Eq.refl

private
  q92 : Ws → Eqn
  q92 c4 = eqn (CS01 ∷ Sw34 ∷ []) (Sw34 ∷ CS01 ∷ []) (c₂ (CS) (Swap ↑))
  q93 : Ws → Eqn
  q93 c4 = eqn (Sw34 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-31-4 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·41·3⟩ (lit c4))
  q94 : Ws → Eqn
  q94 c4 = eqn (CS01 ∷ Sb2-0-31-4 ∷ []) (Sb2-0-31-4 ∷ CS01 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩ c4)
  q95 : Ws → Eqn
  q95 c4 = eqn (Sw34 ∷ Sb2-0-31-4 ∷ []) (Sb2-0-41-3 ∷ Sw34 ∷ []) (lem-nat-3-SBOX⟨2·0·31·4⟩ (lit c4))

-- auto CS01 | SBOX(2;0;31;4) @3443: 7 steps
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at3443 : Ws → ⟪ (CS01 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS01 ∷ []) ⟫ʷ
lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at3443 c4 = derive (CS01 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS01 ∷ [])
  (rw⁻ 0 (q62 c4) ∷
   rw⁻ 1 (q92 c4) ∷
   rw 2 (q93 c4) ∷
   rw 1 (q94 c4) ∷
   rw 0 (q95 c4) ∷
   rw⁻ 1 (q92 c4) ∷
   rw 2 (q62 c4) ∷ []) Eq.refl

private
  q96 : Ws → Eqn
  q96 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CS01 ∷ []) (lem-F5-CS01 c4)
  q97 : Ws → Eqn
  q97 c4 = eqn (CCZ024 ∷ CCZ024 ∷ []) [] (wp0034 c4)
  q98 : Ws → Eqn
  q98 c4 = eqn (Toff204 ∷ Toff204 ∷ []) [] (wp0059 c4)
  q99 : Ws → Eqn
  q99 c4 = eqn (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ []) [] (wl0474 (lit c4))
  q100 : Ws → Eqn
  q100 c4 = eqn (Toff314 ∷ Toff314 ∷ []) [] (wl0248 (lit c4))
  q101 : Ws → Eqn
  q101 c4 = eqn (CS03 ∷ CS03⁻ ∷ []) [] (wl0250 (lit c4))
  q102 : Ws → Eqn
  q102 c4 = eqn (CS03⁻ ∷ CS03 ∷ []) [] (wl0249 (lit c4))
  q103 : Ws → Eqn
  q103 c4 = eqn (CS01 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS01 ∷ []) (lem-auto-CS01-∣-SBOX⟨2·0·31·4⟩-at3443 c4)

-- F4 CS01^0|CS01^1: 63 steps
lem-F4-CS01ᵖ0∣CS01ᵖ1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS01ᵖ0∣CS01ᵖ1 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw 0 (q96 c4) ∷
   rw⁻ 1 (q97 c4) ∷
   rw⁻ 2 (q98 c4) ∷
   rw⁻ 3 (q99 c4) ∷
   re 5 1 (Bx2-03 ∷ []) ∷
   re 8 1 (Bx2-03 ∷ []) ∷
   re 3 6 (Bx0-213 ∷ []) ∷
   re 4 1 (Bx⁻2-03 ∷ []) ∷
   re 7 1 (Bx⁻2-03 ∷ []) ∷
   re 4 6 (Bx⁻0-213 ∷ []) ∷
   rw⁻ 4 (q98 c4) ∷
   rw⁻ 5 (q97 c4) ∷
   rw⁻ 6 (q99 c4) ∷
   re 8 1 (Bx2-03 ∷ []) ∷
   re 11 1 (Bx2-03 ∷ []) ∷
   re 6 6 (Bx0-213 ∷ []) ∷
   re 7 1 (Bx⁻2-03 ∷ []) ∷
   re 10 1 (Bx⁻2-03 ∷ []) ∷
   re 7 6 (Bx⁻0-213 ∷ []) ∷
   re 1 6 (Bx2-0413 ∷ []) ∷
   re 2 6 (Bx⁻2-0413 ∷ []) ∷
   rw⁻ 2 (q100 c4) ∷
   rw⁻ 3 (q101 c4) ∷
   re 3 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   rw⁻ 4 (q100 c4) ∷
   rw⁻ 5 (q102 c4) ∷
   re 5 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 6 1 (Sb2-0-3-1 ∷ []) ∷
   re 1 5 (Sb2-0-41-3 ∷ []) ∷
   re 2 5 (Sb⁻2-0-41-3 ∷ []) ∷
   rw 0 (q103 c4) ∷
   rw⁻ 1 (q96 c4) ∷
   re 5 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) ∷
   re 4 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 8 1 (CS03⁻ ∷ []) ∷
   re 9 1 (CS03 ∷ []) ∷
   rw 8 (q102 c4) ∷
   rw 7 (q100 c4) ∷
   re 6 1 (CS03 ∷ []) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw 6 (q101 c4) ∷
   rw 5 (q100 c4) ∷
   re 5 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) ∷
   re 4 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) ∷
   re 9 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 11 1 (CZ03 ∷ []) ∷
   re 14 1 (CZ03 ∷ []) ∷
   re 15 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   re 15 1 (CZ03 ∷ []) ∷
   re 18 1 (CZ03 ∷ []) ∷
   rw 9 (q99 c4) ∷
   rw 8 (q97 c4) ∷
   rw 7 (q98 c4) ∷
   re 6 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) ∷
   re 8 1 (CZ03 ∷ []) ∷
   re 11 1 (CZ03 ∷ []) ∷
   re 12 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) ∷
   re 12 1 (CZ03 ∷ []) ∷
   re 15 1 (CZ03 ∷ []) ∷
   rw 6 (q99 c4) ∷
   rw 5 (q98 c4) ∷
   rw 4 (q97 c4) ∷ []) Eq.refl

private
  q104 : Ws → Eqn
  q104 c4 = eqn (CS02⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CS02⁻ ∷ []) (lem-CS20-beta-ci c4)

-- auto BOX(0;1234) | CSd02: 1 steps
lem-auto-BOX⟨0·1234⟩-∣-CSd02 : Ws → ⟪ (Bx0-1234 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-auto-BOX⟨0·1234⟩-∣-CSd02 c4 = derive (Bx0-1234 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Bx0-1234 ∷ [])
  (rw⁻ 0 (q104 c4) ∷ []) Eq.refl
