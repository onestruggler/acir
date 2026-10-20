{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D187 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0885 ; wl0886 ; wl0887 ; wl0888 ; wp0461 ; wp0463 ; wp0464 ; wp0465)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-F5-CS01)
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-F4-CS01ᵖ0∣iIᵖ1 ; lem-F4-K1ᵖ0∣CS01ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D173 using (lem-F4-CS01ᵖ0∣CS01ᵖ1 ; lem-F4-CS01ᵖ0∣K1ᵖ1 ; lem-F4-CS01ᵖ0∣S0ᵖ1)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CS01 ∷ []) (lem-F5-CS01 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (K1 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0885 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (S0 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0461 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (ι ∷ []) (wl0886 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (wp0463 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣iIᵖ1 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (wl0887 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣K1ᵖ1 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0888 (lit c4))

-- split4[iI S0 S0 S0 CS01 K1 CS01 K1 CS01 CS01 CS01]: 66 steps
lem-split4iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-CS01-CS01 : Ws → ⟪ (ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-split4iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-CS01-CS01 c4 = derive (ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ [])
  (rw⁻ 10 (q1 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw 7 (q2 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw 5 (q2 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw 3 (q3 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q3 c4) ∷
   rw⁻ 0 (q4 c4) ∷
   rw 3 (q5 c4) ∷
   rw 7 (q6 c4) ∷
   rw 6 (q5 c4) ∷
   rw 11 (q6 c4) ∷
   rw 10 (q6 c4) ∷
   rw 9 (q5 c4) ∷
   rw⁻ 15 (q7 c4) ∷
   rw⁻ 14 (q7 c4) ∷
   rw⁻ 13 (q7 c4) ∷
   rw⁻ 12 (q8 c4) ∷
   rw⁻ 19 (q9 c4) ∷
   rw 18 (q10 c4) ∷
   rw 17 (q10 c4) ∷
   rw 16 (q10 c4) ∷
   rw 15 (q11 c4) ∷
   rw⁻ 23 (q12 c4) ∷
   rw⁻ 22 (q13 c4) ∷
   rw⁻ 21 (q7 c4) ∷
   rw⁻ 20 (q7 c4) ∷
   rw⁻ 19 (q7 c4) ∷
   rw⁻ 18 (q8 c4) ∷
   rw⁻ 27 (q9 c4) ∷
   rw 26 (q14 c4) ∷
   rw⁻ 25 (q9 c4) ∷
   rw 24 (q10 c4) ∷
   rw 23 (q10 c4) ∷
   rw 22 (q10 c4) ∷
   rw 21 (q11 c4) ∷
   rw⁻ 31 (q12 c4) ∷
   rw⁻ 30 (q13 c4) ∷
   rw⁻ 29 (q12 c4) ∷
   rw⁻ 28 (q13 c4) ∷
   rw⁻ 27 (q7 c4) ∷
   rw⁻ 26 (q7 c4) ∷
   rw⁻ 25 (q7 c4) ∷
   rw⁻ 24 (q8 c4) ∷
   rw⁻ 35 (q13 c4) ∷
   rw⁻ 34 (q12 c4) ∷
   rw⁻ 33 (q13 c4) ∷
   rw⁻ 32 (q12 c4) ∷
   rw⁻ 31 (q13 c4) ∷
   rw⁻ 30 (q7 c4) ∷
   rw⁻ 29 (q7 c4) ∷
   rw⁻ 28 (q7 c4) ∷
   rw⁻ 27 (q8 c4) ∷
   rw⁻ 39 (q13 c4) ∷
   rw⁻ 38 (q13 c4) ∷
   rw⁻ 37 (q12 c4) ∷
   rw⁻ 36 (q13 c4) ∷
   rw⁻ 35 (q12 c4) ∷
   rw⁻ 34 (q13 c4) ∷
   rw⁻ 33 (q7 c4) ∷
   rw⁻ 32 (q7 c4) ∷
   rw⁻ 31 (q7 c4) ∷
   rw⁻ 30 (q8 c4) ∷ []) Eq.refl
