{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D196 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0885 ; wl0886 ; wl0887 ; wl0888 ; wl0889 ; wl0890 ; wl0891 ; wl0892 ; wl0893 ; wl0894 ; wl0895 ; wl0896 ; wl0897 ; wp0462 ; wp0463 ; wp0464 ; wp0465 ; wp0466 ; wp0467)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D171 using (lem-F4-iIᵖ0∣CS01ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-F4-CS01ᵖ0∣iIᵖ1 ; lem-F4-K1ᵖ0∣CS01ᵖ1 ; lem-F4-K1ᵖ0∣CS12ᵖ1 ; lem-F4-S0ᵖ0∣CS01ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D173 using (lem-F4-CS01ᵖ0∣CS01ᵖ1 ; lem-F4-CS01ᵖ0∣K1ᵖ1 ; lem-F4-CS01ᵖ0∣S0ᵖ1 ; lem-F4-CS01ᵖ0∣S1ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D177 using (lem-F4-CS12ᵖ0∣S2ᵖ1 ; lem-F4-CS12ᵖ0∣iIᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D178 using (lem-F4-CS12ᵖ0∣K1ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D179 using (lem-F4-CS12ᵖ0∣CS12ᵖ1 ; lem-F5-CS12)
open import Examples.Groups.Clifford+CS.Five.D.D195 using (lem-split4S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01 ; lem-split4iI-S0-S0-S0-CS01-K1-CS01-K1-CS01)
open import Examples.Groups.Clifford+CS.Five.D.TR using (tr05)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (lem-split4S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ []) (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (lem-split4iI-S0-S0-S0-CS01-K1-CS01-K1-CS01 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (CS14 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (wl0889 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-iIᵖ0∣CS01ᵖ1 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (wl0890 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CS04 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (wp0462 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (wl0891 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (wp0467 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (S4 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (wp0463 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣K1ᵖ1 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣iIᵖ1 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (wl0892 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0888 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (wl0887 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) [] (tr05 c4)

-- DB4[K1 S0 iI S0 S0 S0 CS01 K1 CS01 K1 CS01 S1 S1 S1 S1 S1 S1 S1 S1 S1 iI S0 S0 S0 CS01 K1 CS01 K1 CS01 S1 S1 S1]: 174 steps
lem-DB4K1-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1 : Ws → ⟪ (CK41 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
lem-DB4K1-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1 c4 = derive (CK41 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  (rw 1 (q1 c4) ∷
   rw 50 (q2 c4) ∷
   rw 49 (q3 c4) ∷
   rw 48 (q3 c4) ∷
   rw 47 (q3 c4) ∷
   rw 46 (q3 c4) ∷
   rw 45 (q3 c4) ∷
   rw 44 (q3 c4) ∷
   rw 43 (q3 c4) ∷
   rw 42 (q3 c4) ∷
   rw 41 (q3 c4) ∷
   rw⁻ 40 (q4 c4) ∷
   rw 39 (q5 c4) ∷
   rw⁻ 38 (q4 c4) ∷
   rw 37 (q5 c4) ∷
   rw⁻ 36 (q4 c4) ∷
   rw 35 (q6 c4) ∷
   rw 34 (q6 c4) ∷
   rw 33 (q6 c4) ∷
   rw 32 (q7 c4) ∷
   rw 31 (q6 c4) ∷
   rw 52 (q8 c4) ∷
   rw 51 (q8 c4) ∷
   rw 50 (q8 c4) ∷
   rw 49 (q8 c4) ∷
   rw 48 (q8 c4) ∷
   rw 47 (q8 c4) ∷
   rw 46 (q8 c4) ∷
   rw 45 (q8 c4) ∷
   rw 44 (q8 c4) ∷
   rw⁻ 43 (q9 c4) ∷
   rw 42 (q10 c4) ∷
   rw⁻ 41 (q9 c4) ∷
   rw 40 (q10 c4) ∷
   rw⁻ 39 (q9 c4) ∷
   rw 38 (q11 c4) ∷
   rw 37 (q11 c4) ∷
   rw 36 (q11 c4) ∷
   rw 35 (q12 c4) ∷
   rw 34 (q11 c4) ∷
   rw 55 (q8 c4) ∷
   rw 54 (q8 c4) ∷
   rw 53 (q8 c4) ∷
   rw 52 (q8 c4) ∷
   rw 51 (q8 c4) ∷
   rw 50 (q8 c4) ∷
   rw 49 (q8 c4) ∷
   rw 48 (q8 c4) ∷
   rw 47 (q8 c4) ∷
   rw⁻ 46 (q9 c4) ∷
   rw 45 (q10 c4) ∷
   rw⁻ 44 (q9 c4) ∷
   rw 43 (q10 c4) ∷
   rw⁻ 42 (q9 c4) ∷
   rw 41 (q11 c4) ∷
   rw 40 (q11 c4) ∷
   rw 39 (q11 c4) ∷
   rw 38 (q12 c4) ∷
   rw 37 (q11 c4) ∷
   rw 58 (q8 c4) ∷
   rw 57 (q8 c4) ∷
   rw 56 (q8 c4) ∷
   rw 55 (q8 c4) ∷
   rw 54 (q8 c4) ∷
   rw 53 (q8 c4) ∷
   rw 52 (q8 c4) ∷
   rw 51 (q8 c4) ∷
   rw 50 (q8 c4) ∷
   rw⁻ 49 (q9 c4) ∷
   rw 48 (q10 c4) ∷
   rw⁻ 47 (q9 c4) ∷
   rw 46 (q10 c4) ∷
   rw⁻ 45 (q9 c4) ∷
   rw 44 (q11 c4) ∷
   rw 43 (q11 c4) ∷
   rw 42 (q11 c4) ∷
   rw 41 (q12 c4) ∷
   rw 40 (q11 c4) ∷
   rw⁻ 61 (q13 c4) ∷
   rw⁻ 60 (q13 c4) ∷
   rw⁻ 59 (q13 c4) ∷
   rw⁻ 58 (q13 c4) ∷
   rw⁻ 57 (q13 c4) ∷
   rw⁻ 56 (q13 c4) ∷
   rw⁻ 55 (q13 c4) ∷
   rw⁻ 54 (q13 c4) ∷
   rw⁻ 53 (q13 c4) ∷
   rw⁻ 52 (q14 c4) ∷
   rw⁻ 51 (q15 c4) ∷
   rw⁻ 50 (q14 c4) ∷
   rw⁻ 49 (q15 c4) ∷
   rw⁻ 48 (q14 c4) ∷
   rw⁻ 47 (q16 c4) ∷
   rw⁻ 46 (q16 c4) ∷
   rw⁻ 45 (q16 c4) ∷
   rw⁻ 44 (q17 c4) ∷
   rw⁻ 43 (q16 c4) ∷
   rw 64 (q18 c4) ∷
   rw 63 (q18 c4) ∷
   rw 62 (q18 c4) ∷
   rw 61 (q18 c4) ∷
   rw 60 (q18 c4) ∷
   rw 59 (q18 c4) ∷
   rw 58 (q18 c4) ∷
   rw 57 (q18 c4) ∷
   rw 56 (q18 c4) ∷
   rw⁻ 55 (q19 c4) ∷
   rw 54 (q20 c4) ∷
   rw⁻ 53 (q19 c4) ∷
   rw 52 (q20 c4) ∷
   rw⁻ 51 (q19 c4) ∷
   rw 50 (q21 c4) ∷
   rw 49 (q21 c4) ∷
   rw 48 (q21 c4) ∷
   rw 47 (q22 c4) ∷
   rw 46 (q21 c4) ∷
   rw⁻ 67 (q13 c4) ∷
   rw⁻ 66 (q13 c4) ∷
   rw⁻ 65 (q13 c4) ∷
   rw⁻ 64 (q13 c4) ∷
   rw⁻ 63 (q13 c4) ∷
   rw⁻ 62 (q13 c4) ∷
   rw⁻ 61 (q13 c4) ∷
   rw⁻ 60 (q13 c4) ∷
   rw⁻ 59 (q13 c4) ∷
   rw⁻ 58 (q14 c4) ∷
   rw⁻ 57 (q15 c4) ∷
   rw⁻ 56 (q14 c4) ∷
   rw⁻ 55 (q15 c4) ∷
   rw⁻ 54 (q14 c4) ∷
   rw⁻ 53 (q16 c4) ∷
   rw⁻ 52 (q16 c4) ∷
   rw⁻ 51 (q16 c4) ∷
   rw⁻ 50 (q17 c4) ∷
   rw⁻ 49 (q16 c4) ∷
   rw 70 (q18 c4) ∷
   rw 69 (q18 c4) ∷
   rw 68 (q18 c4) ∷
   rw 67 (q18 c4) ∷
   rw 66 (q18 c4) ∷
   rw 65 (q18 c4) ∷
   rw 64 (q18 c4) ∷
   rw 63 (q18 c4) ∷
   rw 62 (q18 c4) ∷
   rw⁻ 61 (q19 c4) ∷
   rw 60 (q20 c4) ∷
   rw⁻ 59 (q19 c4) ∷
   rw 58 (q20 c4) ∷
   rw⁻ 57 (q19 c4) ∷
   rw 56 (q21 c4) ∷
   rw 55 (q21 c4) ∷
   rw 54 (q21 c4) ∷
   rw 53 (q22 c4) ∷
   rw 52 (q21 c4) ∷
   rw⁻ 73 (q13 c4) ∷
   rw⁻ 72 (q13 c4) ∷
   rw⁻ 71 (q13 c4) ∷
   rw⁻ 70 (q13 c4) ∷
   rw⁻ 69 (q13 c4) ∷
   rw⁻ 68 (q13 c4) ∷
   rw⁻ 67 (q13 c4) ∷
   rw⁻ 66 (q13 c4) ∷
   rw⁻ 65 (q13 c4) ∷
   rw⁻ 64 (q14 c4) ∷
   rw⁻ 63 (q15 c4) ∷
   rw⁻ 62 (q14 c4) ∷
   rw⁻ 61 (q15 c4) ∷
   rw⁻ 60 (q14 c4) ∷
   rw⁻ 59 (q16 c4) ∷
   rw⁻ 58 (q16 c4) ∷
   rw⁻ 57 (q16 c4) ∷
   rw⁻ 56 (q17 c4) ∷
   rw⁻ 55 (q16 c4) ∷
   rw 1 (q23 c4) ∷ []) Eq.refl

private
  q24 : Ws → Eqn
  q24 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CS12 ∷ []) (lem-F5-CS12 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (K1 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0885 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (S2 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0893 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (ι ∷ []) (wl0886 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (wl0894 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (wl0895 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0896 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣iIᵖ1 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣K1ᵖ1 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)

-- split4[S2 iI S2 S2 S2 CS12 K1 CS12 K1 CS12]: 55 steps
lem-split4S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12 : Ws → ⟪ (S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-split4S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12 c4 = derive (S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 9 (q24 c4) ∷
   rw 8 (q25 c4) ∷
   rw⁻ 7 (q24 c4) ∷
   rw 6 (q25 c4) ∷
   rw⁻ 5 (q24 c4) ∷
   rw 4 (q26 c4) ∷
   rw 3 (q26 c4) ∷
   rw 2 (q26 c4) ∷
   rw⁻ 1 (q27 c4) ∷
   rw 0 (q26 c4) ∷
   rw 3 (q28 c4) ∷
   rw 7 (q29 c4) ∷
   rw 6 (q30 c4) ∷
   rw 11 (q30 c4) ∷
   rw 10 (q29 c4) ∷
   rw 9 (q30 c4) ∷
   rw 15 (q30 c4) ∷
   rw 14 (q30 c4) ∷
   rw 13 (q29 c4) ∷
   rw 12 (q30 c4) ∷
   rw⁻ 19 (q31 c4) ∷
   rw⁻ 18 (q31 c4) ∷
   rw⁻ 17 (q31 c4) ∷
   rw⁻ 16 (q32 c4) ∷
   rw⁻ 15 (q31 c4) ∷
   rw⁻ 23 (q33 c4) ∷
   rw 22 (q34 c4) ∷
   rw 21 (q34 c4) ∷
   rw 20 (q34 c4) ∷
   rw 19 (q22 c4) ∷
   rw 18 (q34 c4) ∷
   rw⁻ 27 (q35 c4) ∷
   rw⁻ 26 (q36 c4) ∷
   rw⁻ 25 (q31 c4) ∷
   rw⁻ 24 (q31 c4) ∷
   rw⁻ 23 (q31 c4) ∷
   rw⁻ 22 (q32 c4) ∷
   rw⁻ 21 (q31 c4) ∷
   rw⁻ 31 (q33 c4) ∷
   rw 30 (q20 c4) ∷
   rw⁻ 29 (q33 c4) ∷
   rw 28 (q34 c4) ∷
   rw 27 (q34 c4) ∷
   rw 26 (q34 c4) ∷
   rw 25 (q22 c4) ∷
   rw 24 (q34 c4) ∷
   rw⁻ 35 (q35 c4) ∷
   rw⁻ 34 (q36 c4) ∷
   rw⁻ 33 (q35 c4) ∷
   rw⁻ 32 (q36 c4) ∷
   rw⁻ 31 (q31 c4) ∷
   rw⁻ 30 (q31 c4) ∷
   rw⁻ 29 (q31 c4) ∷
   rw⁻ 28 (q32 c4) ∷
   rw⁻ 27 (q31 c4) ∷ []) Eq.refl

-- split4[iI S2 S2 S2 CS12 K1 CS12 K1 CS12]: 45 steps
lem-split4iI-S2-S2-S2-CS12-K1-CS12-K1-CS12 : Ws → ⟪ (ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-split4iI-S2-S2-S2-CS12-K1-CS12-K1-CS12 c4 = derive (ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ []) (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 8 (q24 c4) ∷
   rw 7 (q25 c4) ∷
   rw⁻ 6 (q24 c4) ∷
   rw 5 (q25 c4) ∷
   rw⁻ 4 (q24 c4) ∷
   rw 3 (q26 c4) ∷
   rw 2 (q26 c4) ∷
   rw 1 (q26 c4) ∷
   rw⁻ 0 (q27 c4) ∷
   rw 3 (q29 c4) ∷
   rw 7 (q30 c4) ∷
   rw 6 (q29 c4) ∷
   rw 11 (q30 c4) ∷
   rw 10 (q30 c4) ∷
   rw 9 (q29 c4) ∷
   rw⁻ 15 (q31 c4) ∷
   rw⁻ 14 (q31 c4) ∷
   rw⁻ 13 (q31 c4) ∷
   rw⁻ 12 (q32 c4) ∷
   rw⁻ 19 (q33 c4) ∷
   rw 18 (q34 c4) ∷
   rw 17 (q34 c4) ∷
   rw 16 (q34 c4) ∷
   rw 15 (q22 c4) ∷
   rw⁻ 23 (q35 c4) ∷
   rw⁻ 22 (q36 c4) ∷
   rw⁻ 21 (q31 c4) ∷
   rw⁻ 20 (q31 c4) ∷
   rw⁻ 19 (q31 c4) ∷
   rw⁻ 18 (q32 c4) ∷
   rw⁻ 27 (q33 c4) ∷
   rw 26 (q20 c4) ∷
   rw⁻ 25 (q33 c4) ∷
   rw 24 (q34 c4) ∷
   rw 23 (q34 c4) ∷
   rw 22 (q34 c4) ∷
   rw 21 (q22 c4) ∷
   rw⁻ 31 (q35 c4) ∷
   rw⁻ 30 (q36 c4) ∷
   rw⁻ 29 (q35 c4) ∷
   rw⁻ 28 (q36 c4) ∷
   rw⁻ 27 (q31 c4) ∷
   rw⁻ 26 (q31 c4) ∷
   rw⁻ 25 (q31 c4) ∷
   rw⁻ 24 (q32 c4) ∷ []) Eq.refl
