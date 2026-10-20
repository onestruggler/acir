{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D189 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0885 ; wl0886 ; wl0887 ; wl0888 ; wl0893 ; wl0894 ; wl0895 ; wl0896 ; wl0897)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-F4-CS01ᵖ0∣iIᵖ1 ; lem-F4-K1ᵖ0∣CS12ᵖ1 ; lem-F4-S2ᵖ0∣CS12ᵖ1 ; lem-F4-iIᵖ0∣CS12ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D173 using (lem-F4-CS01ᵖ0∣CS01ᵖ1 ; lem-F4-CS01ᵖ0∣K1ᵖ1 ; lem-F4-CS01ᵖ0∣S0ᵖ1 ; lem-F4-CS01ᵖ0∣S1ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D177 using (lem-F4-CS12ᵖ0∣S2ᵖ1 ; lem-F4-CS12ᵖ0∣iIᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D178 using (lem-F4-CS12ᵖ0∣K1ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D179 using (lem-F4-CS12ᵖ0∣CS12ᵖ1 ; lem-F5-CS12)
open import Examples.Groups.Clifford+CS.Five.D.D188 using (lem-DB4K1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-CS01-CS01-S1-S1-S1-part0)
open import Examples.Groups.Clifford+CS.Five.D.TR using (tr01)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣iIᵖ1 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) (lem-F4-CS01ᵖ0∣K1ᵖ1 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) [] (tr01 c4)

-- DB4[K1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 S0 iI S0 S0 S0 CS01 K1 CS01 K1 CS01 S1 S1 S1 S1 S1 S1 S1 S1 S1 iI S0 S0 S0 CS01 K1 CS01 K1 CS01 CS01 CS01 S1 S1 S1] part1: 34 steps
lem-DB4K1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-CS01-CS01-S1-S1-S1-part1 : Ws → ⟪ (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
lem-DB4K1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-CS01-CS01-S1-S1-S1-part1 c4 = derive (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  (rw⁻ 85 (q1 c4) ∷
   rw⁻ 84 (q2 c4) ∷
   rw⁻ 83 (q3 c4) ∷
   rw⁻ 82 (q3 c4) ∷
   rw⁻ 81 (q3 c4) ∷
   rw⁻ 80 (q3 c4) ∷
   rw⁻ 79 (q3 c4) ∷
   rw⁻ 78 (q3 c4) ∷
   rw⁻ 105 (q4 c4) ∷
   rw⁻ 104 (q4 c4) ∷
   rw⁻ 103 (q4 c4) ∷
   rw⁻ 102 (q4 c4) ∷
   rw⁻ 101 (q4 c4) ∷
   rw⁻ 100 (q4 c4) ∷
   rw⁻ 99 (q4 c4) ∷
   rw⁻ 98 (q4 c4) ∷
   rw⁻ 97 (q4 c4) ∷
   rw⁻ 96 (q3 c4) ∷
   rw⁻ 95 (q5 c4) ∷
   rw⁻ 94 (q3 c4) ∷
   rw⁻ 93 (q5 c4) ∷
   rw⁻ 92 (q3 c4) ∷
   rw⁻ 91 (q2 c4) ∷
   rw⁻ 90 (q2 c4) ∷
   rw⁻ 89 (q2 c4) ∷
   rw⁻ 88 (q1 c4) ∷
   rw⁻ 87 (q2 c4) ∷
   rw⁻ 86 (q3 c4) ∷
   rw⁻ 85 (q3 c4) ∷
   rw⁻ 84 (q3 c4) ∷
   rw⁻ 83 (q3 c4) ∷
   rw⁻ 82 (q3 c4) ∷
   rw⁻ 81 (q3 c4) ∷
   rw 3 (q6 c4) ∷ []) Eq.refl

private
  q7 : Ws → Eqn
  q7 c4 = eqn (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (lem-DB4K1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-CS01-CS01-S1-S1-S1-part0 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (lem-DB4K1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-CS01-CS01-S1-S1-S1-part1 c4)

-- DB4[K1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 S0 iI S0 S0 S0 CS01 K1 CS01 K1 CS01 S1 S1 S1 S1 S1 S1 S1 S1 S1 iI S0 S0 S0 CS01 K1 CS01 K1 CS01 CS01 CS01 S1 S1 S1]: 2 steps
lem-DB4K1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-CS01-CS01-S1-S1-S1 : Ws → ⟪ (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
lem-DB4K1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-CS01-CS01-S1-S1-S1 c4 = derive (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  (rw 0 (q7 c4) ∷
   rw 0 (q8 c4) ∷ []) Eq.refl

private
  q9 : Ws → Eqn
  q9 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CS12 ∷ []) (lem-F5-CS12 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (K1 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0885 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (S2 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0893 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (ι ∷ []) (wl0886 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (CS24 ∷ X4 ∷ S4 ∷ X4 ∷ []) (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (wl0894 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-iIᵖ0∣CS12ᵖ1 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (S4 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (wl0895 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0896 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣iIᵖ1 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (wl0887 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) (lem-F4-CS12ᵖ0∣K1ᵖ1 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0888 (lit c4))

-- split4[CS12 CS12 CS12 CS12 CS12 CS12 S2 iI S2 S2 S2 CS12 K1 CS12 K1 CS12]: 136 steps
lem-split4CS12-CS12-CS12-CS12-CS12-CS12-S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12 : Ws → ⟪ (CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-split4CS12-CS12-CS12-CS12-CS12-CS12-S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12 c4 = derive (CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 15 (q9 c4) ∷
   rw 14 (q10 c4) ∷
   rw⁻ 13 (q9 c4) ∷
   rw 12 (q10 c4) ∷
   rw⁻ 11 (q9 c4) ∷
   rw 10 (q11 c4) ∷
   rw 9 (q11 c4) ∷
   rw 8 (q11 c4) ∷
   rw⁻ 7 (q12 c4) ∷
   rw 6 (q11 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   rw⁻ 3 (q9 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw⁻ 1 (q9 c4) ∷
   rw⁻ 0 (q9 c4) ∷
   rw⁻ 3 (q13 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw⁻ 6 (q13 c4) ∷
   rw⁻ 11 (q13 c4) ∷
   rw⁻ 10 (q13 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw⁻ 15 (q13 c4) ∷
   rw⁻ 14 (q13 c4) ∷
   rw⁻ 13 (q13 c4) ∷
   rw⁻ 12 (q13 c4) ∷
   rw⁻ 19 (q13 c4) ∷
   rw⁻ 18 (q13 c4) ∷
   rw⁻ 17 (q13 c4) ∷
   rw⁻ 16 (q13 c4) ∷
   rw⁻ 15 (q13 c4) ∷
   rw⁻ 23 (q14 c4) ∷
   rw⁻ 22 (q14 c4) ∷
   rw⁻ 21 (q14 c4) ∷
   rw⁻ 20 (q14 c4) ∷
   rw⁻ 19 (q14 c4) ∷
   rw⁻ 18 (q14 c4) ∷
   rw 27 (q15 c4) ∷
   rw⁻ 26 (q16 c4) ∷
   rw⁻ 25 (q16 c4) ∷
   rw⁻ 24 (q16 c4) ∷
   rw⁻ 23 (q16 c4) ∷
   rw⁻ 22 (q16 c4) ∷
   rw⁻ 21 (q16 c4) ∷
   rw 31 (q17 c4) ∷
   rw 30 (q18 c4) ∷
   rw⁻ 29 (q14 c4) ∷
   rw⁻ 28 (q14 c4) ∷
   rw⁻ 27 (q14 c4) ∷
   rw⁻ 26 (q14 c4) ∷
   rw⁻ 25 (q14 c4) ∷
   rw⁻ 24 (q14 c4) ∷
   rw 35 (q18 c4) ∷
   rw 34 (q17 c4) ∷
   rw 33 (q18 c4) ∷
   rw⁻ 32 (q14 c4) ∷
   rw⁻ 31 (q14 c4) ∷
   rw⁻ 30 (q14 c4) ∷
   rw⁻ 29 (q14 c4) ∷
   rw⁻ 28 (q14 c4) ∷
   rw⁻ 27 (q14 c4) ∷
   rw 39 (q18 c4) ∷
   rw 38 (q18 c4) ∷
   rw 37 (q17 c4) ∷
   rw 36 (q18 c4) ∷
   rw⁻ 35 (q14 c4) ∷
   rw⁻ 34 (q14 c4) ∷
   rw⁻ 33 (q14 c4) ∷
   rw⁻ 32 (q14 c4) ∷
   rw⁻ 31 (q14 c4) ∷
   rw⁻ 30 (q14 c4) ∷
   rw⁻ 43 (q19 c4) ∷
   rw⁻ 42 (q19 c4) ∷
   rw⁻ 41 (q19 c4) ∷
   rw⁻ 40 (q20 c4) ∷
   rw⁻ 39 (q19 c4) ∷
   rw⁻ 38 (q13 c4) ∷
   rw⁻ 37 (q13 c4) ∷
   rw⁻ 36 (q13 c4) ∷
   rw⁻ 35 (q13 c4) ∷
   rw⁻ 34 (q13 c4) ∷
   rw⁻ 33 (q13 c4) ∷
   rw⁻ 47 (q21 c4) ∷
   rw 46 (q22 c4) ∷
   rw 45 (q22 c4) ∷
   rw 44 (q22 c4) ∷
   rw 43 (q23 c4) ∷
   rw 42 (q22 c4) ∷
   rw⁻ 41 (q21 c4) ∷
   rw⁻ 40 (q21 c4) ∷
   rw⁻ 39 (q21 c4) ∷
   rw⁻ 38 (q21 c4) ∷
   rw⁻ 37 (q21 c4) ∷
   rw⁻ 36 (q21 c4) ∷
   rw⁻ 51 (q24 c4) ∷
   rw⁻ 50 (q13 c4) ∷
   rw⁻ 49 (q19 c4) ∷
   rw⁻ 48 (q19 c4) ∷
   rw⁻ 47 (q19 c4) ∷
   rw⁻ 46 (q20 c4) ∷
   rw⁻ 45 (q19 c4) ∷
   rw⁻ 44 (q13 c4) ∷
   rw⁻ 43 (q13 c4) ∷
   rw⁻ 42 (q13 c4) ∷
   rw⁻ 41 (q13 c4) ∷
   rw⁻ 40 (q13 c4) ∷
   rw⁻ 39 (q13 c4) ∷
   rw⁻ 55 (q21 c4) ∷
   rw 54 (q25 c4) ∷
   rw⁻ 53 (q21 c4) ∷
   rw 52 (q22 c4) ∷
   rw 51 (q22 c4) ∷
   rw 50 (q22 c4) ∷
   rw 49 (q23 c4) ∷
   rw 48 (q22 c4) ∷
   rw⁻ 47 (q21 c4) ∷
   rw⁻ 46 (q21 c4) ∷
   rw⁻ 45 (q21 c4) ∷
   rw⁻ 44 (q21 c4) ∷
   rw⁻ 43 (q21 c4) ∷
   rw⁻ 42 (q21 c4) ∷
   rw⁻ 59 (q24 c4) ∷
   rw⁻ 58 (q13 c4) ∷
   rw⁻ 57 (q24 c4) ∷
   rw⁻ 56 (q13 c4) ∷
   rw⁻ 55 (q19 c4) ∷
   rw⁻ 54 (q19 c4) ∷
   rw⁻ 53 (q19 c4) ∷
   rw⁻ 52 (q20 c4) ∷
   rw⁻ 51 (q19 c4) ∷
   rw⁻ 50 (q13 c4) ∷
   rw⁻ 49 (q13 c4) ∷
   rw⁻ 48 (q13 c4) ∷
   rw⁻ 47 (q13 c4) ∷
   rw⁻ 46 (q13 c4) ∷
   rw⁻ 45 (q13 c4) ∷ []) Eq.refl

-- split4[iI S2 S2 S2 CS12 K1 CS12 K1 CS12 CS12 CS12]: 66 steps
lem-split4iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-CS12-CS12 : Ws → ⟪ (ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-split4iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-CS12-CS12 c4 = derive (ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ []) (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 10 (q9 c4) ∷
   rw⁻ 9 (q9 c4) ∷
   rw⁻ 8 (q9 c4) ∷
   rw 7 (q10 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   rw 5 (q10 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   rw 3 (q11 c4) ∷
   rw 2 (q11 c4) ∷
   rw 1 (q11 c4) ∷
   rw⁻ 0 (q12 c4) ∷
   rw 3 (q17 c4) ∷
   rw 7 (q18 c4) ∷
   rw 6 (q17 c4) ∷
   rw 11 (q18 c4) ∷
   rw 10 (q18 c4) ∷
   rw 9 (q17 c4) ∷
   rw⁻ 15 (q19 c4) ∷
   rw⁻ 14 (q19 c4) ∷
   rw⁻ 13 (q19 c4) ∷
   rw⁻ 12 (q20 c4) ∷
   rw⁻ 19 (q21 c4) ∷
   rw 18 (q22 c4) ∷
   rw 17 (q22 c4) ∷
   rw 16 (q22 c4) ∷
   rw 15 (q23 c4) ∷
   rw⁻ 23 (q24 c4) ∷
   rw⁻ 22 (q13 c4) ∷
   rw⁻ 21 (q19 c4) ∷
   rw⁻ 20 (q19 c4) ∷
   rw⁻ 19 (q19 c4) ∷
   rw⁻ 18 (q20 c4) ∷
   rw⁻ 27 (q21 c4) ∷
   rw 26 (q25 c4) ∷
   rw⁻ 25 (q21 c4) ∷
   rw 24 (q22 c4) ∷
   rw 23 (q22 c4) ∷
   rw 22 (q22 c4) ∷
   rw 21 (q23 c4) ∷
   rw⁻ 31 (q24 c4) ∷
   rw⁻ 30 (q13 c4) ∷
   rw⁻ 29 (q24 c4) ∷
   rw⁻ 28 (q13 c4) ∷
   rw⁻ 27 (q19 c4) ∷
   rw⁻ 26 (q19 c4) ∷
   rw⁻ 25 (q19 c4) ∷
   rw⁻ 24 (q20 c4) ∷
   rw⁻ 35 (q13 c4) ∷
   rw⁻ 34 (q24 c4) ∷
   rw⁻ 33 (q13 c4) ∷
   rw⁻ 32 (q24 c4) ∷
   rw⁻ 31 (q13 c4) ∷
   rw⁻ 30 (q19 c4) ∷
   rw⁻ 29 (q19 c4) ∷
   rw⁻ 28 (q19 c4) ∷
   rw⁻ 27 (q20 c4) ∷
   rw⁻ 39 (q13 c4) ∷
   rw⁻ 38 (q13 c4) ∷
   rw⁻ 37 (q24 c4) ∷
   rw⁻ 36 (q13 c4) ∷
   rw⁻ 35 (q24 c4) ∷
   rw⁻ 34 (q13 c4) ∷
   rw⁻ 33 (q19 c4) ∷
   rw⁻ 32 (q19 c4) ∷
   rw⁻ 31 (q19 c4) ∷
   rw⁻ 30 (q20 c4) ∷ []) Eq.refl
