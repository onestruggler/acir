{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D189 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0885 ; wl0886 ; wl0887 ; wl0888 ; wl0893 ; wl0894 ; wl0895 ; wl0896 ; wl0897)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-F4-CS01ᵖ0∣iIᵖ1 ; lem-F4-K1ᵖ0∣CS12ᵖ1 ; lem-F4-S2ᵖ0∣CS12ᵖ1 ; lem-F4-iIᵖ0∣CS12ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D173 using (lem-F4-CS01ᵖ0∣CS01ᵖ1 ; lem-F4-CS01ᵖ0∣K1ᵖ1 ; lem-F4-CS01ᵖ0∣S0ᵖ1 ; lem-F4-CS01ᵖ0∣S1ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D177 using (lem-F4-CS12ᵖ0∣S2ᵖ1 ; lem-F4-CS12ᵖ0∣iIᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D178 using (lem-F4-CS12ᵖ0∣K1ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D179 using (lem-F4-CS12ᵖ0∣CS12ᵖ1 ; lem-F5-CS12)
open import Examples.Groups.Clifford+CS.Five.D.D188 using (lem-DB4K1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-CS01-CS01-S1-S1-S1-part0)
open import Examples.Groups.Clifford+CS.Five.D.TR using (tr01)
-- DB4[K1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 S0 iI S0 S0 S0 CS01 K1 CS01 K1 CS01 S1 S1 S1 S1 S1 S1 S1 S1 S1 iI S0 S0 S0 CS01 K1 CS01 K1 CS01 CS01 CS01 S1 S1 S1] part1: 34 steps
lem-DB4K1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-CS01-CS01-S1-S1-S1-part1 : Ws → ⟪ (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
lem-DB4K1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-CS01-CS01-S1-S1-S1-part1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b0 = at 85 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS01ᵖ0∣iIᵖ1 c4)) ▸
       at 84 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 83 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 82 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 81 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 80 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 79 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 78 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸ done

  b1 : Chain (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b1 = at 105 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 104 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 103 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 102 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 101 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 100 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 99 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 98 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸ done

  b2 : Chain (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b2 = at 97 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 96 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 95 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS01ᵖ0∣K1ᵖ1 c4)) ▸
       at 94 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 93 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS01ᵖ0∣K1ᵖ1 c4)) ▸
       at 92 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 91 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 90 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸ done

  b3 : Chain (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b3 = at 89 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 88 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS01ᵖ0∣iIᵖ1 c4)) ▸
       at 87 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 86 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 85 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 84 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 83 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 82 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸ done

  b4 : Chain (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b4 = at 81 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 3 81 [] (tr01 c4) ▸ done


-- DB4[K1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 S0 iI S0 S0 S0 CS01 K1 CS01 K1 CS01 S1 S1 S1 S1 S1 S1 S1 S1 S1 iI S0 S0 S0 CS01 K1 CS01 K1 CS01 CS01 CS01 S1 S1 S1]: 2 steps
lem-DB4K1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-CS01-CS01-S1-S1-S1 : Ws → ⟪ (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
lem-DB4K1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-CS01-CS01-S1-S1-S1 c4 = run b0
  where
  b0 : Chain (CK41 ∷ CCZ014 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b0 = at 0 41 (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (lem-DB4K1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-CS01-CS01-S1-S1-S1-part0 c4) ▸
       at 0 123 (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (lem-DB4K1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-CS01-CS01-S1-S1-S1-part1 c4) ▸ done


-- split4[CS12 CS12 CS12 CS12 CS12 CS12 S2 iI S2 S2 S2 CS12 K1 CS12 K1 CS12]: 136 steps
lem-split4CS12-CS12-CS12-CS12-CS12-CS12-S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12 : Ws → ⟪ (CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-split4CS12-CS12-CS12-CS12-CS12-CS12-S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (run b16))))))))))))))))
  where
  b0 : Chain (CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ []) (CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ ι ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 15 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-CS12 c4)) ▸
       at 14 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0885 (lit c4)) ▸
       at 13 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-CS12 c4)) ▸
       at 12 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0885 (lit c4)) ▸
       at 11 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-CS12 c4)) ▸
       at 10 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0893 (lit c4)) ▸
       at 9 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0893 (lit c4)) ▸
       at 8 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0893 (lit c4)) ▸ done

  b1 : Chain (CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ ι ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ S4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b1 = at 7 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl0886 (lit c4))) ▸
       at 6 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0893 (lit c4)) ▸
       at 5 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-CS12 c4)) ▸
       at 4 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-CS12 c4)) ▸
       at 3 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-CS12 c4)) ▸
       at 2 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-CS12 c4)) ▸
       at 1 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-CS12 c4)) ▸
       at 0 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-CS12 c4)) ▸ done

  b2 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ S4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ S4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b2 = at 3 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 7 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 6 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 11 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 10 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 9 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 15 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 14 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸ done

  b3 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ S4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CS24 ∷ X4 ∷ S4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b3 = at 13 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 12 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 19 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 18 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 17 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 16 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 15 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 23 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)) ▸ done

  b4 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CS24 ∷ X4 ∷ S4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b4 = at 22 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)) ▸
       at 21 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)) ▸
       at 20 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)) ▸
       at 19 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)) ▸
       at 18 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)) ▸
       at 27 4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (wl0894 (lit c4)) ▸
       at 26 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-iIᵖ0∣CS12ᵖ1 c4)) ▸
       at 25 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-iIᵖ0∣CS12ᵖ1 c4)) ▸ done

  b5 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b5 = at 24 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-iIᵖ0∣CS12ᵖ1 c4)) ▸
       at 23 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-iIᵖ0∣CS12ᵖ1 c4)) ▸
       at 22 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-iIᵖ0∣CS12ᵖ1 c4)) ▸
       at 21 4 (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-iIᵖ0∣CS12ᵖ1 c4)) ▸
       at 31 4 (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (wl0895 (lit c4)) ▸
       at 30 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0896 (lit c4)) ▸
       at 29 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)) ▸
       at 28 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)) ▸ done

  b6 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b6 = at 27 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)) ▸
       at 26 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)) ▸
       at 25 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)) ▸
       at 24 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)) ▸
       at 35 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0896 (lit c4)) ▸
       at 34 4 (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (wl0895 (lit c4)) ▸
       at 33 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0896 (lit c4)) ▸
       at 32 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)) ▸ done

  b7 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b7 = at 31 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)) ▸
       at 30 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)) ▸
       at 29 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)) ▸
       at 28 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)) ▸
       at 27 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)) ▸
       at 39 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0896 (lit c4)) ▸
       at 38 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0896 (lit c4)) ▸
       at 37 4 (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (wl0895 (lit c4)) ▸ done

  b8 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b8 = at 36 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0896 (lit c4)) ▸
       at 35 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)) ▸
       at 34 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)) ▸
       at 33 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)) ▸
       at 32 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)) ▸
       at 31 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)) ▸
       at 30 4 (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-S2ᵖ0∣CS12ᵖ1 c4)) ▸
       at 43 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸ done

  b9 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b9 = at 42 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 41 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 40 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS12ᵖ0∣iIᵖ1 c4)) ▸
       at 39 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 38 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 37 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 36 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 35 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸ done

  b10 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b10 = at 34 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 33 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 47 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)) ▸
       at 46 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸
       at 45 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸
       at 44 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸
       at 43 4 (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (wl0887 (lit c4)) ▸
       at 42 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸ done

  b11 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b11 = at 41 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)) ▸
       at 40 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)) ▸
       at 39 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)) ▸
       at 38 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)) ▸
       at 37 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)) ▸
       at 36 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)) ▸
       at 51 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS12ᵖ0∣K1ᵖ1 c4)) ▸
       at 50 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸ done

  b12 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b12 = at 49 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 48 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 47 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 46 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS12ᵖ0∣iIᵖ1 c4)) ▸
       at 45 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 44 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 43 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 42 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸ done

  b13 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b13 = at 41 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 40 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 39 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 55 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)) ▸
       at 54 4 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0888 (lit c4)) ▸
       at 53 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)) ▸
       at 52 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸
       at 51 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸ done

  b14 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b14 = at 50 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸
       at 49 4 (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (wl0887 (lit c4)) ▸
       at 48 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸
       at 47 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)) ▸
       at 46 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)) ▸
       at 45 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)) ▸
       at 44 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)) ▸
       at 43 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)) ▸ done

  b15 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b15 = at 42 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)) ▸
       at 59 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS12ᵖ0∣K1ᵖ1 c4)) ▸
       at 58 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 57 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS12ᵖ0∣K1ᵖ1 c4)) ▸
       at 56 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 55 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 54 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 53 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸ done

  b16 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b16 = at 52 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS12ᵖ0∣iIᵖ1 c4)) ▸
       at 51 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 50 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 49 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 48 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 47 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 46 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 45 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸ done


-- split4[iI S2 S2 S2 CS12 K1 CS12 K1 CS12 CS12 CS12]: 66 steps
lem-split4iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-CS12-CS12 : Ws → ⟪ (ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-split4iI-S2-S2-S2-CS12-K1-CS12-K1-CS12-CS12-CS12 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (run b8))))))))
  where
  b0 : Chain (ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ []) (ι ∷ S2 ∷ S2 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 10 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-CS12 c4)) ▸
       at 9 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-CS12 c4)) ▸
       at 8 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-CS12 c4)) ▸
       at 7 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0885 (lit c4)) ▸
       at 6 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-CS12 c4)) ▸
       at 5 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0885 (lit c4)) ▸
       at 4 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-CS12 c4)) ▸
       at 3 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0893 (lit c4)) ▸ done

  b1 : Chain (ι ∷ S2 ∷ S2 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b1 = at 2 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0893 (lit c4)) ▸
       at 1 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0893 (lit c4)) ▸
       at 0 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl0886 (lit c4))) ▸
       at 3 4 (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (wl0895 (lit c4)) ▸
       at 7 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0896 (lit c4)) ▸
       at 6 4 (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (wl0895 (lit c4)) ▸
       at 11 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0896 (lit c4)) ▸
       at 10 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0896 (lit c4)) ▸ done

  b2 : Chain (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b2 = at 9 4 (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (wl0895 (lit c4)) ▸
       at 15 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 14 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 13 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 12 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS12ᵖ0∣iIᵖ1 c4)) ▸
       at 19 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)) ▸
       at 18 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸
       at 17 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸ done

  b3 : Chain (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b3 = at 16 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸
       at 15 4 (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (wl0887 (lit c4)) ▸
       at 23 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS12ᵖ0∣K1ᵖ1 c4)) ▸
       at 22 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 21 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 20 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 19 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 18 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS12ᵖ0∣iIᵖ1 c4)) ▸ done

  b4 : Chain (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b4 = at 27 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)) ▸
       at 26 4 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0888 (lit c4)) ▸
       at 25 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)) ▸
       at 24 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸
       at 23 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸
       at 22 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸
       at 21 4 (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (wl0887 (lit c4)) ▸
       at 31 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS12ᵖ0∣K1ᵖ1 c4)) ▸ done

  b5 : Chain (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b5 = at 30 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 29 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS12ᵖ0∣K1ᵖ1 c4)) ▸
       at 28 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 27 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 26 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 25 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 24 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS12ᵖ0∣iIᵖ1 c4)) ▸
       at 35 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸ done

  b6 : Chain (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b6 = at 34 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS12ᵖ0∣K1ᵖ1 c4)) ▸
       at 33 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 32 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS12ᵖ0∣K1ᵖ1 c4)) ▸
       at 31 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 30 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 29 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 28 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 27 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS12ᵖ0∣iIᵖ1 c4)) ▸ done

  b7 : Chain (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ [])
  b7 = at 39 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 38 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 37 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS12ᵖ0∣K1ᵖ1 c4)) ▸
       at 36 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 35 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS12ᵖ0∣K1ᵖ1 c4)) ▸
       at 34 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 33 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 32 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸ done

  b8 : Chain (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ [])
  b8 = at 31 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 30 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS12ᵖ0∣iIᵖ1 c4)) ▸ done

