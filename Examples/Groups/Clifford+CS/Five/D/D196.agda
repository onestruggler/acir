{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D196 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0885 ; wl0886 ; wl0887 ; wl0888 ; wl0889 ; wl0890 ; wl0891 ; wl0892 ; wl0893 ; wl0894 ; wl0895 ; wl0896 ; wl0897 ; wp0462 ; wp0463 ; wp0464 ; wp0465 ; wp0466 ; wp0467)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D171 using (lem-F4-iIᵖ0∣CS01ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D172 using (lem-F4-CS01ᵖ0∣iIᵖ1 ; lem-F4-K1ᵖ0∣CS01ᵖ1 ; lem-F4-K1ᵖ0∣CS12ᵖ1 ; lem-F4-S0ᵖ0∣CS01ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D173 using (lem-F4-CS01ᵖ0∣CS01ᵖ1 ; lem-F4-CS01ᵖ0∣K1ᵖ1 ; lem-F4-CS01ᵖ0∣S0ᵖ1 ; lem-F4-CS01ᵖ0∣S1ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D177 using (lem-F4-CS12ᵖ0∣S2ᵖ1 ; lem-F4-CS12ᵖ0∣iIᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D178 using (lem-F4-CS12ᵖ0∣K1ᵖ1)
open import Examples.Groups.Clifford+CS.Five.D.D179 using (lem-F4-CS12ᵖ0∣CS12ᵖ1 ; lem-F5-CS12)
open import Examples.Groups.Clifford+CS.Five.D.D195 using (lem-split4S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01 ; lem-split4iI-S0-S0-S0-CS01-K1-CS01-K1-CS01)
open import Examples.Groups.Clifford+CS.Five.D.TR using (tr05)
-- DB4[K1 S0 iI S0 S0 S0 CS01 K1 CS01 K1 CS01 S1 S1 S1 S1 S1 S1 S1 S1 S1 iI S0 S0 S0 CS01 K1 CS01 K1 CS01 S1 S1 S1]: 174 steps
lem-DB4K1-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1 : Ws → ⟪ (CK41 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ
lem-DB4K1-S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1-S1-S1-S1-S1-S1-S1-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01-S1-S1-S1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (run b21)))))))))))))))))))))
  where
  b0 : Chain (CK41 ∷ S0 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ ι ∷ S0 ∷ S0 ∷ S0 ∷ CS01 ∷ K1 ∷ CS01 ∷ K1 ∷ CS01 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ S4 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b0 = at 1 10 (X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (lem-split4S0-iI-S0-S0-S0-CS01-K1-CS01-K1-CS01 c4) ▸
       at 50 9 (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ []) (lem-split4iI-S0-S0-S0-CS01-K1-CS01-K1-CS01 c4) ▸
       at 49 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (wl0889 (lit c4)) ▸
       at 48 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (wl0889 (lit c4)) ▸
       at 47 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (wl0889 (lit c4)) ▸
       at 46 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (wl0889 (lit c4)) ▸
       at 45 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (wl0889 (lit c4)) ▸
       at 44 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (wl0889 (lit c4)) ▸ done

  b1 : Chain (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ S4 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b1 = at 43 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (wl0889 (lit c4)) ▸
       at 42 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (wl0889 (lit c4)) ▸
       at 41 4 (X4 ∷ S4 ∷ X4 ∷ CS14 ∷ []) (wl0889 (lit c4)) ▸
       at 40 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-iIᵖ0∣CS01ᵖ1 c4)) ▸
       at 39 4 (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (wl0890 (lit c4)) ▸
       at 38 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-iIᵖ0∣CS01ᵖ1 c4)) ▸
       at 37 4 (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (wl0890 (lit c4)) ▸
       at 36 4 (X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-iIᵖ0∣CS01ᵖ1 c4)) ▸ done

  b2 : Chain (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X4 ∷ S4 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b2 = at 35 4 (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (wp0462 c4) ▸
       at 34 4 (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (wp0462 c4) ▸
       at 33 4 (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (wp0462 c4) ▸
       at 32 4 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (wl0891 (lit c4)) ▸
       at 31 4 (X4 ∷ S4 ∷ X4 ∷ CS04 ∷ []) (wp0462 c4) ▸
       at 52 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸
       at 51 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸
       at 50 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸ done

  b3 : Chain (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b3 = at 49 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸
       at 48 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸
       at 47 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸
       at 46 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸
       at 45 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸
       at 44 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸
       at 43 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 42 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (wp0467 c4) ▸ done

  b4 : Chain (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b4 = at 41 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 40 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (wp0467 c4) ▸
       at 39 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 38 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸
       at 37 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸
       at 36 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸
       at 35 4 (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (wp0463 c4) ▸
       at 34 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸ done

  b5 : Chain (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b5 = at 55 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸
       at 54 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸
       at 53 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸
       at 52 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸
       at 51 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸
       at 50 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸
       at 49 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸
       at 48 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸ done

  b6 : Chain (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b6 = at 47 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸
       at 46 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 45 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (wp0467 c4) ▸
       at 44 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 43 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (wp0467 c4) ▸
       at 42 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 41 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸
       at 40 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸ done

  b7 : Chain (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b7 = at 39 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸
       at 38 4 (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (wp0463 c4) ▸
       at 37 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸
       at 58 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸
       at 57 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸
       at 56 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸
       at 55 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸
       at 54 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸ done

  b8 : Chain (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b8 = at 53 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸
       at 52 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸
       at 51 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸
       at 50 4 (X4 ∷ CS04 ∷ X4 ∷ CS14 ∷ []) (wp0466 c4) ▸
       at 49 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 48 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (wp0467 c4) ▸
       at 47 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 46 4 (X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ []) (wp0467 c4) ▸ done

  b9 : Chain (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ X4 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b9 = at 45 4 (X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-S0ᵖ0∣CS01ᵖ1 c4)) ▸
       at 44 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸
       at 43 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸
       at 42 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸
       at 41 4 (X4 ∷ CS04 ∷ X4 ∷ S4 ∷ []) (wp0463 c4) ▸
       at 40 4 (X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ []) (wp0464 c4) ▸
       at 61 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 60 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸ done

  b10 : Chain (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b10 = at 59 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 58 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 57 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 56 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 55 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 54 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 53 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 52 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸ done

  b11 : Chain (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b11 = at 51 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS01ᵖ0∣K1ᵖ1 c4)) ▸
       at 50 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 49 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS01ᵖ0∣K1ᵖ1 c4)) ▸
       at 48 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 47 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 46 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 45 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 44 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS01ᵖ0∣iIᵖ1 c4)) ▸ done

  b12 : Chain (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b12 = at 43 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 64 4 (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (wl0892 (lit c4)) ▸
       at 63 4 (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (wl0892 (lit c4)) ▸
       at 62 4 (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (wl0892 (lit c4)) ▸
       at 61 4 (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (wl0892 (lit c4)) ▸
       at 60 4 (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (wl0892 (lit c4)) ▸
       at 59 4 (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (wl0892 (lit c4)) ▸
       at 58 4 (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (wl0892 (lit c4)) ▸ done

  b13 : Chain (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b13 = at 57 4 (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (wl0892 (lit c4)) ▸
       at 56 4 (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (wl0892 (lit c4)) ▸
       at 55 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸
       at 54 4 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0888 (lit c4)) ▸
       at 53 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸
       at 52 4 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0888 (lit c4)) ▸
       at 51 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸
       at 50 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸ done

  b14 : Chain (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b14 = at 49 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸
       at 48 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸
       at 47 4 (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (wl0887 (lit c4)) ▸
       at 46 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸
       at 67 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 66 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 65 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 64 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸ done

  b15 : Chain (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b15 = at 63 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 62 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 61 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 60 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 59 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 58 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 57 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS01ᵖ0∣K1ᵖ1 c4)) ▸
       at 56 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸ done

  b16 : Chain (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b16 = at 55 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS01ᵖ0∣K1ᵖ1 c4)) ▸
       at 54 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 53 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 52 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 51 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 50 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS01ᵖ0∣iIᵖ1 c4)) ▸
       at 49 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 70 4 (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (wl0892 (lit c4)) ▸ done

  b17 : Chain (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b17 = at 69 4 (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (wl0892 (lit c4)) ▸
       at 68 4 (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (wl0892 (lit c4)) ▸
       at 67 4 (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (wl0892 (lit c4)) ▸
       at 66 4 (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (wl0892 (lit c4)) ▸
       at 65 4 (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (wl0892 (lit c4)) ▸
       at 64 4 (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (wl0892 (lit c4)) ▸
       at 63 4 (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (wl0892 (lit c4)) ▸
       at 62 4 (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (wl0892 (lit c4)) ▸ done

  b18 : Chain (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b18 = at 61 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸
       at 60 4 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0888 (lit c4)) ▸
       at 59 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸
       at 58 4 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0888 (lit c4)) ▸
       at 57 4 (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS01ᵖ1 c4)) ▸
       at 56 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸
       at 55 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸
       at 54 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸ done

  b19 : Chain (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ S4 ∷ X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b19 = at 53 4 (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (wl0887 (lit c4)) ▸
       at 52 4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (wp0465 c4) ▸
       at 73 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 72 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 71 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 70 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 69 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 68 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸ done

  b20 : Chain (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b20 = at 67 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 66 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 65 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS14 ∷ []) (sym (lem-F4-CS01ᵖ0∣S1ᵖ1 c4)) ▸
       at 64 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 63 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS01ᵖ0∣K1ᵖ1 c4)) ▸
       at 62 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸
       at 61 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS01ᵖ0∣K1ᵖ1 c4)) ▸
       at 60 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F4-CS01ᵖ0∣CS01ᵖ1 c4)) ▸ done

  b21 : Chain (CK41 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) (CK41 ∷ CS04 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ S4 ∷ CS04 ∷ CS04 ∷ CS04 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ CS14 ∷ CS14 ∷ CS14 ∷ [])
  b21 = at 59 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 58 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 57 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 56 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS01ᵖ0∣iIᵖ1 c4)) ▸
       at 55 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CS04 ∷ []) (sym (lem-F4-CS01ᵖ0∣S0ᵖ1 c4)) ▸
       at 1 57 [] (tr05 c4) ▸ done


-- split4[S2 iI S2 S2 S2 CS12 K1 CS12 K1 CS12]: 55 steps
lem-split4S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12 : Ws → ⟪ (S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-split4S2-iI-S2-S2-S2-CS12-K1-CS12-K1-CS12 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (run b6))))))
  where
  b0 : Chain (S2 ∷ ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ []) (S2 ∷ ι ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 9 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-CS12 c4)) ▸
       at 8 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0885 (lit c4)) ▸
       at 7 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-CS12 c4)) ▸
       at 6 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0885 (lit c4)) ▸
       at 5 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-CS12 c4)) ▸
       at 4 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0893 (lit c4)) ▸
       at 3 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0893 (lit c4)) ▸
       at 2 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0893 (lit c4)) ▸ done

  b1 : Chain (S2 ∷ ι ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b1 = at 1 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl0886 (lit c4))) ▸
       at 0 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0893 (lit c4)) ▸
       at 3 4 (X4 ∷ S4 ∷ X4 ∷ CS24 ∷ []) (wl0894 (lit c4)) ▸
       at 7 4 (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (wl0895 (lit c4)) ▸
       at 6 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0896 (lit c4)) ▸
       at 11 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0896 (lit c4)) ▸
       at 10 4 (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (wl0895 (lit c4)) ▸
       at 9 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0896 (lit c4)) ▸ done

  b2 : Chain (X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b2 = at 15 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0896 (lit c4)) ▸
       at 14 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0896 (lit c4)) ▸
       at 13 4 (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (wl0895 (lit c4)) ▸
       at 12 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0896 (lit c4)) ▸
       at 19 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 18 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 17 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 16 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS12ᵖ0∣iIᵖ1 c4)) ▸ done

  b3 : Chain (X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b3 = at 15 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 23 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)) ▸
       at 22 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸
       at 21 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸
       at 20 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸
       at 19 4 (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (wl0887 (lit c4)) ▸
       at 18 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸
       at 27 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS12ᵖ0∣K1ᵖ1 c4)) ▸ done

  b4 : Chain (X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b4 = at 26 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 25 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 24 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 23 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 22 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS12ᵖ0∣iIᵖ1 c4)) ▸
       at 21 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 31 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)) ▸
       at 30 4 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0888 (lit c4)) ▸ done

  b5 : Chain (X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b5 = at 29 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)) ▸
       at 28 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸
       at 27 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸
       at 26 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸
       at 25 4 (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (wl0887 (lit c4)) ▸
       at 24 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸
       at 35 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS12ᵖ0∣K1ᵖ1 c4)) ▸
       at 34 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸ done

  b6 : Chain (X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b6 = at 33 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS12ᵖ0∣K1ᵖ1 c4)) ▸
       at 32 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 31 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 30 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 29 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 28 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS12ᵖ0∣iIᵖ1 c4)) ▸
       at 27 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸ done


-- split4[iI S2 S2 S2 CS12 K1 CS12 K1 CS12]: 45 steps
lem-split4iI-S2-S2-S2-CS12-K1-CS12-K1-CS12 : Ws → ⟪ (ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-split4iI-S2-S2-S2-CS12-K1-CS12-K1-CS12 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (ι ∷ S2 ∷ S2 ∷ S2 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ []) (ι ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b0 = at 8 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-CS12 c4)) ▸
       at 7 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0885 (lit c4)) ▸
       at 6 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-CS12 c4)) ▸
       at 5 1 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0885 (lit c4)) ▸
       at 4 1 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F5-CS12 c4)) ▸
       at 3 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0893 (lit c4)) ▸
       at 2 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0893 (lit c4)) ▸
       at 1 1 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0893 (lit c4)) ▸ done

  b1 : Chain (ι ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b1 = at 0 1 (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (sym (wl0886 (lit c4))) ▸
       at 3 4 (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (wl0895 (lit c4)) ▸
       at 7 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0896 (lit c4)) ▸
       at 6 4 (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (wl0895 (lit c4)) ▸
       at 11 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0896 (lit c4)) ▸
       at 10 4 (X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ []) (wl0896 (lit c4)) ▸
       at 9 4 (X4 ∷ CS24 ∷ X4 ∷ S4 ∷ []) (wl0895 (lit c4)) ▸
       at 15 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸ done

  b2 : Chain (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b2 = at 14 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 13 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 12 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS12ᵖ0∣iIᵖ1 c4)) ▸
       at 19 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)) ▸
       at 18 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸
       at 17 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸
       at 16 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸
       at 15 4 (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (wl0887 (lit c4)) ▸ done

  b3 : Chain (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ [])
  b3 = at 23 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS12ᵖ0∣K1ᵖ1 c4)) ▸
       at 22 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 21 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 20 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 19 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 18 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS12ᵖ0∣iIᵖ1 c4)) ▸
       at 27 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)) ▸
       at 26 4 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (wl0888 (lit c4)) ▸ done

  b4 : Chain (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b4 = at 25 4 (X4 ∷ CK41 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-K1ᵖ0∣CS12ᵖ1 c4)) ▸
       at 24 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸
       at 23 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸
       at 22 4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (wl0897 (lit c4)) ▸
       at 21 4 (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (wl0887 (lit c4)) ▸
       at 31 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS12ᵖ0∣K1ᵖ1 c4)) ▸
       at 30 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 29 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ []) (sym (lem-F4-CS12ᵖ0∣K1ᵖ1 c4)) ▸ done

  b5 : Chain (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ CS24 ∷ CS24 ∷ CS24 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ [])
  b5 = at 28 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (sym (lem-F4-CS12ᵖ0∣CS12ᵖ1 c4)) ▸
       at 27 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 26 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 25 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ []) (sym (lem-F4-CS12ᵖ0∣S2ᵖ1 c4)) ▸
       at 24 4 (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ S4 ∷ []) (sym (lem-F4-CS12ᵖ0∣iIᵖ1 c4)) ▸ done

