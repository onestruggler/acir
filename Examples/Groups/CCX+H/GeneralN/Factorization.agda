------------------------------------------------------------------------
-- Presentations of groups
--
-- The group identity behind the constructive Schreier decoder.
-- If Z commutes with J = A K, put T = L A^-1 R and S = Z R.
-- Then L K R = T S^-1 J S.  In the application T and S are even
-- signed permutations and J is the mixed M X K primitive.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Word.Base using (Word ; WRel ; ε ; _•_)
open import Presentation.GroupLike using (Grouplike ; module Group-Lemmas)

module Examples.Groups.CCX+H.GeneralN.Factorization
  {Y : Set} (Γ : WRel Y) (gl : Grouplike Γ) where

open import Presentation.Base Γ
open import Presentation.Properties Γ using (word-setoid ; module Pattern-Assoc)
open Pattern-Assoc using (□ ; by-passoc)
open Group-Lemmas Γ gl
open import Relation.Binary.Reasoning.Setoid word-setoid
import Relation.Binary.PropositionalEquality as Eq

comm-product : ∀ {Z A B} → Z • A ≈ A • Z → Z • B ≈ B • Z →
  Z • (A • B) ≈ (A • B) • Z
comm-product {Z} {A} {B} za zb = begin
  Z • (A • B) ≈⟨ sym assoc ⟩
  (Z • A) • B ≈⟨ cong za refl ⟩
  (A • Z) • B ≈⟨ assoc ⟩
  A • (Z • B) ≈⟨ cong refl zb ⟩
  A • (B • Z) ≈⟨ sym assoc ⟩
  (A • B) • Z ∎

product-comm : ∀ {Z W A} → Z • A ≈ A • Z → W • A ≈ A • W →
  (Z • W) • A ≈ A • (Z • W)
product-comm za wa = sym (comm-product (sym za) (sym wa))

comm-conjugate : ∀ {Z J} → Z • J ≈ J • Z →
  (Z ⁻¹ • J) • Z ≈ J
comm-conjugate {Z} {J} zj = begin
  (Z ⁻¹ • J) • Z ≈⟨ assoc ⟩
  Z ⁻¹ • (J • Z) ≈⟨ cong refl (sym zj) ⟩
  Z ⁻¹ • (Z • J) ≈⟨ sym assoc ⟩
  (Z ⁻¹ • Z) • J ≈⟨ cong inverseˡ refl ⟩
  ε • J ≈⟨ left-unit ⟩
  J ∎

factor : ∀ (L R A K Z : Word Y) →
  Z • (A • K) ≈ (A • K) • Z →
  (L • K) • R ≈
    (((L • A ⁻¹) • R) • (Z • R) ⁻¹) • ((A • K) • (Z • R))
factor L R A K Z commutes = sym (begin
  (((L • A ⁻¹) • R) • (Z • R) ⁻¹) • ((A • K) • (Z • R))
    ≈⟨ by-passoc
      ((((□ • □) • □) • (□ • □)) • ((□ • □) • (□ • □)))
      ((□ • □) • ((□ • □) • ((□ • (□ • □)) • □)) • □) Eq.refl ⟩
  (L • A ⁻¹) • ((R • R ⁻¹) • ((Z ⁻¹ • (A • K)) • Z)) • R
    ≈⟨ cong refl (cong (cong inverseʳ refl) refl) ⟩
  (L • A ⁻¹) • (ε • ((Z ⁻¹ • (A • K)) • Z)) • R
    ≈⟨ cong refl (cong left-unit refl) ⟩
  (L • A ⁻¹) • ((Z ⁻¹ • (A • K)) • Z) • R
    ≈⟨ cong refl (cong (comm-conjugate commutes) refl) ⟩
  (L • A ⁻¹) • (A • K) • R
    ≈⟨ assoc ⟩
  L • (A ⁻¹ • ((A • K) • R))
    ≈⟨ cong refl (cong refl assoc) ⟩
  L • (A ⁻¹ • (A • (K • R)))
    ≈⟨ cong refl (sym assoc) ⟩
  L • ((A ⁻¹ • A) • (K • R))
    ≈⟨ cong refl (cong inverseˡ refl) ⟩
  L • (ε • (K • R))
    ≈⟨ cong refl left-unit ⟩
  L • K • R
    ≈⟨ sym assoc ⟩
  (L • K) • R ∎)
