------------------------------------------------------------------------
-- Presentations of groups
--
-- L2-CZ, the L' 1 component (the j=1 boxes).
--
-- The inj2 half of the old lemma-dir-and-l': three short clauses, the
-- A-box ones, discharged by lemma-A-CZ-1 and lemma-A-CZ-2.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe --call-by-name --termination-depth=4 #-}


open import Relation.Binary.PropositionalEquality using (_≡_ ; _≢_) renaming ([_] to [_]')
import Relation.Binary.Reasoning.Setoid as SR
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)


open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Product.Relation.Binary.Pointwise.NonDependent using (≡×≡⇒≡)
open import Data.Nat hiding (_^_ ; _+_ ; _*_ ; _≟_)
--open import Data.List using () hiding ([_] ; _++_ ; last ; head ; tail ; _∷ʳ_)
open import Data.Vec
open import Data.Fin hiding (_+_ ; _-_ ; _≤_ ; _<_)

open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Empty using (⊥-elim)

open import Word.Base hiding (wfoldl ; _^'_)
import Presentation.Base as PB
import Presentation.Properties as PP
open import Notations



open import Presentation.GroupLike
open import Data.Nat.Primality




module Examples.Groups.Symplectic.BR.Two.L2-CZ.Right (p-2 : ℕ) (p-prime : Prime (2+ p-2)) where

open import Examples.Groups.Symplectic.BR.Two.L2-CZ.Base p-2 p-prime

l'-of₂ : L' 1 → L' 2 ⊎ L' 1

-- L' 1 (= Vec B 0 × A) inputs (the j=1 boxes)
l'-of₂ ([] , (a@₀ , b@(₁₊ _)) , nzp) = inj₂ ([] , (a , b) , nzp)
l'-of₂ ([] , (a@(₁₊ _) , b) , nz)    = inj₁ (((a , b) ∷ []) , ((₀ , - a) , nzp))
  where
  nzp : (₀ , - a) ≢ (₀ , ₀)
  nzp = aux-b≠0⇒ab≠0 ₀ (- a) ((-' (a , λ ())) .proj₂)
l'-of₂ ([] , (a@₀ , b@₀) , nz)       = ⊥-elim (nz auto)




dir-of₂ : L' 1 → Word (Gen 2)

-- L' 1 (= Vec B 0 × A) inputs (j=1)
dir-of₂ ([] , (a@₀ , b@(₁₊ _)) , nzx) =   CZ^ b⁻¹
  where b⁻¹ = ((b , λ ()) ⁻¹) .proj₁
dir-of₂ ([] , (a@(₁₊ _) , b) , nzx)   =   H • CZ^ a⁻¹ • H ^ 3
  where a⁻¹ = ((a , λ ()) ⁻¹) .proj₁
dir-of₂ ([] , (a@₀ , b@₀) , nzx)      =   ⊥-elim (nzx auto)


------------------------------------------------------------------------
-- Interpretation of the L' 2 ⊎ L' 1 output
--
-- Chosen so that ⟦ l'-of₂ l ⟧ is definitionally the old [ l'-of₂ l ]ˡ:
-- the inj₁ (L' 2) branch is [_]ˡ', and the inj₂ (L' 1 = A) branch is
-- the upper-wire A-box, matching the j=1 collapse in L-CZ.

lemma₂ : ∀ (l : L' 1) →
  let
  dir = dir-of₂ l
  l' = l'-of₂ l
  in

  intp (inj₂ l) • CZ ≈ dir • intp l'

lemma₂ l@([] , x@((a@₀ , b@(₁₊ _)) , nzx)) = begin
  intp (inj₂ l) • CZ ≈⟨ cleft left-unit ⟩
  [ x ]ᵃ ↑ • CZ ≈⟨ lemma-A-CZ-1 (b , (λ ())) ⟩
  CZ^ b⁻¹ • [ x ]ᵃ ↑ ≈⟨ cright sym left-unit ⟩
  dir • intp l' ∎
  where
  b⁻¹ = ((b , λ ()) ⁻¹) .proj₁
  l' = l'-of₂ l
  dir = dir-of₂ l
lemma₂ l@([] , x@((a@(₁₊ _) , b) , nzx)) = begin
  intp (inj₂ l) • CZ ≈⟨ cleft left-unit ⟩
  [ x ]ᵃ ↑ • CZ ≈⟨ lemma-A-CZ-2 (a , λ ()) b ⟩
  dir • [ a , b ]ᵇ • [ (₀ , - a) , nzx' ]ᵃ ≈⟨ cright sym (trans assoc left-unit) ⟩
  dir • intp l' ∎
  where
  a* : ℤ* ₚ
  a* = (a , λ ())
  a⁻¹ = (a* ⁻¹) .proj₁
  nzx' = aux-b≠0⇒ab≠0 ₀ (- a) ((-' (a , λ ())) .proj₂)
  dir : Word (Gen 2)
  dir = (H • CZ^ a⁻¹ • H ^ 3)
  l' : L' 2 ⊎ L' 1
  l' = inj₁ (((a , b) ∷ []) , ((₀ , - a) , nzx'))
lemma₂ ([] , (a@₀ , b@₀) , nzx) = ⊥-elim (nzx auto)

