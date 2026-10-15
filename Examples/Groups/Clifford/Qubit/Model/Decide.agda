------------------------------------------------------------------------
-- Presentations of groups
--
-- Equality of stored matrices, decided as one boolean
--
-- `Eq.refl : A ≡ B` on two tries makes the conversion checker compare
-- them entry by entry, and an entry of a stored product is then
-- re-evaluated for every entry it is compared at.  `eqM A B ≡ true` is
-- one evaluation of one boolean; `eqM-sound` turns it into the
-- equation.  (The same device as Real-Clifford+CH's Semantics.Decide.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Clifford.Qubit.Model.Decide where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; T)
open import Data.Fin using (toℕ)
open import Data.Fin.Properties using (toℕ-injective)
open import Data.Nat using (ℕ ; _≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Product using (_×_ ; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import Notations using (₀ ; ₁₊)
open import Examples.Groups.Clifford.Qubit.Model.Algebra using (𝔽 ; Tab ; Mat ; mat)

private
  variable
    k : ℕ

eq𝔽 : 𝔽 → 𝔽 → Bool
eq𝔽 a b = toℕ a ≡ᵇ toℕ b

eqT : ∀ k {A : Set} → (A → A → Bool) → Tab k A → Tab k A → Bool
eqT ₀      e a        b        = e a b
eqT (₁₊ k) e (a , a′) (b , b′) = eqT k e a b ∧ eqT k e a′ b′

eqM : Mat k → Mat k → Bool
eqM {k} (mat s) (mat t) = eqT k (eqT k eq𝔽) s t

private
  ∧-true : ∀ {a b} → a ∧ b ≡ true → a ≡ true × b ≡ true
  ∧-true {true}  {true}  Eq.refl = Eq.refl , Eq.refl
  ∧-true {true}  {false} ()
  ∧-true {false} ()

eq𝔽-sound : ∀ a b → eq𝔽 a b ≡ true → a ≡ b
eq𝔽-sound a b e = toℕ-injective (≡ᵇ⇒≡ (toℕ a) (toℕ b) (Eq.subst T (Eq.sym e) tt))

eqT-sound : ∀ k {A : Set} (e : A → A → Bool) → (∀ a b → e a b ≡ true → a ≡ b) →
            ∀ s t → eqT k e s t ≡ true → s ≡ t
eqT-sound ₀      e ok a        b        h = ok a b h
eqT-sound (₁₊ k) e ok (a , a′) (b , b′) h with ∧-true {eqT k e a b} h
... | h₁ , h₂ = Eq.cong₂ _,_ (eqT-sound k e ok a b h₁) (eqT-sound k e ok a′ b′ h₂)

-- Give both matrices: `eqM` is a function, so they cannot be read back
-- off its type.
eqM-sound : (M N : Mat k) → eqM M N ≡ true → M ≡ N
eqM-sound {k} (mat s) (mat t) h =
  Eq.cong mat (eqT-sound k (eqT k eq𝔽) (eqT-sound k eq𝔽 eq𝔽-sound) s t h)
