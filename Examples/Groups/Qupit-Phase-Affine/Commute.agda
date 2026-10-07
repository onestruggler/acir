------------------------------------------------------------------------
-- Presentations of groups
--
-- Commuting words
--
-- m ⊢ a ∥ b says that a and b commute.  Commutation passes to products
-- on either side and to iterates, and conjugation by an invertible word
-- commutes with taking iterates (conj-pow).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Commute
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) where

open import Data.Fin.Base using (toℕ)
open import Data.Nat.Base using (zero ; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_ ; _^_)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime using (F)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Reasoning p-2 p-prime lv
open import Examples.Groups.Qupit-Phase-Affine.Powers p-2 p-prime lv

infix 4 _⊢_∥_
_⊢_∥_ : (m : ℕ) → Circuit m → Circuit m → Set
m ⊢ a ∥ b = m ⊢ a • b ≈ b • a

module _ {m : ℕ} where

  open Width m

  ∥-sym : {a b : Circuit m} → m ⊢ a ∥ b → m ⊢ b ∥ a
  ∥-sym e = sym e

  -- a past a product.
  ∥-• : {a b c : Circuit m} → m ⊢ a ∥ b → m ⊢ a ∥ c → m ⊢ a ∥ b • c
  ∥-• e f = trans (slide e f) refl

  -- A product past a.
  •-∥ : {a b c : Circuit m} → m ⊢ a ∥ c → m ⊢ b ∥ c → m ⊢ (a • b) ∥ c
  •-∥ e f = ∥-sym (∥-• (∥-sym e) (∥-sym f))

  ∥-^ : {a b : Circuit m} (k : ℕ) → m ⊢ a ∥ b → m ⊢ (a ^ k) ∥ b
  ∥-^ k e = Pow.pow-comm m k e

  ∥-^ᶠ : {a b : Circuit m} (k : F) → m ⊢ a ∥ b → m ⊢ (a ^ᶠ k) ∥ b
  ∥-^ᶠ k = ∥-^ (toℕ k)

  ∥-^ᶠ² : {a b : Circuit m} (k l : F) → m ⊢ a ∥ b → m ⊢ (a ^ᶠ k) ∥ (b ^ᶠ l)
  ∥-^ᶠ² k l e = ∥-^ᶠ k (∥-sym (∥-^ᶠ l (∥-sym e)))

  -- The iterates of a conjugate.
  conj-pow : {g g' a : Circuit m} → m ⊢ g' • g ≈ ε → m ⊢ g • g' ≈ ε →
             (k : ℕ) → m ⊢ (g' • a • g) ^ k ≈ g' • a ^ k • g
  conj-pow {g} {g'} {a} g'g gg' zero = sym (trans (back _ left-unit) g'g)
  conj-pow g'g gg' (suc zero) = refl
  conj-pow {g} {g'} {a} g'g gg' (suc (suc k)) = begin
    (g' • a • g) • (g' • a • g) ^ suc k    ≈⟨ back _ (conj-pow g'g gg' (suc k)) ⟩
    (g' • a • g) • g' • a ^ suc k • g      ≈⟨ by-passoc ((□ • □ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
    g' • a • (g • g') • a ^ suc k • g      ≈⟨ back _ (back _ (trans (front _ gg') left-unit)) ⟩
    g' • a • a ^ suc k • g                 ≈⟨ back _ (sym assoc) ⟩
    g' • (a • a ^ suc k) • g               ∎
