------------------------------------------------------------------------
-- Presentations of groups
--
-- Symmetric groups Sₙ: coset descriptors, their section into circuits,
-- and decidable equality.  (The normal form built from these lives in
-- Examples.Groups.Symmetric.Normalization.)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; zero)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary.Decidable using (yes ; no)

open import Notations
open import Word.Base

module Examples.Groups.Symmetric.Cosets where

open import Examples.Groups.Symmetric.Syntactics

private variable
  n : ℕ

------------------------------------------------------------------------
-- Coset type

-- A coset of Sₙ in S_{n+1} is either the identity coset or one of the
-- n cosets reached by a final transposition.
infixr 10 σ•_
data C : ℕ → Set where
  ε   : C n
  σ•_ : C n → C (₁₊ n)

------------------------------------------------------------------------
-- Section map

-- [ c ]ᶜ realises the coset c as a circuit (shifted by 1 because
-- gate₂ σ-gate needs at least 2 wires).
[_]ᶜ : C n → Circuit (₁₊ n)
[_]ᶜ         ε      = ε
[_]ᶜ {₁₊ n} (σ• c)  = σ • ([ c ]ᶜ ↑)

------------------------------------------------------------------------
-- Decidable equality on cosets

-- The coset constructor σ•_ is injective.
σ•-injective : ∀ {n} (x y : C n) → σ• x ≡ σ• y → x ≡ y
σ•-injective x y Eq.refl = Eq.refl

deceqC : DecidableEquality (C n)
deceqC {zero}  ε      ε       = yes Eq.refl
deceqC {₁₊ n} ε      ε       = yes Eq.refl
deceqC {₁₊ n} ε      (σ• y)  = no (λ ())
deceqC {₁₊ n} (σ• x) ε       = no (λ ())
deceqC {₁₊ n} (σ• x) (σ• y) with deceqC x y
... | yes p  = yes (Eq.cong σ•_ p)
... | no  np = no (λ { eq → np (σ•-injective _ _ eq) })
