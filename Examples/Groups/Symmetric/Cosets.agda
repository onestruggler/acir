------------------------------------------------------------------------
-- Presentations of groups
--
-- Symmetric groups Sₙ: coset descriptors, their section into circuits,
-- and decidable equality.  (The normal form built from these lives in
-- Examples.Groups.Symmetric.Normalization.)
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Nullary.Decidable using (yes ; no)

open import Data.Nat using (ℕ ; zero ; suc)

open import Word.Base
open import Notations

module Examples.Groups.Symmetric.Cosets where

private variable
  n : ℕ

open import Examples.Groups.Symmetric.Syntactics

------------------------------------------------------------------------
-- Coset type

infixr 10 σ•_
data C : ℕ → Set where
  ε   : C n
  σ•_ : C n → C (₁₊ n)

------------------------------------------------------------------------
-- Section map: C n → Circuit (₁₊ n)
-- (shifted by 1 because gate₂ σ-gate needs ≥ 2 wires)

[_]ᶜ : C n → Circuit (₁₊ n)
[_]ᶜ         ε      = ε
[_]ᶜ {₁₊ n} (σ• c)  = σ • ([ c ]ᶜ ↑)

------------------------------------------------------------------------
-- Decidable equality on cosets

lemma-daux : ∀ {n} x y → σ•_ {n} x ≡ σ• y → x ≡ y
lemma-daux x y Eq.refl = Eq.refl

deceqC : DecidableEquality (C n)
deceqC {zero}  ε      ε       = yes Eq.refl
deceqC {₁₊ n} ε      ε       = yes Eq.refl
deceqC {₁₊ n} ε      (σ• y)  = no (λ ())
deceqC {₁₊ n} (σ• x) ε       = no (λ ())
deceqC {₁₊ n} (σ• x) (σ• y) with deceqC x y
... | yes p  = yes (Eq.cong σ•_ p)
... | no  np = no (λ { eq → np (lemma-daux _ _ eq) })

