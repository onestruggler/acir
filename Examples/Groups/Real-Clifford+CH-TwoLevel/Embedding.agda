------------------------------------------------------------------------
-- Presentations of groups
--
-- Embedding a smaller dimension: a strictly increasing map of indices
-- ι : Fin m → Fin n relabels generators and carries every local
-- relation (Local) to a local relation.  A set of relations Γ on n
-- indices pulls back along it (pull: words are related when their
-- images are), with the local relations if Γ has them; so an equation
-- derived on m concrete indices from hypotheses holds in Γ (push) as
-- soon as the images of the hypotheses do.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel.Embedding where

open import Data.Fin.Base using (Fin ; _<_ ; inject≤ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Nat.Base as ℕ using (ℕ ; _≤_)
open import Relation.Binary.Definitions using (tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary.Decidable using (recompute)

open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP

open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Local

private
  variable
    m n : ℕ

------------------------------------------------------------------------
-- Increasing maps of indices

record Emb (m n : ℕ) : Set where
  field
    ι    : Fin m → Fin n
    mono : ∀ {a b : Fin m} → a < b → ι a < ι b

  injective : ∀ {a b : Fin m} → a ≢ b → ι a ≢ ι b
  injective {a} {b} a≢b with FinP.<-cmp a b
  ... | tri< a<b _ _ = λ eq → FinP.<-irrefl eq (mono a<b)
  ... | tri≈ _ a≡b _ = λ _ → a≢b a≡b
  ... | tri> _ _ b<a = λ eq → FinP.<-irrefl (≡.sym eq) (mono b<a)

  private
    rc : ∀ {a b : Fin m} → .(a < b) → a < b
    rc {a} {b} lt = recompute (a FinP.<? b) lt

    monoᵢ : ∀ {a b : Fin m} → .(a < b) → ι a < ι b
    monoᵢ lt = mono (rc lt)

  -- Relabelling generators and words.
  gen : Gen m → Gen n
  gen (X-gen a b p) = X-gen (ι a) (ι b) (monoᵢ p)
  gen (K-gen a b p) = K-gen (ι a) (ι b) (monoᵢ p)
  gen (i-gen a)     = i-gen (ι a)

  word : Word (Gen m) → Word (Gen n)
  word = wmap gen

  -- Local relations go to local relations.
  local : ∀ {u v} → u ===ˡ v → word u ===ˡ word v
  local a1 = a1
  local (a2 p) = a2 (monoᵢ p)
  local (a3 p) = a3 (monoᵢ p)
  local (b1 ne) = b1 (injective ne)
  local (b2 p x y) = b2 (monoᵢ p) (injective x) (injective y)
  local (b3 p q x y z w) = b3 (monoᵢ p) (monoᵢ q) (injective x) (injective y) (injective z) (injective w)
  local (b4 p x y) = b4 (monoᵢ p) (injective x) (injective y)
  local (b5 p q x y z w) = b5 (monoᵢ p) (monoᵢ q) (injective x) (injective y) (injective z) (injective w)
  local (b6 p q x y z w) = b6 (monoᵢ p) (monoᵢ q) (injective x) (injective y) (injective z) (injective w)
  local (c1 p) = c1 (monoᵢ p)
  local (c2 p q) = c2 (mono p) (mono q)
  local (c3 p q) = c3 (mono p) (mono q)
  local (c4 p q) = c4 (mono p) (mono q)
  local (c5 p q) = c5 (mono p) (mono q)
  local (d1 p) = d1 (monoᵢ p)
  local (d2 p) = d2 (monoᵢ p)

open Emb public

-- The first m indices of n ≥ m.
incl : m ≤ n → Emb m n
incl h = record { ι = λ a → inject≤ a h ; mono = λ {a} {b} lt → mono′ lt }
  where
  mono′ : ∀ {a b} → a < b → inject≤ a h < inject≤ b h
  mono′ {a} {b} lt = ≡.subst₂ ℕ._<_ (≡.sym (FinP.toℕ-inject≤ a h)) (≡.sym (FinP.toℕ-inject≤ b h)) lt

toℕ-incl : (h : m ≤ n) (a : Fin m) → toℕ (ι (incl h) a) ≡ toℕ a
toℕ-incl h a = FinP.toℕ-inject≤ a h

------------------------------------------------------------------------
-- Pulling a set of relations back

module Pull (e : Emb m n) (Γ : WRel (Gen n)) where

  pull : WRel (Gen m)
  pull u v = PB._≈_ Γ (word e u) (word e v)

  -- Equations in the pulled-back relations hold for the images.
  push : ∀ {u v} → PB._≈_ pull u v → PB._≈_ Γ (word e u) (word e v)
  push = PP.GenCongruence.fʷ-cong pull Γ (gen e) (λ p → p)

  -- An equation of the images is one of the pulled-back relations.
  hyp : ∀ {u v} → PB._≈_ Γ (word e u) (word e v) → PB._≈_ pull u v
  hyp = PB.axiom

  -- The local relations, if Γ has them.
  pull-local : (∀ {u v} → u ===ˡ v → PB._≈_ Γ u v) → ∀ {u v} → u ===ˡ v → PB._≈_ pull u v
  pull-local loc x = PB.axiom (loc (local e x))
