------------------------------------------------------------------------
-- Presentations of groups
--
-- The interpretation of phase-affine circuits as operators:
-- ⟦_⟧ : Circuit n → Op n  (Definitions 6 and 20)
--
-- A word denotes the composite of its letters' operators, in operator
-- order.  The reading is abstract — a circuit's operator is compared by
-- comparing circuits, never by unfolding a long product — with its
-- defining equations exported as lemmas (⟦⟧-gen, ⟦⟧-ε, ⟦⟧-•), and the
-- iterate and shift laws (⟦⟧-^, up-word).  The library's reading
-- through the monoid (Ext.⟦_⟧ᴱ) equals it (⟦⟧ᴱ-def).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Primality using (Prime)
open import Notations using (₂₊)

module Examples.Groups.Qupit-Phase-Affine.Interpretation
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (lv : ℕ) where

open import Data.Nat.Base using (zero ; suc)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)

open import Notations using (₁₊)

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime lv

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Denotation of generators and words

⟦_⟧ᵍ : Gen n → Op n
⟦ gate₀ (ω-gate _)      ⟧ᵍ = ωₒ
⟦ gate₁ X-gate          ⟧ᵍ = Xₒ
⟦ gate₁ (M-gate a _)    ⟧ᵍ = Mₒ a
⟦ gate₁ (Z-gate _)      ⟧ᵍ = Zₒ
⟦ gate₁ (S-gate _)      ⟧ᵍ = Sₒ
⟦ gate₁ (T-gate _)      ⟧ᵍ = Tₒ
⟦ gate₂ CX-gate         ⟧ᵍ = CXₒ
⟦ gate₂ SWAP-gate       ⟧ᵍ = SWAPₒ
⟦ g ↥                   ⟧ᵍ = up ⟦ g ⟧ᵍ

abstract
  ⟦_⟧ : Circuit n → Op n
  ⟦ [ g ]ʷ ⟧ = ⟦ g ⟧ᵍ
  ⟦ ε ⟧      = Idₒ
  ⟦ w • v ⟧  = ⟦ w ⟧ ⊙ ⟦ v ⟧

  ⟦⟧-gen : (g : Gen n) → ⟦ [ g ]ʷ ⟧ ≐ ⟦ g ⟧ᵍ
  ⟦⟧-gen g = ≐-refl ⟦ g ⟧ᵍ

  ⟦⟧-ε : ⟦_⟧ {n} ε ≐ Idₒ
  ⟦⟧-ε = ≐-refl Idₒ

  ⟦⟧-• : (w v : Circuit n) → ⟦ w • v ⟧ ≐ (⟦ w ⟧ ⊙ ⟦ v ⟧)
  ⟦⟧-• w v = ≐-refl (⟦ w ⟧ ⊙ ⟦ v ⟧)

-- An iterate denotes the iterate.
⟦⟧-^ : (w : Circuit n) (m : ℕ) → ⟦ w ^ m ⟧ ≐ ⟦ w ⟧ ^ₒ m
⟦⟧-^ w zero            = ⟦⟧-ε
⟦⟧-^ w (suc zero)      = ≐-sym (⊙-identityʳ ⟦ w ⟧)
⟦⟧-^ w (suc (suc m))   =
  ≐-trans (⟦⟧-• w (w ^ suc m)) (⊙-cong (≐-refl ⟦ w ⟧) (⟦⟧-^ w (suc m)))

-- Shifting a circuit shifts its operator.
up-word : (w : Circuit n) → ⟦ w ↑ ⟧ ≐ up ⟦ w ⟧
up-word [ g ]ʷ  = ≐-trans (⟦⟧-gen (g ↥)) (up-cong (≐-sym (⟦⟧-gen g)))
up-word ε       = ≐-trans ⟦⟧-ε (≐-trans (≐-sym up-Id) (up-cong (≐-sym ⟦⟧-ε)))
up-word (w • v) =
  ≐-trans (⟦⟧-• (w ↑) (v ↑))
    (≐-trans (⊙-cong (up-word w) (up-word v))
      (≐-trans (≐-sym (up-⊙ ⟦ w ⟧ ⟦ v ⟧)) (up-cong (≐-sym (⟦⟧-• w v)))))

-- The same reading as StarInterp builds it from the monoid, for the
-- presentation machinery; the two agree on the nose.
module Ext (n : ℕ) where
  open import Normalization.StarInterp (n VRel,_===_)
  open Extend (Op-monoid n) ⟦_⟧ᵍ public
    renaming (⟦_⟧ to ⟦_⟧ᴱ)

abstract
  ⟦⟧ᴱ-def : (w : Circuit n) → Ext.⟦_⟧ᴱ n w ≡ ⟦ w ⟧
  ⟦⟧ᴱ-def [ g ]ʷ  = Eq.refl
  ⟦⟧ᴱ-def ε       = Eq.refl
  ⟦⟧ᴱ-def (w • v) = Eq.cong₂ _⊙_ (⟦⟧ᴱ-def w) (⟦⟧ᴱ-def v)

⟦⟧ᴱ-≐ : {w v : Circuit n} → ⟦ w ⟧ ≐ ⟦ v ⟧ → Ext.⟦_⟧ᴱ n w ≐ Ext.⟦_⟧ᴱ n v
⟦⟧ᴱ-≐ {w = w} {v} = Eq.subst₂ _≐_ (Eq.sym (⟦⟧ᴱ-def w)) (Eq.sym (⟦⟧ᴱ-def v))

≐-⟦⟧ᴱ : {w v : Circuit n} → Ext.⟦_⟧ᴱ n w ≐ Ext.⟦_⟧ᴱ n v → ⟦ w ⟧ ≐ ⟦ v ⟧
≐-⟦⟧ᴱ {w = w} {v} = Eq.subst₂ _≐_ (⟦⟧ᴱ-def w) (⟦⟧ᴱ-def v)
