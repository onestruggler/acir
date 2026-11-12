------------------------------------------------------------------------
-- Presentations of groups
--
-- Li, Ross and Selinger (2021): the main theorems, for MainTheorems
--
-- (−1)_[a], X_[a,b], K_[a,b,c,d] and Table 1 present Oₙ(ℤ[½]) in every
-- dimension (Theorem 4.10), and with I ⊗ H and Table 2 the scaled
-- dyadic orthogonal matrices Lₙ, for n = 2(k + 1) (Theorem 5.7); the
-- second is indexed by k.  Both groups are subgroups of Uₙ(𝔻[ω])
-- (DOmega, Scaled.DOmega), where a word's matrix is read and compared.
-- This module collects what MainTheorems states, behind one import: for
-- each, the words, the relations at each dimension (_MRel,_===_,
-- _MRelᴸ,_===_), the group, a word's matrix, derivability, the
-- presentation, and its completeness and soundness.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-TwoLevel.MainTheorem where

open import Data.Nat.Base as ℕ using (ℕ ; suc)

import Word.Base as W
open import Word.Base using (WRel)
import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)

open import Examples.Groups.CCX+HH-TwoLevel.Syntactics using (Gen ; _===_)
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics using (Genᴸ ; _===ᴸ_)
open import Examples.Groups.CCX+HH-TwoLevel.Semantics public using (O)
open import Examples.Groups.CCX+HH-TwoLevel.Scaled.Presentation public using (L)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Unitary public using (UMat ; _≈ᵁ_)
import Examples.Groups.CCX+HH-TwoLevel.DOmega as Ω
import Examples.Groups.CCX+HH-TwoLevel.Presentation as P
import Examples.Groups.CCX+HH-TwoLevel.Scaled.DOmega as ΩL
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Presentation as PL

------------------------------------------------------------------------
-- Oₙ(ℤ[½])

-- Words over the generators of dimension n.
Word : ℕ → Set
Word n = W.Word (Gen n)

-- Table 1 in dimension n.
infix 4 _MRel,_===_
_MRel,_===_ : (n : ℕ) → WRel (Gen n)
n MRel, w === v = _===_ {n} w v

-- Equality by the relations.
infix 4 ⊢_≈_
⊢_≈_ : ∀ {n} → Word n → Word n → Set
⊢_≈_ {n} = PB._≈_ (n MRel,_===_)

presentation : ∀ n → (n MRel,_===_) IsPresentationOf (O n)
presentation n = P.presentation {n}

-- A word's matrix, over 𝔻[ω].
⟦_⟧ : ∀ {n} → Word n → UMat n
⟦_⟧ = Ω.⟦_⟧

complete : ∀ {n} {w v : Word n} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
complete = Ω.complete

sound : ∀ {n} {w v : Word n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
sound = Ω.sound

------------------------------------------------------------------------
-- Lₙ, n = 2(k + 1), indexed by k

-- Words over the generators of dimension 2(k + 1).
Wordᴸ : ℕ → Set
Wordᴸ k = W.Word (Genᴸ (suc k ℕ.* 2))

-- Tables 1 and 2 in dimension 2(k + 1).
infix 4 _MRelᴸ,_===_
_MRelᴸ,_===_ : (k : ℕ) → WRel (Genᴸ (suc k ℕ.* 2))
k MRelᴸ, w === v = _===ᴸ_ {suc k ℕ.* 2} w v

-- Equality by the relations.  Here k is explicit, here and in ⟦_⟧ᴸ_: a
-- word over the generators of dimension suc k * 2 does not determine k
-- to unification, multiplication not being invertible.
infix 4 _⊢ᴸ_≈_
_⊢ᴸ_≈_ : ∀ k → Wordᴸ k → Wordᴸ k → Set
k ⊢ᴸ w ≈ v = PB._≈_ (k MRelᴸ,_===_) w v

presentationᴸ : ∀ k → (k MRelᴸ,_===_) IsPresentationOf (L k)
presentationᴸ k = PL.presentation k

-- A word's matrix, over 𝔻[ω].
⟦_⟧ᴸ_ : ∀ k → Wordᴸ k → UMat (suc k ℕ.* 2)
⟦ k ⟧ᴸ w = ΩL.⟦_⟧ k w

completeᴸ : ∀ k {w v : Wordᴸ k} → ⟦ k ⟧ᴸ w ≈ᵁ ⟦ k ⟧ᴸ v → k ⊢ᴸ w ≈ v
completeᴸ k = ΩL.complete k

soundᴸ : ∀ k {w v : Wordᴸ k} → k ⊢ᴸ w ≈ v → ⟦ k ⟧ᴸ w ≈ᵁ ⟦ k ⟧ᴸ v
soundᴸ k = ΩL.sound k
