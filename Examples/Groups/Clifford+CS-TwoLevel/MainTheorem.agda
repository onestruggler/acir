------------------------------------------------------------------------
-- Presentations of groups
--
-- Bian and Selinger (2021): the main theorem, for MainTheorems
--
-- The two-level generators and the relations of their Figure 1 present
-- Uₙ(ℤ[½, i]) in every dimension.  Uₙ(ℤ[½, i]) is a subgroup of
-- Uₙ(𝔻[ω]) (DOmega), where a word's matrix is read and compared.  This
-- module collects what MainTheorems states, behind one import: the
-- words (Word n), the relations at each dimension (_MRel,_===_), the
-- group, a word's matrix ⟦_⟧, derivability ⊢_≈_, the presentation, and
-- its completeness and soundness for ⟦_⟧.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS-TwoLevel.MainTheorem where

open import Data.Nat.Base using (ℕ)

import Word.Base as W
open import Word.Base using (WRel)
import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)

open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics using (Gen ; _===_)
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics public using (U)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Unitary public using (UMat ; _≈ᵁ_)
import Examples.Groups.Clifford+CS-TwoLevel.DOmega as Ω
import Examples.Groups.Clifford+CS-TwoLevel.Presentation as P

------------------------------------------------------------------------
-- Words and relations

-- Words over the generators of dimension n.
Word : ℕ → Set
Word n = W.Word (Gen n)

-- The relations of Figure 1 in dimension n.
infix 4 _MRel,_===_
_MRel,_===_ : (n : ℕ) → WRel (Gen n)
n MRel, w === v = _===_ {n} w v

-- Equality by the relations.
infix 4 ⊢_≈_
⊢_≈_ : ∀ {n} → Word n → Word n → Set
⊢_≈_ {n} = PB._≈_ (n MRel,_===_)

------------------------------------------------------------------------
-- The theorem

presentation : ∀ n → (n MRel,_===_) IsPresentationOf (U n)
presentation n = P.presentation {n}

-- A word's matrix, over 𝔻[ω].
⟦_⟧ : ∀ {n} → Word n → UMat n
⟦_⟧ = Ω.⟦_⟧

complete : ∀ {n} {w v : Word n} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
complete = Ω.complete

sound : ∀ {n} {w v : Word n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
sound = Ω.sound
