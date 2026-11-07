------------------------------------------------------------------------
-- Presentations of groups
--
-- Clément (2019, thesis): the main theorem, for MainTheorems
--
-- Clément's own proof, over his version of the synthesis algorithm: his
-- relations (1)–(21), and Figure 6 of Hadamard-Π, present Oₙ(ℤ[1/√2])
-- in every dimension.  Oₙ(ℤ[1/√2]) is a subgroup of Uₙ(𝔻[ω])
-- (Thesis.DOmega), where a word's matrix is read and compared.  This
-- module collects what MainTheorems states, behind one import: the
-- words (Word n), Clément's relations (_MRelᶜ,_===_) and Figure 6
-- (_MRel,_===_, as in Real-Clifford+CH-TwoLevel.MainTheorem) at each
-- dimension, the group, a word's matrix ⟦_⟧, derivability (⊢ᶜ_≈_,
-- ⊢_≈_), the two presentations, and their completeness and soundness
-- for ⟦_⟧.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.MainTheorem where

open import Data.Nat.Base using (ℕ)

open import Word.Base using (WRel)
import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)

open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics using (Gen)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Clement using (_===ᶜ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.MainTheorem public
  using (Word ; _MRel,_===_ ; ⊢_≈_ ; O ; UMat ; _≈ᵁ_)
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.DOmega as Ω
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Thesis.Presentation as T

------------------------------------------------------------------------
-- Clément's relations

-- His relations (1)–(21) in dimension n.
infix 4 _MRelᶜ,_===_
_MRelᶜ,_===_ : (n : ℕ) → WRel (Gen n)
n MRelᶜ, w === v = _===ᶜ_ {n} w v

-- Equality by them.
infix 4 ⊢ᶜ_≈_
⊢ᶜ_≈_ : ∀ {n} → Word n → Word n → Set
⊢ᶜ_≈_ {n} = PB._≈_ (n MRelᶜ,_===_)

------------------------------------------------------------------------
-- The theorem

presentationᶜ : ∀ n → (n MRelᶜ,_===_) IsPresentationOf (O n)
presentationᶜ n = T.presentationᶜ {n}

presentation : ∀ n → (n MRel,_===_) IsPresentationOf (O n)
presentation n = T.presentation {n}

-- A word's matrix, over 𝔻[ω].
⟦_⟧ : ∀ {n} → Word n → UMat n
⟦_⟧ = Ω.⟦_⟧

completeᶜ : ∀ {n} {w v : Word n} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ᶜ w ≈ v
completeᶜ = Ω.completeᶜ

soundᶜ : ∀ {n} {w v : Word n} → ⊢ᶜ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
soundᶜ = Ω.soundᶜ

complete : ∀ {n} {w v : Word n} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
complete = Ω.complete

sound : ∀ {n} {w v : Word n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
sound = Ω.sound
