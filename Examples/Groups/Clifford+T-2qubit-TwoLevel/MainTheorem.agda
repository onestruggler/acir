------------------------------------------------------------------------
-- Presentations of groups
--
-- Greylyn (2014): the main theorem, for MainTheorems
--
-- The two-level generators ω_[a], H_[a,b], X_[a,b] and Greylyn's
-- relations present Uₙ(ℤ[1/√2, i]) = Uₙ(𝔻[ω]) for n ≤ 4, by the main
-- lemma of the exact synthesis algorithm, as the thesis does.  This
-- module collects what MainTheorems states, behind one import: the
-- words (Word n), the relations at each dimension (_MRel,_===_), the
-- group, a word's matrix ⟦_⟧, derivability ⊢_≈_, the presentation, and
-- its completeness and soundness for ⟦_⟧.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+T-2qubit-TwoLevel.MainTheorem where

open import Data.Nat.Base using (ℕ ; _≤_)

import Word.Base as W
open import Word.Base using (WRel)
import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)

open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics using (Gen ; _===_)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics using (𝕀)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics public using (U)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Unitary public using (UMat ; _≈ᵁ_)
import Examples.Groups.Clifford+T-2qubit-TwoLevel.MainLemma as ML
import Examples.Groups.Clifford+T-2qubit-TwoLevel.Presentation as P
import Examples.Groups.Clifford+T-2qubit-TwoLevel.Reduction as R

------------------------------------------------------------------------
-- Words and relations

-- Words over the generators of dimension n.
Word : ℕ → Set
Word n = W.Word (Gen n)

-- Greylyn's relations in dimension n.
infix 4 _MRel,_===_
_MRel,_===_ : (n : ℕ) → WRel (Gen n)
n MRel, w === v = _===_ {n} w v

-- Equality by the relations.
infix 4 ⊢_≈_
⊢_≈_ : ∀ {n} → Word n → Word n → Set
⊢_≈_ {n} = PB._≈_ (n MRel,_===_)

------------------------------------------------------------------------
-- The theorem

presentation : ∀ n → n ≤ 4 → (n MRel,_===_) IsPresentationOf (U n)
presentation n n≤4 = P.presentation n≤4

-- A word's matrix.
⟦_⟧ : ∀ {n} → Word n → UMat n
⟦_⟧ = P.⟦_⟧ᵘ

complete : ∀ {n} → n ≤ 4 → {w v : Word n} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
complete n≤4 = ML.relations-complete n≤4

sound : ∀ {n} {w v : Word n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
sound e = R.sound-act e 𝕀
