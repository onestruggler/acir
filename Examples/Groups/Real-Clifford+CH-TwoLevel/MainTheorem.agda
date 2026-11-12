------------------------------------------------------------------------
-- Presentations of groups
--
-- Fang, Heunen and Kaarsgaard (2026), Hadamard-Π: the main theorem, for
-- MainTheorems
--
-- Z_[a], X_[a,b], H_[a,b] and the relations (a1)–(d4) of Figure 6
-- present Oₙ(ℤ[1/√2]) in every dimension.  The paper's proof does not
-- cover one case of its Main Lemma (its Lemmas A.16 and A.17 are
-- false): Presentation proves the theorem from that case, Hard, and
-- Real-Clifford+CH-TwoLevel-Clement proves the case itself, after
-- Clément's thesis.  Oₙ(ℤ[1/√2]) is a subgroup of Uₙ(𝔻[ω]) (DOmega,
-- and Real-Clifford+CH-TwoLevel-Clement.DOmega), where a word's matrix
-- is read and compared.  This module collects what MainTheorems
-- states, behind one import: the words (Word n), the relations at each
-- dimension (_MRel,_===_), the group, a word's matrix ⟦_⟧,
-- derivability ⊢_≈_, the presentation, and its completeness and
-- soundness for ⟦_⟧, each also as the paper's proof gives it, from
-- Hard.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford+CH-TwoLevel.MainTheorem where

open import Data.Nat.Base using (ℕ)

import Word.Base as W
open import Word.Base using (WRel)
import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)
import Presentation.Embedding as PE

open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics using (Gen ; _===_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics public using (O)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.MainLemma public using (Hard)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Unitary public using (UMat ; _≈ᵁ_)
import Examples.Groups.Real-Clifford+CH-TwoLevel.DOmega as RΩ
import Examples.Groups.Real-Clifford+CH-TwoLevel.Presentation as P
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.DOmega as Ω
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Presentation as C

------------------------------------------------------------------------
-- Words and relations

-- Words over the generators of dimension n.
Word : ℕ → Set
Word n = W.Word (Gen n)

-- Figure 6 in dimension n.
infix 4 _MRel,_===_
_MRel,_===_ : (n : ℕ) → WRel (Gen n)
n MRel, w === v = _===_ {n} w v

-- Equality by the relations.
infix 4 ⊢_≈_
⊢_≈_ : ∀ {n} → Word n → Word n → Set
⊢_≈_ {n} = PB._≈_ (n MRel,_===_)

------------------------------------------------------------------------
-- The theorem

-- The paper's proof, given the case it misses ...
presentation-given : ∀ n → Hard {n} → (n MRel,_===_) IsPresentationOf (O n)
presentation-given n = P.presentation {n}

-- ... and the theorem.
presentation : ∀ n → (n MRel,_===_) IsPresentationOf (O n)
presentation n = C.presentation {n}

-- A word's matrix, over 𝔻[ω].
⟦_⟧ : ∀ {n} → Word n → UMat n
⟦_⟧ = Ω.⟦_⟧

-- Completeness by the paper's proof, given the case it misses ...
complete-given : ∀ {n} → Hard {n} → {w v : Word n} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
complete-given hard = PE.Sub.complete (RΩ.presentation-given hard)

-- ... and the theorem.
complete : ∀ {n} {w v : Word n} → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧ → ⊢ w ≈ v
complete = Ω.complete

sound : ∀ {n} {w v : Word n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᵁ ⟦ v ⟧
sound = Ω.sound
