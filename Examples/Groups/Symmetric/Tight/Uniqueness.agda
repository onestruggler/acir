------------------------------------------------------------------------
-- Presentations of groups
--
-- Unique normal form for the tight (Permutation′) semantics of Sₙ,
-- derived from the loose uniqueness via a pointwise agreement lemma.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Fin using (Fin ; zero ; suc)
import Data.Fin as F
open import Data.Fin.Permutation
  using ( Permutation′ ; _⟨$⟩ʳ_ ; _∘ₚ_ )
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl)
import Normalization.NormalForm.Propositional as NFBase
import Normalization.NormalForm.Uniqueness.Propositional as NFU
import Normalization.NormalForm.Setoid as SNF
open import Algebra.Bundles using (Group)
import Examples.Groups.Symmetric.Tight.Semantics as TightSem
open TightSem using (Permutation′-group)

open import Word.Base
open import Notations

module Examples.Groups.Symmetric.Tight.Uniqueness where

open import Examples.Groups.Symmetric.Syntactics
open import Examples.Groups.Symmetric.Normalization using (NF ; inv-nf ; nfp'-t)
open import Examples.Groups.Symmetric.Loose.Semantics
open import Examples.Groups.Symmetric.Loose.Uniqueness using (unique-nf)

private variable n : ℕ

------------------------------------------------------------------------
-- Agreement between tight and loose denotations

private

  ⟦⟧ᵍ-agree : ∀ {n} (g : Gen n) (k : Fin n)
             → TightSem.⟦ g ⟧ᵍ ⟨$⟩ʳ k ≡ ⟦ g ⟧ᵍ k
  ⟦⟧ᵍ-agree (gate₁ ()) _
  ⟦⟧ᵍ-agree (gate₂ σ-gate) zero      = refl
  ⟦⟧ᵍ-agree (gate₂ σ-gate) (₁₊ zero) = refl
  ⟦⟧ᵍ-agree (gate₂ σ-gate) (₂₊ _)    = refl
  ⟦⟧ᵍ-agree (g ↥) zero    = refl
  ⟦⟧ᵍ-agree (g ↥) (suc j) = Eq.cong F.suc (⟦⟧ᵍ-agree g j)

  ⟦⟧-agree : ∀ {n} (w : Circuit n) (k : Fin n)
            → TightSem.⟦ w ⟧ ⟨$⟩ʳ k ≡ ⟦ w ⟧ k
  ⟦⟧-agree ε       _ = refl
  ⟦⟧-agree [ g ]ʷ  k = ⟦⟧ᵍ-agree g k
  ⟦⟧-agree (w • v) k = Eq.trans (Eq.cong (TightSem.⟦ v ⟧ ⟨$⟩ʳ_) (⟦⟧-agree w k))
                                 (⟦⟧-agree v _)

------------------------------------------------------------------------
-- Unique normal form for the tight semantics

-- A tight denotation determines a loose one wirewise (⟦⟧-agree), so
-- the loose uniqueness transfers: rewrite the hypothesis along
-- ⟦⟧-agree at both ends and appeal to unique-nf.
unique-nf-tight :
  NFBase.UniqueNormalForm (_VRel,_===_ n) (NF n)
    (Group.setoid (Permutation′-group n)) (TightSem.⟦_⟧ {n}) (nfp'-t n)
unique-nf-tight {n = n} = record
  { unique = λ {u} {v} eq →
      UniqueNormalForm.unique (unique-nf n)
        (λ k → Eq.trans (Eq.sym (⟦⟧-agree (inv-nf {n} u) k))
               (Eq.trans (eq k) (⟦⟧-agree (inv-nf {n} v) k)))
  }
  where open SNF using (UniqueNormalForm)

-- The same content in the packaging of
-- Normalization.NormalForm.Uniqueness, which takes the section
-- inv-nf directly instead of a whole NormalForm record.  The two
-- `unique` fields have the same type, so this is a repackaging.
unique-nf-tight′ : ∀ n →
  let open NFU (_VRel,_===_ n) (NF n)
               (Group.setoid (Permutation′-group n)) (TightSem.⟦_⟧ {n})
  in UniqueNormalForm (inv-nf {n})
unique-nf-tight′ n = record
  { unique = SNF.UniqueNormalForm.unique (unique-nf-tight {n})
  }
