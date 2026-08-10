------------------------------------------------------------------------
-- Presentations of groups
--
-- Unique normal form for the permutation (Permutation′) semantics of
-- Sₙ, derived from the endofunction uniqueness of
-- SubPresentation.UniqueNormalForm via a pointwise agreement lemma.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Symmetric.UniqueNormalForm where

open import Algebra.Bundles using (Group)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (ℕ)
open import Notations using (₁₊ ; ₂₊)
open import Word.Base using (ε ; [_]ʷ ; _•_)

import Data.Fin as F
import Normalization.NormalForm.Propositional as NFBase
import Normalization.NormalForm.Setoid as SNF
import Normalization.NormalForm.Uniqueness.Propositional as NFU
import Relation.Binary.PropositionalEquality as Eq

open Eq using (_≡_ ; refl)

open import Examples.Groups.Symmetric.SubPresentation.Semantics
open import Examples.Groups.Symmetric.SubPresentation.UniqueNormalForm using (unique-nf)
open import Examples.Groups.Symmetric.Normalization
  using (NF ; inv-nf ; nfp'-t)
open import Examples.Groups.Symmetric.Syntactics

import Examples.Groups.Symmetric.Semantics as TightSem

open TightSem using (Permutation′-group)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- Agreement between tight and loose denotations

private

  ⟦⟧ᵍ-agree : ∀ {n} (g : Gen n) (k : Fin n) →
              TightSem.⟦ g ⟧ᵍ ⟨$⟩ʳ k ≡ ⟦ g ⟧ᵍ k
  ⟦⟧ᵍ-agree (gate₁ ())     _
  ⟦⟧ᵍ-agree (gate₂ σ-gate) zero      = refl
  ⟦⟧ᵍ-agree (gate₂ σ-gate) (₁₊ zero) = refl
  ⟦⟧ᵍ-agree (gate₂ σ-gate) (₂₊ _)    = refl
  ⟦⟧ᵍ-agree (g ↥)          zero      = refl
  ⟦⟧ᵍ-agree (g ↥)          (suc j)   = Eq.cong F.suc (⟦⟧ᵍ-agree g j)

  ⟦⟧-agree : ∀ {n} (w : Circuit n) (k : Fin n) →
             TightSem.⟦ w ⟧ ⟨$⟩ʳ k ≡ ⟦ w ⟧ k
  ⟦⟧-agree ε       _ = refl
  ⟦⟧-agree [ g ]ʷ  k = ⟦⟧ᵍ-agree g k
  ⟦⟧-agree (w • v) k =
    Eq.trans (Eq.cong (TightSem.⟦ v ⟧ ⟨$⟩ʳ_) (⟦⟧-agree w k)) (⟦⟧-agree v _)

------------------------------------------------------------------------
-- Unique normal form for the tight semantics

private
  -- A tight denotation determines a loose one wirewise (⟦⟧-agree), so
  -- the loose uniqueness transfers: rewrite the hypothesis along
  -- ⟦⟧-agree at both ends and appeal to unique-nf.  This is the whole
  -- content of the two witnesses below, which differ only in how they
  -- are packaged.
  transfer : ∀ {n} {u v : NF n} →
             (∀ k → TightSem.⟦ inv-nf {n} u ⟧ ⟨$⟩ʳ k ≡
                    TightSem.⟦ inv-nf {n} v ⟧ ⟨$⟩ʳ k) →
             u ≡ v
  transfer {n} {u} {v} eq =
    UniqueNormalForm.unique (unique-nf n)
      (λ k → Eq.trans (Eq.sym (⟦⟧-agree (inv-nf {n} u) k))
             (Eq.trans (eq k) (⟦⟧-agree (inv-nf {n} v) k)))
    where open SNF using (UniqueNormalForm)

-- Uniqueness in the sense of Normalization.NormalForm.Uniqueness,
-- which states it against the section inv-nf alone.
unique-nf-tight : ∀ {n} →
  let open NFU (_VRel,_===_ n) (NF n)
               (Group.setoid (Permutation′-group n)) (TightSem.⟦_⟧ {n})
  in UniqueNormalForm (inv-nf {n})
unique-nf-tight = record { unique = transfer }

-- The same content in the packaging of
-- Normalization.NormalForm.Setoid, which states uniqueness against a
-- whole NormalForm record.  Kept because that is the form
-- Normalization.StarPresentation's groupSubPres consumes.
unique-nf-tight-bundled : ∀ {n} →
  NFBase.UniqueNormalForm (_VRel,_===_ n) (NF n)
    (Group.setoid (Permutation′-group n)) (TightSem.⟦_⟧ {n}) (nfp'-t n)
unique-nf-tight-bundled = record { unique = transfer }
