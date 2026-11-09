------------------------------------------------------------------------
-- Presentations of groups
--
-- Completeness: in a sound theory where the rules of Fig. 10 hold,
-- circuits with the same denotation are congruent.
--
-- This is Lafont's proof of Theorem 4 from Lemmas 6 and 8.  Two
-- circuits with the same permutation reduce to canonical forms
-- (Lemma 8, Normalization), which denote that permutation too
-- (soundness), so they are the same canonical form (Lemma 6,
-- UniqueNormalForm), and the circuits are congruent.  On the way nf
-- respects the congruence, so it is a NormalForm in the sense of
-- Normalization.NormalForm, its normal forms unique for the semantics:
-- the data that Symmetric's coset tower supplies, obtained here without
-- checking the coset action against every relation.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Alternating.Interpretation using (⟦_⟧)
open import Examples.Groups.Alternating.Rules using (Fig10)
open import Examples.Groups.Alternating.Semantics using (_≈ᴬ_)
open import Examples.Groups.Alternating.Syntactics using (Circuit ; Theory)

module Examples.Groups.Alternating.Completeness
  (T : Theory) (rules : Fig10 T)
  (sound-T : ∀ {n} {w v : Circuit n} → T n w v → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧)
  where

open import Algebra.Bundles using (Group)
open import Data.Nat using (ℕ)
open import Function.Definitions using (Injective)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

import Normalization.NormalForm.Propositional as NFBase
import Normalization.NormalForm.Uniqueness.Propositional as NFU
import Presentation.Base as PB
import Presentation.Properties as PP
import Relation.Binary.Reasoning.Setoid as SR

open import Examples.Groups.Alternating.Normalization
  using (NF ; nf ; inv-nf ; inv-nf∘nf≈id)
open import Examples.Groups.Alternating.Semantics using (Alt-group)
open import Examples.Groups.Alternating.Soundness using (sound)
open import Examples.Groups.Alternating.Syntactics
  using (_∣_⊢_≈_ ; module Lift-Relation)
open import Examples.Groups.Alternating.UniqueNormalForm
  using (inv-nf-injective)

open Lift-Relation T using (_VRel,_===_)

private
  variable
    n : ℕ

  sound′ : ∀ {w v : Circuit n} → T ∣ n ⊢ w ≈ v → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧
  sound′ = sound T sound-T

  lemma-8 : (w : Circuit n) → T ∣ n ⊢ inv-nf (nf w) ≈ w
  lemma-8 = inv-nf∘nf≈id rules


------------------------------------------------------------------------
-- Completeness

-- Circuits with the same denotation have the same canonical form.
nf-unique : ∀ {w v : Circuit n} → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧ → nf w ≡ nf v
nf-unique {n} {w} {v} eq = inv-nf-injective λ k →
  Eq.trans (sound′ (lemma-8 w) k)
  (Eq.trans (eq k) (Eq.sym (sound′ (lemma-8 v) k)))

completeness : Injective (_∣_⊢_≈_ T n) (Group._≈_ (Alt-group n)) ⟦_⟧
completeness {n} {w} {v} eq = begin
  w              ≈⟨ PB.sym (lemma-8 w) ⟩
  inv-nf (nf w)  ≡⟨ Eq.cong inv-nf (nf-unique eq) ⟩
  inv-nf (nf v)  ≈⟨ lemma-8 v ⟩
  v              ∎
  where open SR (PP.word-setoid (n VRel,_===_))

------------------------------------------------------------------------
-- The normal form

-- nf respects the congruence,
nf-cong : ∀ {w v : Circuit n} → T ∣ n ⊢ w ≈ v → nf w ≡ nf v
nf-cong w≈v = nf-unique (sound′ w≈v)

-- so it is a normal form with the canonical forms as its section,
nfp′ : ∀ n → NFBase.NormalForm (n VRel,_===_) (NF n)
nfp′ n = record
  { rightInverse = record
    { to        = nf
    ; from      = inv-nf
    ; to-cong   = nf-cong
    ; from-cong = λ { Eq.refl → PB.refl }
    ; inverseʳ  = λ { Eq.refl → lemma-8 _ }
    }
  }

-- and they are unique for the semantics.
unique-nf : NFU.UniqueNormalForm (n VRel,_===_) (NF n)
              (Group.setoid (Alt-group n)) ⟦_⟧ (inv-nf {n})
unique-nf = record { unique = inv-nf-injective }
