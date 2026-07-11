------------------------------------------------------------------------
-- Presentations of groups
--
-- The cyclic presentation ⟨ t ∣ t^(1+n) = ε ⟩ presents ℤ/(1+n)ℤ: a
-- group isomorphism from the word group (Word X / ≈) to Cn-group (1+n).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Examples.Groups.Cyclic.Presentation where

open import Data.Fin.Permutation using (inverseˡ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (sym ; trans ; cong)

open import Algebra.Bundles using (Group)

open import Presentation.GroupLike

open import Examples.Groups.Cyclic.Syntactics

open import Notations
open import Word.Base


import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Definitions

open import Examples.Groups.Cyclic.Syntactics
open import Examples.Groups.Cyclic.Semantics
open import Examples.Groups.Cyclic.Soundness
open import Data.Fin.Permutation
  using ( Permutation′ ; _⟨$⟩ʳ_ ; _⟨$⟩ˡ_ ; _∘ₚ_ ; flip
        ; inverseˡ ; inverseʳ ; lift₀ ; lift₀-cong ; remove ; lift₀-remove)
open import Data.Product using (_,_)

open import Data.Nat using (ℕ ; zero ; suc ; _+_)
import Data.Nat.Properties as NP
open import Data.Fin using (zero ; suc)

import Normalization.NormalForm.Propositional as NFBase

import Examples.Groups.Cyclic.Uniqueness as TU
import Examples.Groups.Cyclic.Normalization as SN

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl)

open import Normalization.StarPresentation

subpresentation : ∀ {n} -> let open PP ((₁₊ n) Cn,_===_) in
  ((₁₊ n) Cn,_===_) IsSubPresentationOf (Cn-group (₁₊ n))
subpresentation {n} =
  GS.GetSubPresentation.groupSubPres
    (λ { order → order-sound (₁₊ n) })
    (grouplike n) (SN.nfp' (₁₊ n)) (TU.unique-nf (₁₊ n))
  where
  module GS = GroupSem ((₁₊ n) Cn,_===_) (Eq.setoid (SN.NF ((₁₊ n))))
                       (Cn-group (₁₊ n)) (gg {(₁₊ n)})



presentation : ∀ {n} -> let open PP ((₁₊ n) Cn,_===_) in
  ((₁₊ n) Cn,_===_) IsPresentationOf (Cn-group (₁₊ n))
presentation {n} = isPresentationOf subpresentation claim
  where
  open PB ((₁₊ n) Cn,_===_)
  open import Function.Definitions using (Surjective)

  -- The section [_] of the normal form realises every element: ⟦ [ y ] ⟧
  -- ≡ y.  At order 1 (ℤ/1ℤ) this is trivial; at order ≥ 2 it is pow-id.
  nf-sound : ∀ m (y : SN.NF (₁₊ m)) → ⟦_⟧ {₁₊ m} SN.[ y ] ≡ y
  nf-sound zero      zero = refl
  nf-sound (suc m')  y    = TU.pow-id y

  claim : Surjective _≈_ (Group._≈_ ((Cn-group (₁₊ n)))) (⟦_⟧ {(₁₊ n)})
  claim y = SN.[ y ] , λ {z} z≈y → Eq.trans (sound z≈y) (nf-sound n y)

------------------------------------------------------------------------
-- Order 0: the presented monoid is ℕ
--
-- Every presentation in this library is a monoid presentation.  At
-- order 0 the relation T ^' 0 = ε is the trivial ε = ε, so the
-- presented monoid is the free monoid on the single generator: (ℕ, +,
-- 0), with the generator denoting 1.  Read as a group presentation the
-- same relation set presents the cyclic group of order 0, which is ℤ
-- by definition — but grouplikeness fails at order 0 (T has no left
-- inverse), so monoidPresentation⇒presentation does not apply, and the
-- monoid-level statement below is the sharpest one available.  This is
-- the smallest example separating monoid presentations from group
-- presentations.

private
  module MS₀ = MonoidSem (0 Cn,_===_) (Eq.setoid (SN.NF 0)) NP.+-0-monoid (λ _ → 1)

-- The denotation of Tᵏ in (ℕ, +, 0) is k itself.
sem-ℕ : ∀ k → MS₀.⟦_⟧ (T ^' k) ≡ k
sem-ℕ zero          = refl
sem-ℕ (suc zero)    = refl
sem-ℕ (suc (suc k)) = trans (cong (_+ 1) (sem-ℕ (suc k))) (NP.+-comm (suc k) 1)

-- Distinct normal forms (word counts) have distinct denotations.
unique-nf₀ :
  NFBase.UniqueNormalForm (0 Cn,_===_) (SN.NF 0) (Eq.setoid ℕ) MS₀.⟦_⟧ (SN.nfp' 0)
unique-nf₀ = record
  { unique = λ {u} {v} eq → trans (sym (sem-ℕ u)) (trans eq (sem-ℕ v)) }

private
  module Sub₀ = MS₀.GetSubPresentation (λ { order → refl }) (SN.nfp' 0) unique-nf₀

monoid-presentation : (0 Cn,_===_) IsMonoidPresentationOf NP.+-0-monoid
monoid-presentation = isMonoidPresentationOf Sub₀.monoidSubPres claim
  where
  open PB (0 Cn,_===_)
  open import Function.Definitions using (Surjective)

  claim : Surjective _≈_ (_≡_ {A = ℕ}) MS₀.⟦_⟧
  claim k = SN.[_] {0} k , λ {z} hyp → Eq.trans (Sub₀.fʷ-cong hyp) (sem-ℕ k)
