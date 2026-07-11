------------------------------------------------------------------------
-- Presentations of groups
--
-- Group homomorphism from the free-group presentation (Word (Gen n) / ≈)
-- to the permutation group Permutation′ n, via the tight semantics.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Symmetric.Tight.Presentation where

open import Data.Fin.Permutation using (_⟨$⟩ˡ_ ; _⟨$⟩ʳ_ ; inverseˡ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (sym ; trans ; cong)

open import Algebra.Bundles using (Group)

open import Presentation.GroupLike

open import Examples.Groups.Symmetric.Syntactics
import Examples.Groups.Symmetric.Tight.Semantics as ST
open ST using (Permutation′-group)
open import Notations
open import Word.Base


import Presentation.Base as PB
import Presentation.Properties as PP
open import Presentation.Definitions

open import Examples.Groups.Symmetric.Tight.Semantics
open import Examples.Groups.Symmetric.Tight.Soundness
open import Data.Fin.Permutation
  using ( Permutation′ ; _⟨$⟩ʳ_ ; _⟨$⟩ˡ_ ; _∘ₚ_ ; flip
        ; inverseˡ ; inverseʳ ; lift₀ ; lift₀-cong ; remove ; lift₀-remove)
open import Data.Product using (∃ ; _,_ ; proj₁ ; proj₂)
import Data.Fin as F

open import Data.Nat using (zero ; suc)
open import Data.Fin using (Fin ; zero ; suc)
open import Examples.Groups.Symmetric.Cosets
import Examples.Groups.Symmetric.Tight.Uniqueness as TU
import Examples.Groups.Symmetric.Normalization as SN

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl)

open import Normalization.StarPresentation

subpresentation : ∀ {n} -> let open PP (n VRel,_===_) in
  (n VRel,_===_) IsSubPresentationOf (Permutation′-group n)
subpresentation {n} =
  GS.GetSubPresentation.groupSubPres sound-ax grouplike (SN.nfp'-t n) TU.unique-nf-tight
  where
  module GS = GroupSem (n VRel,_===_) (Eq.setoid (SN.NF n))
                       (Permutation′-group n) (⟦_⟧ᵍ {n})



presentation : ∀ {n} -> let open PP (n VRel,_===_) in
  (n VRel,_===_) IsPresentationOf (Permutation′-group n)
presentation {n} = isPresentationOf subpresentation  claim
  where
  open PB (n VRel,_===_)
  open import Function.Definitions using (Surjective)

  fin-to-C : ∀ {m} → Fin (₁₊ m) → C m
  fin-to-C           F.zero    = ε
  fin-to-C {₁₊ m} (F.suc j) = σ• (fin-to-C j)

  depth : ∀ {m} → C m → Fin (₁₊ m)
  depth ε      = F.zero
  depth (σ• c) = F.suc (depth c)

  depth-fin-to-C : ∀ {m} (j : Fin (₁₊ m)) → depth (fin-to-C j) ≡ j
  depth-fin-to-C           F.zero    = refl
  depth-fin-to-C {₁₊ m} (F.suc j) = Eq.cong F.suc (depth-fin-to-C j)

  ⟦[r]ᶜ⟧-zero : ∀ {m} (r : C m) → ⟦ [ r ]ᶜ ⟧ ⟨$⟩ʳ F.zero ≡ depth r
  ⟦[r]ᶜ⟧-zero ε      = refl
  ⟦[r]ᶜ⟧-zero (σ• c) =
    Eq.trans (⟦↑⟧ ([ c ]ᶜ) (F.suc F.zero))
             (Eq.cong F.suc (⟦[r]ᶜ⟧-zero c))

  go : ∀ m (π : Permutation′ m) → ∃ λ w → ∀ k → ⟦ w ⟧ ⟨$⟩ʳ k ≡ π ⟨$⟩ʳ k
  go 0       π = ε , λ ()
  go (suc m) π = w' ↑ • [ r ]ᶜ , correct
    where
    j      = π ⟨$⟩ʳ F.zero
    r      = fin-to-C j
    ρ_r    = ⟦ [ r ]ᶜ ⟧
    χ      = π ∘ₚ flip ρ_r
    ρ_r-eq : ρ_r ⟨$⟩ʳ F.zero ≡ j
    ρ_r-eq = Eq.trans (⟦[r]ᶜ⟧-zero r) (depth-fin-to-C j)
    χ₀     : χ ⟨$⟩ʳ F.zero ≡ F.zero
    χ₀     = Eq.subst (λ x → ρ_r ⟨$⟩ˡ x ≡ F.zero) ρ_r-eq (inverseˡ ρ_r)
    ρ'     = remove F.zero χ
    rec    = go m ρ'
    w'     = rec .proj₁
    ih     = rec .proj₂
    correct : ∀ k → ⟦ (w' ↑) • [ r ]ᶜ ⟧ ⟨$⟩ʳ k ≡ π ⟨$⟩ʳ k
    correct k =
      Eq.trans
        (Eq.cong (ρ_r ⟨$⟩ʳ_)
          (Eq.trans (⟦↑⟧ w' k)
          (Eq.trans (lift₀-cong ⟦ w' ⟧ ρ' ih k)
                    (lift₀-remove χ χ₀ k))))
        (inverseʳ ρ_r)

  claim : Surjective _≈_ (Group._≈_ ((Permutation′-group n))) ⟦_⟧
  claim y = let w , ih = go n y in w , λ {z} z≈w k → Eq.trans (sound z≈w k) (ih k)
  
