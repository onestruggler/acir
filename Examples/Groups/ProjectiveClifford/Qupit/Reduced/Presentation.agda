------------------------------------------------------------------------
-- Presentations of groups
--
-- The reduced Clifford rules present Pauli n ⋊ Sp(2n, ℤ/pℤ).
--
-- Nothing new is proved here: the theorem is the composite of two
-- results that already exist.
--
--   * Reduced.Iso gives a group isomorphism between the word group of
--     the reduced rules and the word group of the Paper-V1 rules.  Both
--     rule sets are relations over the same alphabet, so the
--     isomorphism is the identity on words and needs no transport of
--     the interpretation at all.
--   * Paper-V1.Presentation gives that the Paper-V1 rules present
--     Pauli⋊Sp.
--
-- Composing, the reduced rules present the same group, with the same
-- interpretation: ⟦_⟧ ∘ id, where ⟦_⟧ is Paper-V1's.
--
-- This mirrors Paper-V1.Presentation, which transports Paper-V0's
-- presentation the same way.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Notations
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ForStdlib.Data.Fin.Mod.Prime.Fermat
open import ForStdlib.Data.Fin.Mod

module Examples.Groups.ProjectiveClifford.Qupit.Reduced.Presentation
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) -> ∃ \ (k : ℤ ₚ-₁) -> x ≡ g ^′ toℕ k )
  where

open import Algebra.Bundles using (Group)
open import Algebra.Bundles.Raw using (RawGroup)
import Algebra.Morphism.Construct.Composition as MC
open import Algebra.Morphism.Structures using (module GroupMorphisms)
open import Function using (_∘_ ; id)
open import Level using (0ℓ)
open import Presentation.Definitions using (_IsPresentationOf_)
open import Presentation.GroupLike using (module Group-Lemmas)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Transitive)

-- The target group, from the semidirect-product presentation.
import Examples.Groups.ProjectiveClifford.Qupit.SemiDirect.Presentation
  p-3 p-prime g* g-gen as SDPres

-- The reduced rules and the identity isomorphism onto Paper-V1's.
import Examples.Groups.ProjectiveClifford.Qupit.Reduced.Syntactics
  p-3 p-prime g* g-gen as Red
import Examples.Groups.ProjectiveClifford.Qupit.Reduced.Iso
  p-3 p-prime g* g-gen as RIso

-- The Paper-V1 presentation theorem, which the composite runs through.
import Examples.Groups.ProjectiveClifford.Qupit.Paper-V1.Presentation
  p-3 p-prime g* g-gen as V1Pres

private
  module Build (n : ℕ) where

    private
      module P = _IsPresentationOf_ (V1Pres.presentation n)

    -- The two word groups: W₀ over the reduced rules, W₁ over Paper-V1's.
    -- W₁ must be the Paper-V1 presentation's own word group — it is the
    -- source of P.iso — and it is the target of the isomorphism exactly
    -- because Reduced.Iso builds it from the same grouplike witness,
    -- Paper-V1.Iso's.
    module W₀ = Group-Lemmas (Red.Clifford-Relations._QRel,_===_ n)
                             (RIso.red-grouplike {n})
    module W₁ = P.GL

    G₃ : Group 0ℓ 0ℓ
    G₃ = SDPres.Semidirect.Pauli⋊Sp n

    ------------------------------------------------------------------
    -- The two isomorphisms

    private
      module M₀₁ = GroupMorphisms (Group.rawGroup W₀.•-ε-group)
                                  (Group.rawGroup W₁.•-ε-group)

    iso₀₁ : M₀₁.IsGroupIsomorphism id
    iso₀₁ = RIso.Theorem.M.Theorem-Reduced-iso-PaperV1 n

    ------------------------------------------------------------------
    -- The composite

    open GroupMorphisms (Group.rawGroup W₀.•-ε-group)
                        (Group.rawGroup G₃)

    -- Transitivity of the target's equality, with its three implicits
    -- bound by hand: the semidirect product's equality is Pointwise
    -- through projections, so unification never recovers them.
    ≈₃-trans : Transitive (RawGroup._≈_ (Group.rawGroup G₃))
    ≈₃-trans {x} {y} {z} eq₁ eq₂ =
      Setoid.trans (Group.setoid G₃) {x} {y} {z} eq₁ eq₂

    iso : IsGroupIsomorphism (P.⟦_⟧ ∘ id)
    iso = MC.isGroupIsomorphism {G₁ = Group.rawGroup W₀.•-ε-group}
                                {G₂ = Group.rawGroup W₁.•-ε-group}
                                {G₃ = Group.rawGroup G₃}
                                (λ {x} {y} {z} → ≈₃-trans {x} {y} {z})
                                {f = id} {g = P.⟦_⟧} iso₀₁ P.iso

    pres : (Red.Clifford-Relations._QRel,_===_ n) IsPresentationOf G₃
    pres = record
      { gl  = RIso.red-grouplike
      ; ⟦_⟧ = P.⟦_⟧ ∘ id
      ; iso = iso
      }

open Red using (module Clifford-Relations)
open SDPres using (module Semidirect)
open Clifford-Relations renaming (_QRel,_===_ to _CRel,_===_)
open Semidirect using (Pauli⋊Sp)

------------------------------------------------------------------------
-- The theorem

-- The reduced rules — Figure 1 mod scalars, without semi-MR, order-Ex,
-- yang-baxter and cz-slide — present the semidirect product of the
-- Pauli group and Sp(2n, ℤ/pℤ).
presentation : ∀ (n : ℕ) → (n CRel,_===_) IsPresentationOf (Pauli⋊Sp n)
presentation = Build.pres
