------------------------------------------------------------------------
-- Presentations of groups
--
-- The V1 Clifford rules present Pauli n ⋊ Sp(2n, ℤ/pℤ).
--
-- Nothing new is proved here: the theorem is the composite of two
-- results that already exist.
--
--   * Iso gives a group isomorphism between the word group of the
--     semidirect-product rules and the word group of the V1 Clifford
--     rules.  It is stated in the direction SemiDirect → Clifford, via
--     (f ʷ); the direction that composes here is the other one, so it
--     is rebuilt from the same six ingredients with the roles of f and
--     h swapped — StarGroupIsomorphism is symmetric in exactly that
--     way.
--   * SemiDirect.Presentation gives that the semidirect-product rules
--     present Pauli⋊Sp.
--
-- Composing, the V1 Clifford rules present the same group, with
-- interpretation ⟦_⟧ ∘ (h ʷ): read a Clifford word as a word over the
-- semidirect generators, then interpret it.
--
-- This mirrors Symplectic.Simplified.Presentation, which transports the
-- symplectic presentation along the same kind of isomorphism.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe --termination-depth=4 #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (_,_ ; ∃)
open import Notations
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ForStdlib.Data.Fin.Mod.Prime.Fermat
open import ForStdlib.Data.Fin.Mod

module Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.Presentation
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
open import Function using (_∘_)
open import Level using (0ℓ)
open import Presentation.Definitions using (_IsPresentationOf_)
open import Presentation.GroupLike using (module Group-Lemmas)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Transitive)
open import Word.Base using (_ʷ)

-- The semidirect-product rules and their presentation theorem.
open import Examples.Groups.ProjectiveClifford.Qupit.SemiDirect.Syntactics
  p-3 p-prime g* g-gen as SD using (module SemiDirect)
import Examples.Groups.ProjectiveClifford.Qupit.SemiDirect.Presentation
  p-3 p-prime g* g-gen as SDPres

-- The V1 Clifford rules, their grouplike witness, and the isomorphism.
open import Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.Syntactics
  p-3 p-prime g* g-gen as Cli
  using (module Clifford-Relations)
open import Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.Lemmas
  p-3 p-prime g* g-gen
  using (module Clifford-GroupLike)
import Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.Forward
  p-3 p-prime g* g-gen as IFwd
import Examples.Groups.ProjectiveClifford.Qupit.Simplified-V1.Iso
  p-3 p-prime g* g-gen as ISO

private
  module Build (n : ℕ) where

    private
      module I  = IFwd.Iso n
      module I2 = ISO.Iso-Inverse-Direction n
      module I3 = ISO.M n
      module P  = _IsPresentationOf_ (SDPres.presentation {n})

    -- The two word groups: W₁ over the Clifford rules, W₂ over the
    -- semidirect-product rules.  The target is Pauli⋊Sp.
    --
    -- W₂ must use the presentation's own grouplike witness, not
    -- Semi-GroupLike's: a Grouplike determines the word group's
    -- inverse, so two different witnesses give two different groups,
    -- and only the presentation's one is the source of P.iso.
    module W₁ = Group-Lemmas (Cli.Clifford-Relations._QRel,_===_ n)
                             (Clifford-GroupLike.grouplike {n})
    module W₂ = P.GL

    G₃ : Group 0ℓ 0ℓ
    G₃ = SDPres.Semidirect.Pauli⋊Sp n

    ------------------------------------------------------------------
    -- The isomorphism, in the direction that composes

    private
      module M₁₂ = GroupMorphisms (Group.rawGroup W₁.•-ε-group)
                                  (Group.rawGroup W₂.•-ε-group)
      module M₂₃ = GroupMorphisms (Group.rawGroup W₂.•-ε-group)
                                  (Group.rawGroup G₃)

      -- Presentation.Morphism instantiated the other way round from
      -- Iso: Clifford first, semidirect second.
      open import Presentation.Morphism
        (Cli.Clifford-Relations._QRel,_===_ n)
        (SemiDirect._QRel,_===_ n)
      open GroupMorphism (Clifford-GroupLike.grouplike {n}) P.gl

    -- Iso's six ingredients, with f and h exchanged.
    iso₁₂ : M₁₂.IsGroupIsomorphism (I.h ʷ)
    iso₁₂ = StarGroupIsomorphism.isGroupIsomorphism
              I.h I.f
              I2.h-well-defined I3.g-left-inv-gen
              I.f-well-defined  I3.f-left-inv-gen

    iso₂₃ : M₂₃.IsGroupIsomorphism P.⟦_⟧
    iso₂₃ = P.iso

    ------------------------------------------------------------------
    -- The composite

    open GroupMorphisms (Group.rawGroup W₁.•-ε-group)
                        (Group.rawGroup G₃)

    -- Transitivity of the target's equality, with its three implicits
    -- bound by hand: the semidirect product's equality is Pointwise
    -- through projections, so unification never recovers them.
    ≈₃-trans : Transitive (RawGroup._≈_ (Group.rawGroup G₃))
    ≈₃-trans {x} {y} {z} eq₁ eq₂ =
      Setoid.trans (Group.setoid G₃) {x} {y} {z} eq₁ eq₂

    iso : IsGroupIsomorphism (P.⟦_⟧ ∘ (I.h ʷ))
    iso = MC.isGroupIsomorphism {G₁ = Group.rawGroup W₁.•-ε-group}
                                {G₂ = Group.rawGroup W₂.•-ε-group}
                                {G₃ = Group.rawGroup G₃}
                                (λ {x} {y} {z} → ≈₃-trans {x} {y} {z})
                                {f = I.h ʷ} {g = P.⟦_⟧} iso₁₂ iso₂₃

    pres : (Cli.Clifford-Relations._QRel,_===_ n) IsPresentationOf G₃
    pres = record
      { gl  = Clifford-GroupLike.grouplike
      ; ⟦_⟧ = P.⟦_⟧ ∘ (I.h ʷ)
      ; iso = iso
      }

------------------------------------------------------------------------
-- The theorem

-- The V1 Clifford rules present the semidirect product of the Pauli
-- group by Sp(2n, ℤ/pℤ).
presentation : ∀ {n} →
               (Cli.Clifford-Relations._QRel,_===_ n)
                 IsPresentationOf (SDPres.Semidirect.Pauli⋊Sp n)
presentation {n} = Build.pres n
