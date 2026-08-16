------------------------------------------------------------------------
-- Presentations of groups
--
-- The simplified rule set presents Sp(2n, ℤ/pℤ)
--
-- Examples.Groups.Symplectic.PresentationFull proves that the original
-- rule set _QRel,_===₁_ presents the symplectic group.  Iso proves that
-- the simplified rule set _QRel,_===₂_ generates exactly the same
-- congruence on words — the identity is a group isomorphism between the
-- two word groups, in both directions.  Composing the two gives the
-- presentation theorem for the simplified rules, with the SAME
-- interpretation ⟦_⟧: the underlying function on words is unchanged,
-- only the congruence it is quotiented by is presented differently.
--
-- Both results here are postulate-free, inheriting that from
-- PresentationFull (soundness, completeness and surjectivity are all
-- proved) and from Iso (every axiom on each side is derived from the
-- other side's axioms outright).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ ; suc)
open import Data.Nat.Primality using (Prime)
open import Data.Product using (∃ ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations
open import ForStdlib.Data.Fin.Mod
open import ForStdlib.Data.Fin.Mod.Prime.Fermat

module Examples.Groups.Symplectic.Simplified.Presentation
  (p-2 : ℕ)
  (p-prime : Prime (suc (₁₊ p-2)))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ \ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k )
  where

open import Algebra.Bundles using (Group)
open import Algebra.Bundles.Raw using (RawGroup)
open import Algebra.Morphism.Structures using (module GroupMorphisms)
import Algebra.Morphism.Construct.Composition as MC
open import Function using (id)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Transitive)

open import Presentation.Definitions
  using (_IsPresentationOf_ ; _IsSubPresentationOf_)
open import Presentation.GroupLike using (module Group-Lemmas)

-- The original presentation and its theorem.
open import Examples.Groups.Symplectic.Semantics p-2 p-prime using (Sp-group)
open import Examples.Groups.Symplectic.Syntactics p-2 p-prime as NSym using ()
open NSym.Symplectic using () renaming (_QRel,_===_ to _QRel,_===₁_)
open NSym.Symplectic-GroupLike using () renaming (grouplike to grouplike₁)
open import Examples.Groups.Symplectic.PresentationFull p-2 p-prime
  using () renaming (presentation to presentation₁)

-- The simplified presentation, and the isomorphism with the original.
open import Examples.Groups.Symplectic.Simplified.Syntactics p-2 p-prime g* g-gen
  as Sim using ()
open Sim.Simplified-Relations using () renaming (_QRel,_===_ to _QRel,_===₂_)
open import Examples.Groups.Symplectic.Simplified.Lemmas p-2 p-prime g* g-gen
  as SimL using ()
open SimL.Symplectic-Sim-GroupLike using () renaming (grouplike to grouplike₂)
open import Examples.Groups.Symplectic.Simplified.Iso p-2 p-prime g* g-gen
  using (Theorem-Sym-iso-Sim')

------------------------------------------------------------------------
-- Transport along the isomorphism
--
-- Theorem-Sym-iso-Sim' runs from the simplified word group to the
-- original one, which is the direction that composes with the original
-- presentation.  Its underlying function is the identity, so the
-- composite's underlying function is ⟦_⟧ itself, up to η.

private
  module Build (n : ℕ) where

    module P₁ = _IsPresentationOf_ (presentation₁ {n})

    -- The two word groups: W₁ over the original rules, W₂ over the
    -- simplified ones.
    module W₁ = Group-Lemmas (n QRel,_===₁_) (grouplike₁ {n})
    module W₂ = Group-Lemmas (n QRel,_===₂_) (grouplike₂ {n})

    private
      module M₂₁ = GroupMorphisms (Group.rawGroup W₂.•-ε-group)
                                  (Group.rawGroup W₁.•-ε-group)
      module M₁₃ = GroupMorphisms (Group.rawGroup W₁.•-ε-group)
                                  (Group.rawGroup (Sp-group n))

    open GroupMorphisms (Group.rawGroup W₂.•-ε-group)
                        (Group.rawGroup (Sp-group n))

    -- The two halves, with their groups spelled out.  Left implicit,
    -- the middle group W₁ is never solved.
    iso₂₁ : M₂₁.IsGroupIsomorphism id
    iso₂₁ = Theorem-Sym-iso-Sim' {n}

    iso₁₃ : M₁₃.IsGroupIsomorphism P₁.⟦_⟧
    iso₁₃ = P₁.iso

    -- Transitivity of _≈ˢ_, phrased exactly as the composition wants it.
    -- Its three implicits are bound by hand: _≈ˢ_ is defined through the
    -- projection ap, so unification never recovers them.
    ≈ˢ-trans : Transitive (RawGroup._≈_ (Group.rawGroup (Sp-group n)))
    ≈ˢ-trans {S} {T} {U} eq₁ eq₂ =
      Setoid.trans (Group.setoid (Sp-group n)) {S} {T} {U} eq₁ eq₂

    -- Every implicit is given, and none of it is decoration:
    --   G₁-G₃  -- ≈ˢ-trans is checked before the morphism arguments
    --             could solve G₃;
    --   f, g   -- the type of `iso` fixes only the composite g ∘ f, and
    --             splitting that back apart is higher-order;
    --   the λ  -- passed bare, ≈ˢ-trans has its own three implicits
    --             inserted eagerly, and those are the ones ap hides.
    iso : IsGroupIsomorphism P₁.⟦_⟧
    iso = MC.isGroupIsomorphism {G₁ = Group.rawGroup W₂.•-ε-group}
                                {G₂ = Group.rawGroup W₁.•-ε-group}
                                {G₃ = Group.rawGroup (Sp-group n)}
                                (λ {S} {T} {U} → ≈ˢ-trans {S} {T} {U})
                                {f = id} {g = P₁.⟦_⟧} iso₂₁ iso₁₃

    pres : (n QRel,_===₂_) IsPresentationOf (Sp-group n)
    pres = record { gl = grouplike₂ ; ⟦_⟧ = P₁.⟦_⟧ ; iso = iso }

    subpres : (n QRel,_===₂_) IsSubPresentationOf (Sp-group n)
    subpres = record
      { gl   = grouplike₂
      ; ⟦_⟧  = P₁.⟦_⟧
      ; mono = IsGroupIsomorphism.isGroupMonomorphism iso
      }

_SRel,_===_ = _QRel,_===₂_

------------------------------------------------------------------------
-- The simplified presentation

-- Soundness and completeness: ⟦_⟧ is an injective homomorphism from the
-- words modulo the simplified rules into Sp(2n, ℤ/pℤ).
subpresentation : ∀ {n} → (n QRel,_===₂_) IsSubPresentationOf (Sp-group n)
subpresentation {n} = Build.subpres n

-- The simplified rules present the symplectic group.
presentation : ∀ {n} → (n SRel,_===_) IsPresentationOf (Sp-group n)
presentation {n} = Build.pres n
